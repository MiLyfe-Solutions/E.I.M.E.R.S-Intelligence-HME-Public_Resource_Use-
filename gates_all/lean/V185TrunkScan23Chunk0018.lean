import V185TrunkScan23Chunk0017

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_105946 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_105946 : Nat := 118140960795 + 105946 * 2 ^ 59
def prefixEnd_105946 : Nat := 4983230072969 + 3 ^ 40 * 105946 * 2
def baseEnd_105946 : Nat := 54401221421347719487769

theorem tailTrace_105946 : CollatzResearch.WordTrace tailWord_105946 prefixEnd_105946 54401221421347719487769 := by
  unfold tailWord_105946
  simp only [CollatzResearch.WordTrace]
  refine ⟨966042018545802745340423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2576112049455473987574461 966042018545802745340423)
  ·
    refine ⟨1449063027818704118010635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966042018545802745340423 1449063027818704118010635)
    ·
      refine ⟨2173594541728056177015953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1449063027818704118010635 2173594541728056177015953)
      ·
        refine ⟨1630195906296042132761965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2173594541728056177015953 1630195906296042132761965)
        ·
          refine ⟨611323464861015799785737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630195906296042132761965 611323464861015799785737)
          ·
            refine ⟨458492598645761849839303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611323464861015799785737 458492598645761849839303)
            ·
              refine ⟨687738897968642774758955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458492598645761849839303 687738897968642774758955)
              ·
                refine ⟨1031608346952964162138433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687738897968642774758955 1031608346952964162138433)
                ·
                  refine ⟨773706260214723121603825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031608346952964162138433 773706260214723121603825)
                  ·
                    refine ⟨580279695161042341202869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 773706260214723121603825 580279695161042341202869)
                    ·
                      refine ⟨54401221421347719487769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 580279695161042341202869 54401221421347719487769)
                      ·
                        rfl

theorem cell23_105946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_105946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105946 prefixEnd_105946 := by exact prefixLift 105946
  have htrace : WordTrace (prefixWord ++ tailWord_105946) baseStart_105946 baseEnd_105946 := by
    simpa [prefixWord, tailWord_105946, baseEnd_105946] using wordTrace_append hprefix tailTrace_105946
  have hstable : (prefixWord ++ tailWord_105946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105946).length < 2 ^ (prefixWord ++ tailWord_105946).sum := by decide
  have hdescent : baseEnd_105946 < baseStart_105946 := by decide
  rcases family_descends (prefixWord ++ tailWord_105946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105960 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_105960 : Nat := 118140960795 + 105960 * 2 ^ 59
def prefixEnd_105960 : Nat := 4983230072969 + 3 ^ 40 * 105960 * 2
def baseEnd_105960 : Nat := 54408410150510664712705

theorem tailTrace_105960 : CollatzResearch.WordTrace tailWord_105960 prefixEnd_105960 54408410150510664712705 := by
  unfold tailWord_105960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932339348066245686185667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2576452464088327581580889 1932339348066245686185667)
  ·
    refine ⟨2898509022099368529278501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932339348066245686185667 2898509022099368529278501)
    ·
      refine ⟨543470441643631599239719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2898509022099368529278501 543470441643631599239719)
      ·
        refine ⟨815205662465447398859579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543470441643631599239719 815205662465447398859579)
        ·
          refine ⟨1222808493698171098289369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815205662465447398859579 1222808493698171098289369)
          ·
            refine ⟨917106370273628323717027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222808493698171098289369 917106370273628323717027)
            ·
              refine ⟨1375659555410442485575541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917106370273628323717027 1375659555410442485575541)
              ·
                refine ⟨128968083319728983022707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1375659555410442485575541 128968083319728983022707)
                ·
                  refine ⟨193452124979593474534061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128968083319728983022707 193452124979593474534061)
                  ·
                    refine ⟨72544546867347552950273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193452124979593474534061 72544546867347552950273)
                    ·
                      refine ⟨54408410150510664712705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72544546867347552950273 54408410150510664712705)
                      ·
                        rfl

theorem cell23_105960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_105960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105960 prefixEnd_105960 := by exact prefixLift 105960
  have htrace : WordTrace (prefixWord ++ tailWord_105960) baseStart_105960 baseEnd_105960 := by
    simpa [prefixWord, tailWord_105960, baseEnd_105960] using wordTrace_append hprefix tailTrace_105960
  have hstable : (prefixWord ++ tailWord_105960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105960).length < 2 ^ (prefixWord ++ tailWord_105960).sum := by decide
  have hdescent : baseEnd_105960 < baseStart_105960 := by decide
  rcases family_descends (prefixWord ++ tailWord_105960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106060 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_106060 : Nat := 118140960795 + 106060 * 2 ^ 59
def prefixEnd_106060 : Nat := 4983230072969 + 3 ^ 40 * 106060 * 2
def baseEnd_106060 : Nat := 18153252738653424487415

theorem tailTrace_106060 : CollatzResearch.WordTrace tailWord_106060 prefixEnd_106060 18153252738653424487415 := by
  unfold tailWord_106060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934162997885104225505817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2578883997180138967341089 1934162997885104225505817)
  ·
    refine ⟨1450622248413828169129363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1934162997885104225505817 1450622248413828169129363)
    ·
      refine ⟨2175933372620742253694045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450622248413828169129363 2175933372620742253694045)
      ·
        refine ⟨815975014732778345135267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2175933372620742253694045 815975014732778345135267)
        ·
          refine ⟨1223962522099167517702901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815975014732778345135267 1223962522099167517702901)
          ·
            refine ⟨114746486446796954784647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1223962522099167517702901 114746486446796954784647)
            ·
              refine ⟨172119729670195432176971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114746486446796954784647 172119729670195432176971)
              ·
                refine ⟨258179594505293148265457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172119729670195432176971 258179594505293148265457)
                ·
                  refine ⟨193634695878969861199093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258179594505293148265457 193634695878969861199093)
                  ·
                    refine ⟨18153252738653424487415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193634695878969861199093 18153252738653424487415)
                    ·
                      rfl

theorem cell23_106060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_106060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106060 prefixEnd_106060 := by exact prefixLift 106060
  have htrace : WordTrace (prefixWord ++ tailWord_106060) baseStart_106060 baseEnd_106060 := by
    simpa [prefixWord, tailWord_106060, baseEnd_106060] using wordTrace_append hprefix tailTrace_106060
  have hstable : (prefixWord ++ tailWord_106060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106060).length < 2 ^ (prefixWord ++ tailWord_106060).sum := by decide
  have hdescent : baseEnd_106060 < baseStart_106060 := by decide
  rcases family_descends (prefixWord ++ tailWord_106060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106063 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 6, 2]
def baseStart_106063 : Nat := 118140960795 + 106063 * 2 ^ 59
def prefixEnd_106063 : Nat := 4983230072969 + 3 ^ 40 * 106063 * 2
def baseEnd_106063 : Nat := 54461298657923761724731

theorem tailTrace_106063 : CollatzResearch.WordTrace tailWord_106063 prefixEnd_106063 54461298657923761724731 := by
  unfold tailWord_106063
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868435414759339963370843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2578956943172893308913895 3868435414759339963370843)
  ·
    refine ⟨5802653122139009945056265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3868435414759339963370843 5802653122139009945056265)
    ·
      refine ⟨4351989841604257458792199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5802653122139009945056265 4351989841604257458792199)
      ·
        refine ⟨6527984762406386188188299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351989841604257458792199 6527984762406386188188299)
        ·
          refine ⟨9791977143609579282282449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527984762406386188188299 9791977143609579282282449)
          ·
            refine ⟨7343982857707184461711837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791977143609579282282449 7343982857707184461711837)
            ·
              refine ⟨2753993571640194173141939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7343982857707184461711837 2753993571640194173141939)
              ·
                refine ⟨4130990357460291259712909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753993571640194173141939 4130990357460291259712909)
                ·
                  refine ⟨1549121384047609222392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4130990357460291259712909 1549121384047609222392341)
                  ·
                    refine ⟨72615064877231682299641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1549121384047609222392341 72615064877231682299641)
                    ·
                      refine ⟨54461298657923761724731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72615064877231682299641 54461298657923761724731)
                      ·
                        rfl

theorem cell23_106063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6, 2].length) (baseStart_106063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106063 prefixEnd_106063 := by exact prefixLift 106063
  have htrace : WordTrace (prefixWord ++ tailWord_106063) baseStart_106063 baseEnd_106063 := by
    simpa [prefixWord, tailWord_106063, baseEnd_106063] using wordTrace_append hprefix tailTrace_106063
  have hstable : (prefixWord ++ tailWord_106063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106063).length < 2 ^ (prefixWord ++ tailWord_106063).sum := by decide
  have hdescent : baseEnd_106063 < baseStart_106063 := by decide
  rcases family_descends (prefixWord ++ tailWord_106063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106090 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_106090 : Nat := 118140960795 + 106090 * 2 ^ 59
def prefixEnd_106090 : Nat := 4983230072969 + 3 ^ 40 * 106090 * 2
def baseEnd_106090 : Nat := 18158387545198385362369

theorem tailTrace_106090 : CollatzResearch.WordTrace tailWord_106090 prefixEnd_106090 18158387545198385362369 := by
  unfold tailWord_106090
  simp only [CollatzResearch.WordTrace]
  refine ⟨967355046415380893650931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2579613457107682383069149 967355046415380893650931)
  ·
    refine ⟨1451032569623071340476397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967355046415380893650931 1451032569623071340476397)
    ·
      refine ⟨544137213608651752678649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1451032569623071340476397 544137213608651752678649)
      ·
        refine ⟨408102910206488814508987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544137213608651752678649 408102910206488814508987)
        ·
          refine ⟨612154365309733221763481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408102910206488814508987 612154365309733221763481)
          ·
            refine ⟨459115773982299916322611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612154365309733221763481 459115773982299916322611)
            ·
              refine ⟨688673660973449874483917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459115773982299916322611 688673660973449874483917)
              ·
                refine ⟨258252622865043702931469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688673660973449874483917 258252622865043702931469)
                ·
                  refine ⟨96844733574391388599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258252622865043702931469 96844733574391388599301)
                  ·
                    refine ⟨18158387545198385362369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96844733574391388599301 18158387545198385362369)
                    ·
                      rfl

theorem cell23_106090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_106090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106090 prefixEnd_106090 := by exact prefixLift 106090
  have htrace : WordTrace (prefixWord ++ tailWord_106090) baseStart_106090 baseEnd_106090 := by
    simpa [prefixWord, tailWord_106090, baseEnd_106090] using wordTrace_append hprefix tailTrace_106090
  have hstable : (prefixWord ++ tailWord_106090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106090).length < 2 ^ (prefixWord ++ tailWord_106090).sum := by decide
  have hdescent : baseEnd_106090 < baseStart_106090 := by decide
  rcases family_descends (prefixWord ++ tailWord_106090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106157 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_106157 : Nat := 118140960795 + 106157 * 2 ^ 59
def prefixEnd_106157 : Nat := 4983230072969 + 3 ^ 40 * 106157 * 2
def baseEnd_106157 : Nat := 54509565839446393949299

theorem tailTrace_106157 : CollatzResearch.WordTrace tailWord_106157 prefixEnd_106157 54509565839446393949299 := by
  unfold tailWord_106157
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871863876418794017292725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2581242584279196011528483 3871863876418794017292725)
  ·
    refine ⟨362987238414261939121193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3871863876418794017292725 362987238414261939121193)
    ·
      refine ⟨272240428810696454340895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362987238414261939121193 272240428810696454340895)
      ·
        refine ⟨408360643216044681511343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272240428810696454340895 408360643216044681511343)
        ·
          refine ⟨612540964824067022267015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408360643216044681511343 612540964824067022267015)
          ·
            refine ⟨918811447236100533400523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612540964824067022267015 918811447236100533400523)
            ·
              refine ⟨1378217170854150800100785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918811447236100533400523 1378217170854150800100785)
              ·
                refine ⟨1033662878140613100075589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378217170854150800100785 1033662878140613100075589)
                ·
                  refine ⟨193811789651364956264173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033662878140613100075589 193811789651364956264173)
                  ·
                    refine ⟨72679421119261858599065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193811789651364956264173 72679421119261858599065)
                    ·
                      refine ⟨54509565839446393949299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72679421119261858599065 54509565839446393949299)
                      ·
                        rfl

theorem cell23_106157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_106157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106157 prefixEnd_106157 := by exact prefixLift 106157
  have htrace : WordTrace (prefixWord ++ tailWord_106157) baseStart_106157 baseEnd_106157 := by
    simpa [prefixWord, tailWord_106157, baseEnd_106157] using wordTrace_append hprefix tailTrace_106157
  have hstable : (prefixWord ++ tailWord_106157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106157).length < 2 ^ (prefixWord ++ tailWord_106157).sum := by decide
  have hdescent : baseEnd_106157 < baseStart_106157 := by decide
  rcases family_descends (prefixWord ++ tailWord_106157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106163 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 1, 6]
def baseStart_106163 : Nat := 118140960795 + 106163 * 2 ^ 59
def prefixEnd_106163 : Nat := 4983230072969 + 3 ^ 40 * 106163 * 2
def baseEnd_106163 : Nat := 18170882241124456824757

theorem tailTrace_106163 : CollatzResearch.WordTrace tailWord_106163 prefixEnd_106163 18170882241124456824757 := by
  unfold tailWord_106163
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872082714397057042011143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2581388476264704694674095 3872082714397057042011143)
  ·
    refine ⟨5808124071595585563016715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872082714397057042011143 5808124071595585563016715)
    ·
      refine ⟨8712186107393378344525073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5808124071595585563016715 8712186107393378344525073)
      ·
        refine ⟨6534139580545033758393805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8712186107393378344525073 6534139580545033758393805)
        ·
          refine ⟨2450302342704387659397677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6534139580545033758393805 2450302342704387659397677)
          ·
            refine ⟨918863378514145372274129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2450302342704387659397677 918863378514145372274129)
            ·
              refine ⟨689147533885609029205597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918863378514145372274129 689147533885609029205597)
              ·
                refine ⟨258430325207103385952099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689147533885609029205597 258430325207103385952099)
                ·
                  refine ⟨387645487810655078928149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258430325207103385952099 387645487810655078928149)
                  ·
                    refine ⟨18170882241124456824757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 387645487810655078928149 18170882241124456824757)
                    ·
                      rfl

theorem cell23_106163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 6].length) (baseStart_106163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106163 prefixEnd_106163 := by exact prefixLift 106163
  have htrace : WordTrace (prefixWord ++ tailWord_106163) baseStart_106163 baseEnd_106163 := by
    simpa [prefixWord, tailWord_106163, baseEnd_106163] using wordTrace_append hprefix tailTrace_106163
  have hstable : (prefixWord ++ tailWord_106163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106163).length < 2 ^ (prefixWord ++ tailWord_106163).sum := by decide
  have hdescent : baseEnd_106163 < baseStart_106163 := by decide
  rcases family_descends (prefixWord ++ tailWord_106163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106167 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 1, 5]
def baseStart_106167 : Nat := 118140960795 + 106167 * 2 ^ 59
def prefixEnd_106167 : Nat := 4983230072969 + 3 ^ 40 * 106167 * 2
def baseEnd_106167 : Nat := 18171566881997118274751

theorem tailTrace_106167 : CollatzResearch.WordTrace tailWord_106167 prefixEnd_106167 18171566881997118274751 := by
  unfold tailWord_106167
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872228606382565725156755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2581485737588377150104503 3872228606382565725156755)
  ·
    refine ⟨5808342909573848587735133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872228606382565725156755 5808342909573848587735133)
    ·
      refine ⟨2178128591090193220400675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5808342909573848587735133 2178128591090193220400675)
      ·
        refine ⟨3267192886635289830601013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178128591090193220400675 3267192886635289830601013)
        ·
          refine ⟨306299333122058421618845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3267192886635289830601013 306299333122058421618845)
          ·
            refine ⟨114862249920771908107067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306299333122058421618845 114862249920771908107067)
            ·
              refine ⟨172293374881157862160601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114862249920771908107067 172293374881157862160601)
              ·
                refine ⟨129220031160868396620451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172293374881157862160601 129220031160868396620451)
                ·
                  refine ⟨193830046741302594930677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129220031160868396620451 193830046741302594930677)
                  ·
                    refine ⟨18171566881997118274751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193830046741302594930677 18171566881997118274751)
                    ·
                      rfl

theorem cell23_106167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_106167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106167 prefixEnd_106167 := by exact prefixLift 106167
  have htrace : WordTrace (prefixWord ++ tailWord_106167) baseStart_106167 baseEnd_106167 := by
    simpa [prefixWord, tailWord_106167, baseEnd_106167] using wordTrace_append hprefix tailTrace_106167
  have hstable : (prefixWord ++ tailWord_106167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106167).length < 2 ^ (prefixWord ++ tailWord_106167).sum := by decide
  have hdescent : baseEnd_106167 < baseStart_106167 := by decide
  rcases family_descends (prefixWord ++ tailWord_106167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106170 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_106170 : Nat := 118140960795 + 106170 * 2 ^ 59
def prefixEnd_106170 : Nat := 4983230072969 + 3 ^ 40 * 106170 * 2
def baseEnd_106170 : Nat := 54516241087954843086739

theorem tailTrace_106170 : CollatzResearch.WordTrace tailWord_106170 prefixEnd_106170 54516241087954843086739 := by
  unfold tailWord_106170
  simp only [CollatzResearch.WordTrace]
  refine ⟨968084506342924309378991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2581558683581131491677309 968084506342924309378991)
  ·
    refine ⟨1452126759514386464068487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 968084506342924309378991 1452126759514386464068487)
    ·
      refine ⟨2178190139271579696102731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452126759514386464068487 2178190139271579696102731)
      ·
        refine ⟨3267285208907369544154097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178190139271579696102731 3267285208907369544154097)
        ·
          refine ⟨2450463906680527158115573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267285208907369544154097 2450463906680527158115573)
          ·
            refine ⟨229730991251299421073335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2450463906680527158115573 229730991251299421073335)
            ·
              refine ⟨344596486876949131610003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229730991251299421073335 344596486876949131610003)
              ·
                refine ⟨516894730315423697415005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344596486876949131610003 516894730315423697415005)
                ·
                  refine ⟨193835523868283886530627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516894730315423697415005 193835523868283886530627)
                  ·
                    refine ⟨290753285802425829795941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193835523868283886530627 290753285802425829795941)
                    ·
                      refine ⟨54516241087954843086739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 290753285802425829795941 54516241087954843086739)
                      ·
                        rfl

theorem cell23_106170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_106170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106170 prefixEnd_106170 := by exact prefixLift 106170
  have htrace : WordTrace (prefixWord ++ tailWord_106170) baseStart_106170 baseEnd_106170 := by
    simpa [prefixWord, tailWord_106170, baseEnd_106170] using wordTrace_append hprefix tailTrace_106170
  have hstable : (prefixWord ++ tailWord_106170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106170).length < 2 ^ (prefixWord ++ tailWord_106170).sum := by decide
  have hdescent : baseEnd_106170 < baseStart_106170 := by decide
  rcases family_descends (prefixWord ++ tailWord_106170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106174 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_106174 : Nat := 118140960795 + 106174 * 2 ^ 59
def prefixEnd_106174 : Nat := 4983230072969 + 3 ^ 40 * 106174 * 2
def baseEnd_106174 : Nat := 54518295010572827436721

theorem tailTrace_106174 : CollatzResearch.WordTrace tailWord_106174 prefixEnd_106174 54518295010572827436721 := by
  unfold tailWord_106174
  simp only [CollatzResearch.WordTrace]
  refine ⟨484060489669650740082697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2581655944904803947107717 484060489669650740082697)
  ·
    refine ⟨363045367252238055062023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484060489669650740082697 363045367252238055062023)
    ·
      refine ⟨544568050878357082593035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363045367252238055062023 544568050878357082593035)
      ·
        refine ⟨816852076317535623889553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544568050878357082593035 816852076317535623889553)
        ·
          refine ⟨612639057238151717917165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816852076317535623889553 612639057238151717917165)
          ·
            refine ⟨229739646464306894218937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612639057238151717917165 229739646464306894218937)
            ·
              refine ⟨172304734848230170664203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229739646464306894218937 172304734848230170664203)
              ·
                refine ⟨258457102272345255996305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172304734848230170664203 258457102272345255996305)
                ·
                  refine ⟨193842826704258941997229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258457102272345255996305 193842826704258941997229)
                  ·
                    refine ⟨72691060014097103248961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193842826704258941997229 72691060014097103248961)
                    ·
                      refine ⟨54518295010572827436721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72691060014097103248961 54518295010572827436721)
                      ·
                        rfl

theorem cell23_106174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_106174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106174 prefixEnd_106174 := by exact prefixLift 106174
  have htrace : WordTrace (prefixWord ++ tailWord_106174) baseStart_106174 baseEnd_106174 := by
    simpa [prefixWord, tailWord_106174, baseEnd_106174] using wordTrace_append hprefix tailTrace_106174
  have hstable : (prefixWord ++ tailWord_106174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106174).length < 2 ^ (prefixWord ++ tailWord_106174).sum := by decide
  have hdescent : baseEnd_106174 < baseStart_106174 := by decide
  rcases family_descends (prefixWord ++ tailWord_106174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106180 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_106180 : Nat := 118140960795 + 106180 * 2 ^ 59
def prefixEnd_106180 : Nat := 4983230072969 + 3 ^ 40 * 106180 * 2
def baseEnd_106180 : Nat := 18173791964833267987231

theorem tailTrace_106180 : CollatzResearch.WordTrace tailWord_106180 prefixEnd_106180 18173791964833267987231 := by
  unfold tailWord_106180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936351377667734472689997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2581801836890312630253329 1936351377667734472689997)
  ·
    refine ⟨726131766625400427258749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1936351377667734472689997 726131766625400427258749)
    ·
      refine ⟨272299412484525160222031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 726131766625400427258749 272299412484525160222031)
      ·
        refine ⟨408449118726787740333047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272299412484525160222031 408449118726787740333047)
        ·
          refine ⟨612673678090181610499571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408449118726787740333047 612673678090181610499571)
          ·
            refine ⟨919010517135272415749357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612673678090181610499571 919010517135272415749357)
            ·
              refine ⟨344628943925727155906009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919010517135272415749357 344628943925727155906009)
              ·
                refine ⟨258471707944295366929507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344628943925727155906009 258471707944295366929507)
                ·
                  refine ⟨387707561916443050394261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258471707944295366929507 387707561916443050394261)
                  ·
                    refine ⟨18173791964833267987231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 387707561916443050394261 18173791964833267987231)
                    ·
                      rfl

theorem cell23_106180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_106180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106180 prefixEnd_106180 := by exact prefixLift 106180
  have htrace : WordTrace (prefixWord ++ tailWord_106180) baseStart_106180 baseEnd_106180 := by
    simpa [prefixWord, tailWord_106180, baseEnd_106180] using wordTrace_append hprefix tailTrace_106180
  have hstable : (prefixWord ++ tailWord_106180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106180).length < 2 ^ (prefixWord ++ tailWord_106180).sum := by decide
  have hdescent : baseEnd_106180 < baseStart_106180 := by decide
  rcases family_descends (prefixWord ++ tailWord_106180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106203 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3]
def baseStart_106203 : Nat := 118140960795 + 106203 * 2 ^ 59
def prefixEnd_106203 : Nat := 4983230072969 + 3 ^ 40 * 106203 * 2
def baseEnd_106203 : Nat := 54533185949553213974087

theorem tailTrace_106203 : CollatzResearch.WordTrace tailWord_106203 prefixEnd_106203 54533185949553213974087 := by
  unfold tailWord_106203
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873541634252143873467263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2582361089501429248978175 3873541634252143873467263)
  ·
    refine ⟨5810312451378215810200895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3873541634252143873467263 5810312451378215810200895)
    ·
      refine ⟨8715468677067323715301343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810312451378215810200895 8715468677067323715301343)
      ·
        refine ⟨13073203015600985572952015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715468677067323715301343 13073203015600985572952015)
        ·
          refine ⟨19609804523401478359428023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13073203015600985572952015 19609804523401478359428023)
          ·
            refine ⟨29414706785102217539142035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19609804523401478359428023 29414706785102217539142035)
            ·
              refine ⟨44122060177653326308713053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29414706785102217539142035 44122060177653326308713053)
              ·
                refine ⟨16545772566619997365767395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44122060177653326308713053 16545772566619997365767395)
                ·
                  refine ⟨24818658849929996048651093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545772566619997365767395 24818658849929996048651093)
                  ·
                    refine ⟨145421829198808570597565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24818658849929996048651093 145421829198808570597565)
                    ·
                      refine ⟨54533185949553213974087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 145421829198808570597565 54533185949553213974087)
                      ·
                        rfl

theorem cell23_106203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3].length) (baseStart_106203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106203 prefixEnd_106203 := by exact prefixLift 106203
  have htrace : WordTrace (prefixWord ++ tailWord_106203) baseStart_106203 baseEnd_106203 := by
    simpa [prefixWord, tailWord_106203, baseEnd_106203] using wordTrace_append hprefix tailTrace_106203
  have hstable : (prefixWord ++ tailWord_106203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106203).length < 2 ^ (prefixWord ++ tailWord_106203).sum := by decide
  have hdescent : baseEnd_106203 < baseStart_106203 := by decide
  rcases family_descends (prefixWord ++ tailWord_106203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106220 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_106220 : Nat := 118140960795 + 106220 * 2 ^ 59
def prefixEnd_106220 : Nat := 4983230072969 + 3 ^ 40 * 106220 * 2
def baseEnd_106220 : Nat := 54541915120679647461509

theorem tailTrace_106220 : CollatzResearch.WordTrace tailWord_106220 prefixEnd_106220 54541915120679647461509 := by
  unfold tailWord_106220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1937080837595277888418057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2582774450127037184557409 1937080837595277888418057)
  ·
    refine ⟨1452810628196458416313543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1937080837595277888418057 1452810628196458416313543)
    ·
      refine ⟨2179215942294687624470315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452810628196458416313543 2179215942294687624470315)
      ·
        refine ⟨3268823913442031436705473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179215942294687624470315 3268823913442031436705473)
        ·
          refine ⟨2451617935081523577529105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268823913442031436705473 2451617935081523577529105)
          ·
            refine ⟨1838713451311142683146829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451617935081523577529105 1838713451311142683146829)
            ·
              refine ⟨689517544241678506180061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838713451311142683146829 689517544241678506180061)
              ·
                refine ⟨258569079090629439817523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689517544241678506180061 258569079090629439817523)
                ·
                  refine ⟨387853618635944159726285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258569079090629439817523 387853618635944159726285)
                  ·
                    refine ⟨145445106988479059897357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387853618635944159726285 145445106988479059897357)
                    ·
                      refine ⟨54541915120679647461509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 145445106988479059897357 54541915120679647461509)
                      ·
                        rfl

theorem cell23_106220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_106220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106220 prefixEnd_106220 := by exact prefixLift 106220
  have htrace : WordTrace (prefixWord ++ tailWord_106220) baseStart_106220 baseEnd_106220 := by
    simpa [prefixWord, tailWord_106220, baseEnd_106220] using wordTrace_append hprefix tailTrace_106220
  have hstable : (prefixWord ++ tailWord_106220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106220).length < 2 ^ (prefixWord ++ tailWord_106220).sum := by decide
  have hdescent : baseEnd_106220 < baseStart_106220 := by decide
  rcases family_descends (prefixWord ++ tailWord_106220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106223 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 7]
def baseStart_106223 : Nat := 118140960795 + 106223 * 2 ^ 59
def prefixEnd_106223 : Nat := 4983230072969 + 3 ^ 40 * 106223 * 2
def baseEnd_106223 : Nat := 18181151854214378574665

theorem tailTrace_106223 : CollatzResearch.WordTrace tailWord_106223 prefixEnd_106223 18181151854214378574665 := by
  unfold tailWord_106223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874271094179687289195323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2582847396119791526130215 3874271094179687289195323)
  ·
    refine ⟨5811406641269530933792985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874271094179687289195323 5811406641269530933792985)
    ·
      refine ⟨4358554980952148200344739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5811406641269530933792985 4358554980952148200344739)
      ·
        refine ⟨6537832471428222300517109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358554980952148200344739 6537832471428222300517109)
        ·
          refine ⟨612921794196395840673479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6537832471428222300517109 612921794196395840673479)
          ·
            refine ⟨919382691294593761010219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612921794196395840673479 919382691294593761010219)
            ·
              refine ⟨1379074036941890641515329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919382691294593761010219 1379074036941890641515329)
              ·
                refine ⟨1034305527706417981136497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379074036941890641515329 1034305527706417981136497)
                ·
                  refine ⟨775729145779813485852373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1034305527706417981136497 775729145779813485852373)
                  ·
                    refine ⟨18181151854214378574665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 775729145779813485852373 18181151854214378574665)
                    ·
                      rfl

theorem cell23_106223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_106223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106223 prefixEnd_106223 := by exact prefixLift 106223
  have htrace : WordTrace (prefixWord ++ tailWord_106223) baseStart_106223 baseEnd_106223 := by
    simpa [prefixWord, tailWord_106223, baseEnd_106223] using wordTrace_append hprefix tailTrace_106223
  have hstable : (prefixWord ++ tailWord_106223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106223).length < 2 ^ (prefixWord ++ tailWord_106223).sum := by decide
  have hdescent : baseEnd_106223 < baseStart_106223 := by decide
  rcases family_descends (prefixWord ++ tailWord_106223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106238 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_106238 : Nat := 118140960795 + 106238 * 2 ^ 59
def prefixEnd_106238 : Nat := 4983230072969 + 3 ^ 40 * 106238 * 2
def baseEnd_106238 : Nat := 54551157772460577036427

theorem tailTrace_106238 : CollatzResearch.WordTrace tailWord_106238 prefixEnd_106238 54551157772460577036427 := by
  unfold tailWord_106238
  simp only [CollatzResearch.WordTrace]
  refine ⟨484352273640668106373921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2583212126083563233994245 484352273640668106373921)
  ·
    refine ⟨363264205230501079780441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484352273640668106373921 363264205230501079780441)
    ·
      refine ⟨272448153922875809835331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363264205230501079780441 272448153922875809835331)
      ·
        refine ⟨408672230884313714752997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272448153922875809835331 408672230884313714752997)
        ·
          refine ⟨76626043290808821516187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408672230884313714752997 76626043290808821516187)
          ·
            refine ⟨114939064936213232274281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76626043290808821516187 114939064936213232274281)
            ·
              refine ⟨86204298702159924205711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114939064936213232274281 86204298702159924205711)
              ·
                refine ⟨129306448053239886308567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86204298702159924205711 129306448053239886308567)
                ·
                  refine ⟨193959672079859829462851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129306448053239886308567 193959672079859829462851)
                  ·
                    refine ⟨290939508119789744194277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193959672079859829462851 290939508119789744194277)
                    ·
                      refine ⟨54551157772460577036427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 290939508119789744194277 54551157772460577036427)
                      ·
                        rfl

theorem cell23_106238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_106238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106238 prefixEnd_106238 := by exact prefixLift 106238
  have htrace : WordTrace (prefixWord ++ tailWord_106238) baseStart_106238 baseEnd_106238 := by
    simpa [prefixWord, tailWord_106238, baseEnd_106238] using wordTrace_append hprefix tailTrace_106238
  have hstable : (prefixWord ++ tailWord_106238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106238).length < 2 ^ (prefixWord ++ tailWord_106238).sum := by decide
  have hdescent : baseEnd_106238 < baseStart_106238 := by decide
  rcases family_descends (prefixWord ++ tailWord_106238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106254 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_106254 : Nat := 118140960795 + 106254 * 2 ^ 59
def prefixEnd_106254 : Nat := 4983230072969 + 3 ^ 40 * 106254 * 2
def baseEnd_106254 : Nat := 54559373462932514436353

theorem tailTrace_106254 : CollatzResearch.WordTrace tailWord_106254 prefixEnd_106254 54559373462932514436353 := by
  unfold tailWord_106254
  simp only [CollatzResearch.WordTrace]
  refine ⟨484425219633422447946727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2583601171378253055715877 484425219633422447946727)
  ·
    refine ⟨726637829450133671920091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484425219633422447946727 726637829450133671920091)
    ·
      refine ⟨1089956744175200507880137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726637829450133671920091 1089956744175200507880137)
      ·
        refine ⟨817467558131400380910103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089956744175200507880137 817467558131400380910103)
        ·
          refine ⟨1226201337197100571365155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817467558131400380910103 1226201337197100571365155)
          ·
            refine ⟨1839302005795650857047733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226201337197100571365155 1839302005795650857047733)
            ·
              refine ⟨172434563043342267848225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1839302005795650857047733 172434563043342267848225)
              ·
                refine ⟨129325922282506700886169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172434563043342267848225 129325922282506700886169)
                ·
                  refine ⟨96994441711880025664627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129325922282506700886169 96994441711880025664627)
                  ·
                    refine ⟨145491662567820038496941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96994441711880025664627 145491662567820038496941)
                    ·
                      refine ⟨54559373462932514436353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 145491662567820038496941 54559373462932514436353)
                      ·
                        rfl

theorem cell23_106254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_106254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106254 prefixEnd_106254 := by exact prefixLift 106254
  have htrace : WordTrace (prefixWord ++ tailWord_106254) baseStart_106254 baseEnd_106254 := by
    simpa [prefixWord, tailWord_106254, baseEnd_106254] using wordTrace_append hprefix tailTrace_106254
  have hstable : (prefixWord ++ tailWord_106254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106254).length < 2 ^ (prefixWord ++ tailWord_106254).sum := by decide
  have hdescent : baseEnd_106254 < baseStart_106254 := by decide
  rcases family_descends (prefixWord ++ tailWord_106254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106330 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_106330 : Nat := 118140960795 + 106330 * 2 ^ 59
def prefixEnd_106330 : Nat := 4983230072969 + 3 ^ 40 * 106330 * 2
def baseEnd_106330 : Nat := 18199465997558072362001

theorem tailTrace_106330 : CollatzResearch.WordTrace tailWord_106330 prefixEnd_106330 18199465997558072362001 := by
  unfold tailWord_106330
  simp only [CollatzResearch.WordTrace]
  refine ⟨969543426198011140835111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2585449136528029708893629 969543426198011140835111)
  ·
    refine ⟨1454315139297016711252667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969543426198011140835111 1454315139297016711252667)
    ·
      refine ⟨2181472708945525066879001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454315139297016711252667 2181472708945525066879001)
      ·
        refine ⟨1636104531709143800159251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2181472708945525066879001 1636104531709143800159251)
        ·
          refine ⟨2454156797563715700238877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636104531709143800159251 2454156797563715700238877)
          ·
            refine ⟨920308799086393387589579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454156797563715700238877 920308799086393387589579)
            ·
              refine ⟨1380463198629590081384369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920308799086393387589579 1380463198629590081384369)
              ·
                refine ⟨1035347398972192561038277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380463198629590081384369 1035347398972192561038277)
                ·
                  refine ⟨194127637307286105194677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035347398972192561038277 194127637307286105194677)
                  ·
                    refine ⟨18199465997558072362001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194127637307286105194677 18199465997558072362001)
                    ·
                      rfl

theorem cell23_106330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_106330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106330 prefixEnd_106330 := by exact prefixLift 106330
  have htrace : WordTrace (prefixWord ++ tailWord_106330) baseStart_106330 baseEnd_106330 := by
    simpa [prefixWord, tailWord_106330, baseEnd_106330] using wordTrace_append hprefix tailTrace_106330
  have hstable : (prefixWord ++ tailWord_106330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106330).length < 2 ^ (prefixWord ++ tailWord_106330).sum := by decide
  have hdescent : baseEnd_106330 < baseStart_106330 := by decide
  rcases family_descends (prefixWord ++ tailWord_106330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106367 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 2, 4, 2]
def baseStart_106367 : Nat := 118140960795 + 106367 * 2 ^ 59
def prefixEnd_106367 : Nat := 4983230072969 + 3 ^ 40 * 106367 * 2
def baseEnd_106367 : Nat := 54617396776890572323333

theorem tailTrace_106367 : CollatzResearch.WordTrace tailWord_106367 prefixEnd_106367 54617396776890572323333 := by
  unfold tailWord_106367
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879523205657999882437355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2586348803771999921624903 3879523205657999882437355)
  ·
    refine ⟨5819284808486999823656033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3879523205657999882437355 5819284808486999823656033)
    ·
      refine ⟨4364463606365249867742025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5819284808486999823656033 4364463606365249867742025)
      ·
        refine ⟨3273347704773937400806519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4364463606365249867742025 3273347704773937400806519)
        ·
          refine ⟨4910021557160906101209779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273347704773937400806519 4910021557160906101209779)
          ·
            refine ⟨7365032335741359151814669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910021557160906101209779 7365032335741359151814669)
            ·
              refine ⟨2761887125903009681930501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7365032335741359151814669 2761887125903009681930501)
              ·
                refine ⟨517853836106814315361969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2761887125903009681930501 517853836106814315361969)
                ·
                  refine ⟨388390377080110736521477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517853836106814315361969 388390377080110736521477)
                  ·
                    refine ⟨72823195702520763097777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388390377080110736521477 72823195702520763097777)
                    ·
                      refine ⟨54617396776890572323333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72823195702520763097777 54617396776890572323333)
                      ·
                        rfl

theorem cell23_106367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_106367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106367 prefixEnd_106367 := by exact prefixLift 106367
  have htrace : WordTrace (prefixWord ++ tailWord_106367) baseStart_106367 baseEnd_106367 := by
    simpa [prefixWord, tailWord_106367, baseEnd_106367] using wordTrace_append hprefix tailTrace_106367
  have hstable : (prefixWord ++ tailWord_106367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106367).length < 2 ^ (prefixWord ++ tailWord_106367).sum := by decide
  have hdescent : baseEnd_106367 < baseStart_106367 := by decide
  rcases family_descends (prefixWord ++ tailWord_106367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106377 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_106377 : Nat := 118140960795 + 106377 * 2 ^ 59
def prefixEnd_106377 : Nat := 4983230072969 + 3 ^ 40 * 106377 * 2
def baseEnd_106377 : Nat := 18207510527811844399429

theorem tailTrace_106377 : CollatzResearch.WordTrace tailWord_106377 prefixEnd_106377 18207510527811844399429 := by
  unfold tailWord_106377
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879887935621771590301385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2586591957081181060200923 3879887935621771590301385)
  ·
    refine ⟨2909915951716328692726039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3879887935621771590301385 2909915951716328692726039)
    ·
      refine ⟨4364873927574493039089059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909915951716328692726039 4364873927574493039089059)
      ·
        refine ⟨6547310891361739558633589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364873927574493039089059 6547310891361739558633589)
        ·
          refine ⟨613810396065163083621899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6547310891361739558633589 613810396065163083621899)
          ·
            refine ⟨920715594097744625432849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613810396065163083621899 920715594097744625432849)
            ·
              refine ⟨690536695573308469074637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920715594097744625432849 690536695573308469074637)
              ·
                refine ⟨258951260839990675902989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 690536695573308469074637 258951260839990675902989)
                ·
                  refine ⟨97106722814996503463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258951260839990675902989 97106722814996503463621)
                  ·
                    refine ⟨18207510527811844399429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97106722814996503463621 18207510527811844399429)
                    ·
                      rfl

theorem cell23_106377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_106377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106377 prefixEnd_106377 := by exact prefixLift 106377
  have htrace : WordTrace (prefixWord ++ tailWord_106377) baseStart_106377 baseEnd_106377 := by
    simpa [prefixWord, tailWord_106377, baseEnd_106377] using wordTrace_append hprefix tailTrace_106377
  have hstable : (prefixWord ++ tailWord_106377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106377).length < 2 ^ (prefixWord ++ tailWord_106377).sum := by decide
  have hdescent : baseEnd_106377 < baseStart_106377 := by decide
  rcases family_descends (prefixWord ++ tailWord_106377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106380 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_106380 : Nat := 118140960795 + 106380 * 2 ^ 59
def prefixEnd_106380 : Nat := 4983230072969 + 3 ^ 40 * 106380 * 2
def baseEnd_106380 : Nat := 54624072025399021460773

theorem tailTrace_106380 : CollatzResearch.WordTrace tailWord_106380 prefixEnd_106380 54624072025399021460773 := by
  unfold tailWord_106380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939998677305451551330297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2586664903073935401773729 1939998677305451551330297)
  ·
    refine ⟨1454999007979088663497723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1939998677305451551330297 1454999007979088663497723)
    ·
      refine ⟨2182498511968632995246585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454999007979088663497723 2182498511968632995246585)
      ·
        refine ⟨1636873883976474746434939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182498511968632995246585 1636873883976474746434939)
        ·
          refine ⟨2455310825964712119652409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636873883976474746434939 2455310825964712119652409)
          ·
            refine ⟨1841483119473534089739307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455310825964712119652409 1841483119473534089739307)
            ·
              refine ⟨2762224679210301134608961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841483119473534089739307 2762224679210301134608961)
              ·
                refine ⟨2071668509407725850956721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762224679210301134608961 2071668509407725850956721)
                ·
                  refine ⟨1553751382055794388217541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071668509407725850956721 1553751382055794388217541)
                  ·
                    refine ⟨291328384135461447790789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1553751382055794388217541 291328384135461447790789)
                    ·
                      refine ⟨54624072025399021460773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 291328384135461447790789 54624072025399021460773)
                      ·
                        rfl

theorem cell23_106380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_106380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106380 prefixEnd_106380 := by exact prefixLift 106380
  have htrace : WordTrace (prefixWord ++ tailWord_106380) baseStart_106380 baseEnd_106380 := by
    simpa [prefixWord, tailWord_106380, baseEnd_106380] using wordTrace_append hprefix tailTrace_106380
  have hstable : (prefixWord ++ tailWord_106380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106380).length < 2 ^ (prefixWord ++ tailWord_106380).sum := by decide
  have hdescent : baseEnd_106380 < baseStart_106380 := by decide
  rcases family_descends (prefixWord ++ tailWord_106380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106394 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_106394 : Nat := 118140960795 + 106394 * 2 ^ 59
def prefixEnd_106394 : Nat := 4983230072969 + 3 ^ 40 * 106394 * 2
def baseEnd_106394 : Nat := 18210420251520655561903

theorem tailTrace_106394 : CollatzResearch.WordTrace tailWord_106394 prefixEnd_106394 18210420251520655561903 := by
  unfold tailWord_106394
  simp only [CollatzResearch.WordTrace]
  refine ⟨970126994140045873417559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2587005317706788995780157 970126994140045873417559)
  ·
    refine ⟨1455190491210068810126339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970126994140045873417559 1455190491210068810126339)
    ·
      refine ⟨2182785736815103215189509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455190491210068810126339 2182785736815103215189509)
      ·
        refine ⟨409272325652831852848033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2182785736815103215189509 409272325652831852848033)
        ·
          refine ⟨306954244239623889636025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409272325652831852848033 306954244239623889636025)
          ·
            refine ⟨230215683179717917227019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306954244239623889636025 230215683179717917227019)
            ·
              refine ⟨345323524769576875840529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230215683179717917227019 345323524769576875840529)
              ·
                refine ⟨258992643577182656880397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345323524769576875840529 258992643577182656880397)
                ·
                  refine ⟨97122241341443496330149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258992643577182656880397 97122241341443496330149)
                  ·
                    refine ⟨18210420251520655561903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97122241341443496330149 18210420251520655561903)
                    ·
                      rfl

theorem cell23_106394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_106394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106394 prefixEnd_106394 := by exact prefixLift 106394
  have htrace : WordTrace (prefixWord ++ tailWord_106394) baseStart_106394 baseEnd_106394 := by
    simpa [prefixWord, tailWord_106394, baseEnd_106394] using wordTrace_append hprefix tailTrace_106394
  have hstable : (prefixWord ++ tailWord_106394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106394).length < 2 ^ (prefixWord ++ tailWord_106394).sum := by decide
  have hdescent : baseEnd_106394 < baseStart_106394 := by decide
  rcases family_descends (prefixWord ++ tailWord_106394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106398 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_106398 : Nat := 118140960795 + 106398 * 2 ^ 59
def prefixEnd_106398 : Nat := 4983230072969 + 3 ^ 40 * 106398 * 2
def baseEnd_106398 : Nat := 18211104892393317011897

theorem tailTrace_106398 : CollatzResearch.WordTrace tailWord_106398 prefixEnd_106398 18211104892393317011897 := by
  unfold tailWord_106398
  simp only [CollatzResearch.WordTrace]
  refine ⟨485081733568211522101981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2587102579030461451210565 485081733568211522101981)
  ·
    refine ⟨181905650088079320788243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 485081733568211522101981 181905650088079320788243)
    ·
      refine ⟨272858475132118981182365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181905650088079320788243 272858475132118981182365)
      ·
        refine ⟨102321928174544617943387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272858475132118981182365 102321928174544617943387)
        ·
          refine ⟨153482892261816926915081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102321928174544617943387 153482892261816926915081)
          ·
            refine ⟨115112169196362695186311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153482892261816926915081 115112169196362695186311)
            ·
              refine ⟨172668253794544042779467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115112169196362695186311 172668253794544042779467)
              ·
                refine ⟨259002380691816064169201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172668253794544042779467 259002380691816064169201)
                ·
                  refine ⟨194251785518862048126901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259002380691816064169201 194251785518862048126901)
                  ·
                    refine ⟨18211104892393317011897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194251785518862048126901 18211104892393317011897)
                    ·
                      rfl

theorem cell23_106398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_106398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106398 prefixEnd_106398 := by exact prefixLift 106398
  have htrace : WordTrace (prefixWord ++ tailWord_106398) baseStart_106398 baseEnd_106398 := by
    simpa [prefixWord, tailWord_106398, baseEnd_106398] using wordTrace_append hprefix tailTrace_106398
  have hstable : (prefixWord ++ tailWord_106398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106398).length < 2 ^ (prefixWord ++ tailWord_106398).sum := by decide
  have hdescent : baseEnd_106398 < baseStart_106398 := by decide
  rcases family_descends (prefixWord ++ tailWord_106398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106401 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_106401 : Nat := 118140960795 + 106401 * 2 ^ 59
def prefixEnd_106401 : Nat := 4983230072969 + 3 ^ 40 * 106401 * 2
def baseEnd_106401 : Nat := 54634855119143439298177

theorem tailTrace_106401 : CollatzResearch.WordTrace tailWord_106401 prefixEnd_106401 54634855119143439298177 := by
  unfold tailWord_106401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880763287534823689175057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2587175525023215792783371 3880763287534823689175057)
  ·
    refine ⟨2910572465651117766881293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3880763287534823689175057 2910572465651117766881293)
    ·
      refine ⟨1091464674619169162580485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2910572465651117766881293 1091464674619169162580485)
      ·
        refine ⟨204649626491094217983841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1091464674619169162580485 204649626491094217983841)
        ·
          refine ⟨153487219868320663487881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204649626491094217983841 153487219868320663487881)
          ·
            refine ⟨115115414901240497615911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153487219868320663487881 115115414901240497615911)
            ·
              refine ⟨172673122351860746423867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115115414901240497615911 172673122351860746423867)
              ·
                refine ⟨259009683527791119635801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172673122351860746423867 259009683527791119635801)
                ·
                  refine ⟨194257262645843339726851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259009683527791119635801 194257262645843339726851)
                  ·
                    refine ⟨291385893968765009590277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194257262645843339726851 291385893968765009590277)
                    ·
                      refine ⟨54634855119143439298177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 291385893968765009590277 54634855119143439298177)
                      ·
                        rfl

theorem cell23_106401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_106401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106401 prefixEnd_106401 := by exact prefixLift 106401
  have htrace : WordTrace (prefixWord ++ tailWord_106401) baseStart_106401 baseEnd_106401 := by
    simpa [prefixWord, tailWord_106401, baseEnd_106401] using wordTrace_append hprefix tailTrace_106401
  have hstable : (prefixWord ++ tailWord_106401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106401).length < 2 ^ (prefixWord ++ tailWord_106401).sum := by decide
  have hdescent : baseEnd_106401 < baseStart_106401 := by decide
  rcases family_descends (prefixWord ++ tailWord_106401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106404 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_106404 : Nat := 118140960795 + 106404 * 2 ^ 59
def prefixEnd_106404 : Nat := 4983230072969 + 3 ^ 40 * 106404 * 2
def baseEnd_106404 : Nat := 54636395561106927560663

theorem tailTrace_106404 : CollatzResearch.WordTrace tailWord_106404 prefixEnd_106404 54636395561106927560663 := by
  unfold tailWord_106404
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940436353261977600767133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2587248471015970134356177 1940436353261977600767133)
  ·
    refine ⟨727663632473241600287675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1940436353261977600767133 727663632473241600287675)
    ·
      refine ⟨1091495448709862400431513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727663632473241600287675 1091495448709862400431513)
      ·
        refine ⟨818621586532396800323635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091495448709862400431513 818621586532396800323635)
        ·
          refine ⟨1227932379798595200485453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818621586532396800323635 1227932379798595200485453)
          ·
            refine ⟨460474642424473200182045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1227932379798595200485453 460474642424473200182045)
            ·
              refine ⟨172677990909177450068267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460474642424473200182045 172677990909177450068267)
              ·
                refine ⟨259016986363766175102401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172677990909177450068267 259016986363766175102401)
                ·
                  refine ⟨194262739772824631326801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259016986363766175102401 194262739772824631326801)
                  ·
                    refine ⟨145697054829618473495101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194262739772824631326801 145697054829618473495101)
                    ·
                      refine ⟨54636395561106927560663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 145697054829618473495101 54636395561106927560663)
                      ·
                        rfl

theorem cell23_106404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_106404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106404 prefixEnd_106404 := by exact prefixLift 106404
  have htrace : WordTrace (prefixWord ++ tailWord_106404) baseStart_106404 baseEnd_106404 := by
    simpa [prefixWord, tailWord_106404, baseEnd_106404] using wordTrace_append hprefix tailTrace_106404
  have hstable : (prefixWord ++ tailWord_106404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106404).length < 2 ^ (prefixWord ++ tailWord_106404).sum := by decide
  have hdescent : baseEnd_106404 < baseStart_106404 := by decide
  rcases family_descends (prefixWord ++ tailWord_106404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106427 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 5, 2]
def baseStart_106427 : Nat := 118140960795 + 106427 * 2 ^ 59
def prefixEnd_106427 : Nat := 4983230072969 + 3 ^ 40 * 106427 * 2
def baseEnd_106427 : Nat := 54648205616160337573057

theorem tailTrace_106427 : CollatzResearch.WordTrace tailWord_106427 prefixEnd_106427 54648205616160337573057 := by
  unfold tailWord_106427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881711585440630129621535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2587807723627086753081023 3881711585440630129621535)
  ·
    refine ⟨5822567378160945194432303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3881711585440630129621535 5822567378160945194432303)
    ·
      refine ⟨8733851067241417791648455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5822567378160945194432303 8733851067241417791648455)
      ·
        refine ⟨13100776600862126687472683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8733851067241417791648455 13100776600862126687472683)
        ·
          refine ⟨19651164901293190031209025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100776600862126687472683 19651164901293190031209025)
          ·
            refine ⟨14738373675969892523406769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19651164901293190031209025 14738373675969892523406769)
            ·
              refine ⟨11053780256977419392555077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14738373675969892523406769 11053780256977419392555077)
              ·
                refine ⟨2072583798183266136104077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11053780256977419392555077 2072583798183266136104077)
                ·
                  refine ⟨777218924318724801039029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2072583798183266136104077 777218924318724801039029)
                  ·
                    refine ⟨72864274154880450097409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 777218924318724801039029 72864274154880450097409)
                    ·
                      refine ⟨54648205616160337573057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72864274154880450097409 54648205616160337573057)
                      ·
                        rfl

theorem cell23_106427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5, 2].length) (baseStart_106427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106427 prefixEnd_106427 := by exact prefixLift 106427
  have htrace : WordTrace (prefixWord ++ tailWord_106427) baseStart_106427 baseEnd_106427 := by
    simpa [prefixWord, tailWord_106427, baseEnd_106427] using wordTrace_append hprefix tailTrace_106427
  have hstable : (prefixWord ++ tailWord_106427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106427).length < 2 ^ (prefixWord ++ tailWord_106427).sum := by decide
  have hdescent : baseEnd_106427 < baseStart_106427 := by decide
  rcases family_descends (prefixWord ++ tailWord_106427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106444 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_106444 : Nat := 118140960795 + 106444 * 2 ^ 59
def prefixEnd_106444 : Nat := 4983230072969 + 3 ^ 40 * 106444 * 2
def baseEnd_106444 : Nat := 54656934787286771060479

theorem tailTrace_106444 : CollatzResearch.WordTrace tailWord_106444 prefixEnd_106444 54656934787286771060479 := by
  unfold tailWord_106444
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941165813189521016495193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2588221084252694688660257 1941165813189521016495193)
  ·
    refine ⟨1455874359892140762371395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1941165813189521016495193 1455874359892140762371395)
    ·
      refine ⟨2183811539838211143557093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455874359892140762371395 2183811539838211143557093)
      ·
        refine ⟨409464663719664589416955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2183811539838211143557093 409464663719664589416955)
        ·
          refine ⟨614196995579496884125433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409464663719664589416955 614196995579496884125433)
          ·
            refine ⟨460647746684622663094075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614196995579496884125433 460647746684622663094075)
            ·
              refine ⟨690971620026933994641113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460647746684622663094075 690971620026933994641113)
              ·
                refine ⟨518228715020200495980835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690971620026933994641113 518228715020200495980835)
                ·
                  refine ⟨777343072530300743971253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518228715020200495980835 777343072530300743971253)
                  ·
                    refine ⟨72875913049715694747305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 777343072530300743971253 72875913049715694747305)
                    ·
                      refine ⟨54656934787286771060479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72875913049715694747305 54656934787286771060479)
                      ·
                        rfl

theorem cell23_106444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_106444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106444 prefixEnd_106444 := by exact prefixLift 106444
  have htrace : WordTrace (prefixWord ++ tailWord_106444) baseStart_106444 baseEnd_106444 := by
    simpa [prefixWord, tailWord_106444, baseEnd_106444] using wordTrace_append hprefix tailTrace_106444
  have hstable : (prefixWord ++ tailWord_106444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106444).length < 2 ^ (prefixWord ++ tailWord_106444).sum := by decide
  have hdescent : baseEnd_106444 < baseStart_106444 := by decide
  rcases family_descends (prefixWord ++ tailWord_106444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106474 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_106474 : Nat := 118140960795 + 106474 * 2 ^ 59
def prefixEnd_106474 : Nat := 4983230072969 + 3 ^ 40 * 106474 * 2
def baseEnd_106474 : Nat := 54672339206921653685341

theorem tailTrace_106474 : CollatzResearch.WordTrace tailWord_106474 prefixEnd_106474 54672339206921653685341 := by
  unfold tailWord_106474
  simp only [CollatzResearch.WordTrace]
  refine ⟨970856454067589289145619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2588950544180238104388317 970856454067589289145619)
  ·
    refine ⟨1456284681101383933718429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970856454067589289145619 1456284681101383933718429)
    ·
      refine ⟨546106755413018975144411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1456284681101383933718429 546106755413018975144411)
      ·
        refine ⟨819160133119528462716617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546106755413018975144411 819160133119528462716617)
        ·
          refine ⟨614370099839646347037463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819160133119528462716617 614370099839646347037463)
          ·
            refine ⟨921555149759469520556195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614370099839646347037463 921555149759469520556195)
            ·
              refine ⟨1382332724639204280834293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921555149759469520556195 1382332724639204280834293)
              ·
                refine ⟨129593692934925401328215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1382332724639204280834293 129593692934925401328215)
                ·
                  refine ⟨194390539402388101992323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129593692934925401328215 194390539402388101992323)
                  ·
                    refine ⟨291585809103582152988485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194390539402388101992323 291585809103582152988485)
                    ·
                      refine ⟨54672339206921653685341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 291585809103582152988485 54672339206921653685341)
                      ·
                        rfl

theorem cell23_106474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_106474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106474 prefixEnd_106474 := by exact prefixLift 106474
  have htrace : WordTrace (prefixWord ++ tailWord_106474) baseStart_106474 baseEnd_106474 := by
    simpa [prefixWord, tailWord_106474, baseEnd_106474] using wordTrace_append hprefix tailTrace_106474
  have hstable : (prefixWord ++ tailWord_106474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106474).length < 2 ^ (prefixWord ++ tailWord_106474).sum := by decide
  have hdescent : baseEnd_106474 < baseStart_106474 := by decide
  rcases family_descends (prefixWord ++ tailWord_106474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106480 : List Nat := [2, 1, 1, 1, 3, 2, 13]
def baseStart_106480 : Nat := 118140960795 + 106480 * 2 ^ 59
def prefixEnd_106480 : Nat := 4983230072969 + 3 ^ 40 * 106480 * 2
def baseEnd_106480 : Nat := 675005186306773212473

theorem tailTrace_106480 : CollatzResearch.WordTrace tailWord_106480 prefixEnd_106480 675005186306773212473 := by
  unfold tailWord_106480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941822327124310090650447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2589096436165746787533929 1941822327124310090650447)
  ·
    refine ⟨2912733490686465135975671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941822327124310090650447 2912733490686465135975671)
    ·
      refine ⟨4369100236029697703963507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912733490686465135975671 4369100236029697703963507)
      ·
        refine ⟨6553650354044546555945261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369100236029697703963507 6553650354044546555945261)
        ·
          refine ⟨2457618882766704958479473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6553650354044546555945261 2457618882766704958479473)
          ·
            refine ⟨1843214162075028718859605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2457618882766704958479473 1843214162075028718859605)
            ·
              refine ⟨675005186306773212473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 1843214162075028718859605 675005186306773212473)
              ·
                rfl

theorem cell23_106480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 13].length) (baseStart_106480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106480 prefixEnd_106480 := by exact prefixLift 106480
  have htrace : WordTrace (prefixWord ++ tailWord_106480) baseStart_106480 baseEnd_106480 := by
    simpa [prefixWord, tailWord_106480, baseEnd_106480] using wordTrace_append hprefix tailTrace_106480
  have hstable : (prefixWord ++ tailWord_106480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106480).length < 2 ^ (prefixWord ++ tailWord_106480).sum := by decide
  have hdescent : baseEnd_106480 < baseStart_106480 := by decide
  rcases family_descends (prefixWord ++ tailWord_106480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106491 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 3, 2, 2]
def baseStart_106491 : Nat := 118140960795 + 106491 * 2 ^ 59
def prefixEnd_106491 : Nat := 4983230072969 + 3 ^ 40 * 106491 * 2
def baseEnd_106491 : Nat := 54681068378048087172763

theorem tailTrace_106491 : CollatzResearch.WordTrace tailWord_106491 prefixEnd_106491 54681068378048087172763 := by
  unfold tailWord_106491
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884045857208769059951327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2589363904805846039967551 3884045857208769059951327)
  ·
    refine ⟨5826068785813153589926991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3884045857208769059951327 5826068785813153589926991)
    ·
      refine ⟨8739103178719730384890487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5826068785813153589926991 8739103178719730384890487)
      ·
        refine ⟨13108654768079595577335731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739103178719730384890487 13108654768079595577335731)
        ·
          refine ⟨19662982152119393366003597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108654768079595577335731 19662982152119393366003597)
          ·
            refine ⟨7373618307044772512251349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19662982152119393366003597 7373618307044772512251349)
            ·
              refine ⟨172819179071361855755891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7373618307044772512251349 172819179071361855755891)
              ·
                refine ⟨259228768607042783633837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172819179071361855755891 259228768607042783633837)
                ·
                  refine ⟨97210788227641043862689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259228768607042783633837 97210788227641043862689)
                  ·
                    refine ⟨72908091170730782897017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97210788227641043862689 72908091170730782897017)
                    ·
                      refine ⟨54681068378048087172763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72908091170730782897017 54681068378048087172763)
                      ·
                        rfl

theorem cell23_106491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2, 2].length) (baseStart_106491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106491 prefixEnd_106491 := by exact prefixLift 106491
  have htrace : WordTrace (prefixWord ++ tailWord_106491) baseStart_106491 baseEnd_106491 := by
    simpa [prefixWord, tailWord_106491, baseEnd_106491] using wordTrace_append hprefix tailTrace_106491
  have hstable : (prefixWord ++ tailWord_106491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106491).length < 2 ^ (prefixWord ++ tailWord_106491).sum := by decide
  have hdescent : baseEnd_106491 < baseStart_106491 := by decide
  rcases family_descends (prefixWord ++ tailWord_106491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106497 : List Nat := [1, 2, 4, 1, 2, 1, 4, 8]
def baseStart_106497 : Nat := 118140960795 + 106497 * 2 ^ 59
def prefixEnd_106497 : Nat := 4983230072969 + 3 ^ 40 * 106497 * 2
def baseEnd_106497 : Nat := 2025338861554631988805

theorem tailTrace_106497 : CollatzResearch.WordTrace tailWord_106497 prefixEnd_106497 2025338861554631988805 := by
  unfold tailWord_106497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884264695187032084669745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2589509796791354723113163 3884264695187032084669745)
  ·
    refine ⟨2913198521390274063502309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3884264695187032084669745 2913198521390274063502309)
    ·
      refine ⟨546224722760676386906683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2913198521390274063502309 546224722760676386906683)
      ·
        refine ⟨819337084141014580360025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546224722760676386906683 819337084141014580360025)
        ·
          refine ⟨614502813105760935270019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819337084141014580360025 614502813105760935270019)
          ·
            refine ⟨921754219658641402905029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614502813105760935270019 921754219658641402905029)
            ·
              refine ⟨172828916185995263044693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 921754219658641402905029 172828916185995263044693)
              ·
                refine ⟨2025338861554631988805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 172828916185995263044693 2025338861554631988805)
                ·
                  rfl

theorem cell23_106497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 8].length) (baseStart_106497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106497 prefixEnd_106497 := by exact prefixLift 106497
  have htrace : WordTrace (prefixWord ++ tailWord_106497) baseStart_106497 baseEnd_106497 := by
    simpa [prefixWord, tailWord_106497, baseEnd_106497] using wordTrace_append hprefix tailTrace_106497
  have hstable : (prefixWord ++ tailWord_106497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106497).length < 2 ^ (prefixWord ++ tailWord_106497).sum := by decide
  have hdescent : baseEnd_106497 < baseStart_106497 := by decide
  rcases family_descends (prefixWord ++ tailWord_106497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106501 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_106501 : Nat := 118140960795 + 106501 * 2 ^ 59
def prefixEnd_106501 : Nat := 4983230072969 + 3 ^ 40 * 106501 * 2
def baseEnd_106501 : Nat := 18228734394864349349239

theorem tailTrace_106501 : CollatzResearch.WordTrace tailWord_106501 prefixEnd_106501 18228734394864349349239 := by
  unfold tailWord_106501
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884410587172540767815357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2589607058115027178543571 3884410587172540767815357)
  ·
    refine ⟨1456653970189702787930759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3884410587172540767815357 1456653970189702787930759)
    ·
      refine ⟨2184980955284554181896139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456653970189702787930759 2184980955284554181896139)
      ·
        refine ⟨3277471432926831272844209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184980955284554181896139 3277471432926831272844209)
        ·
          refine ⟨2458103574695123454633157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3277471432926831272844209 2458103574695123454633157)
          ·
            refine ⟨460894420255335647743717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2458103574695123454633157 460894420255335647743717)
            ·
              refine ⟨86417703797875433951947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460894420255335647743717 86417703797875433951947)
              ·
                refine ⟨129626555696813150927921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86417703797875433951947 129626555696813150927921)
                ·
                  refine ⟨97219916772609863195941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129626555696813150927921 97219916772609863195941)
                  ·
                    refine ⟨18228734394864349349239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97219916772609863195941 18228734394864349349239)
                    ·
                      rfl

theorem cell23_106501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_106501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106501 prefixEnd_106501 := by exact prefixLift 106501
  have htrace : WordTrace (prefixWord ++ tailWord_106501) baseStart_106501 baseEnd_106501 := by
    simpa [prefixWord, tailWord_106501, baseEnd_106501] using wordTrace_append hprefix tailTrace_106501
  have hstable : (prefixWord ++ tailWord_106501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106501).length < 2 ^ (prefixWord ++ tailWord_106501).sum := by decide
  have hdescent : baseEnd_106501 < baseStart_106501 := by decide
  rcases family_descends (prefixWord ++ tailWord_106501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106524 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_106524 : Nat := 118140960795 + 106524 * 2 ^ 59
def prefixEnd_106524 : Nat := 4983230072969 + 3 ^ 40 * 106524 * 2
def baseEnd_106524 : Nat := 54698013239646458060111

theorem tailTrace_106524 : CollatzResearch.WordTrace tailWord_106524 prefixEnd_106524 54698013239646458060111 := by
  unfold tailWord_106524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942624733044607847951313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2590166310726143797268417 1942624733044607847951313)
  ·
    refine ⟨1456968549783455885963485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1942624733044607847951313 1456968549783455885963485)
    ·
      refine ⟨546363206168795957236307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1456968549783455885963485 546363206168795957236307)
      ·
        refine ⟨819544809253193935854461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546363206168795957236307 819544809253193935854461)
        ·
          refine ⟨307329303469947725945423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819544809253193935854461 307329303469947725945423)
          ·
            refine ⟨460993955204921588918135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307329303469947725945423 460993955204921588918135)
            ·
              refine ⟨691490932807382383377203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460993955204921588918135 691490932807382383377203)
              ·
                refine ⟨1037236399211073575065805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691490932807382383377203 1037236399211073575065805)
                ·
                  refine ⟨388963649704152590649677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037236399211073575065805 388963649704152590649677)
                  ·
                    refine ⟨145861368639057221493629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388963649704152590649677 145861368639057221493629)
                    ·
                      refine ⟨54698013239646458060111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 145861368639057221493629 54698013239646458060111)
                      ·
                        rfl

theorem cell23_106524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_106524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106524 prefixEnd_106524 := by exact prefixLift 106524
  have htrace : WordTrace (prefixWord ++ tailWord_106524) baseStart_106524 baseEnd_106524 := by
    simpa [prefixWord, tailWord_106524, baseEnd_106524] using wordTrace_append hprefix tailTrace_106524
  have hstable : (prefixWord ++ tailWord_106524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106524).length < 2 ^ (prefixWord ++ tailWord_106524).sum := by decide
  have hdescent : baseEnd_106524 < baseStart_106524 := by decide
  rcases family_descends (prefixWord ++ tailWord_106524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106542 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_106542 : Nat := 118140960795 + 106542 * 2 ^ 59
def prefixEnd_106542 : Nat := 4983230072969 + 3 ^ 40 * 106542 * 2
def baseEnd_106542 : Nat := 54707255891427387635029

theorem tailTrace_106542 : CollatzResearch.WordTrace tailWord_106542 prefixEnd_106542 54707255891427387635029 := by
  unfold tailWord_106542
  simp only [CollatzResearch.WordTrace]
  refine ⟨485738247503000596257235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2590603986682669846705253 485738247503000596257235)
  ·
    refine ⟨728607371254500894385853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 485738247503000596257235 728607371254500894385853)
    ·
      refine ⟨273227764220437835394695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 728607371254500894385853 273227764220437835394695)
      ·
        refine ⟨409841646330656753092043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273227764220437835394695 409841646330656753092043)
        ·
          refine ⟨614762469495985129638065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409841646330656753092043 614762469495985129638065)
          ·
            refine ⟨461071852121988847228549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614762469495985129638065 461071852121988847228549)
            ·
              refine ⟨86450972272872908855353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461071852121988847228549 86450972272872908855353)
              ·
                refine ⟨64838229204654681641515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86450972272872908855353 64838229204654681641515)
                ·
                  refine ⟨97257343806982022462273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64838229204654681641515 97257343806982022462273)
                  ·
                    refine ⟨72943007855236516846705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97257343806982022462273 72943007855236516846705)
                    ·
                      refine ⟨54707255891427387635029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72943007855236516846705 54707255891427387635029)
                      ·
                        rfl

theorem cell23_106542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_106542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106542 prefixEnd_106542 := by exact prefixLift 106542
  have htrace : WordTrace (prefixWord ++ tailWord_106542) baseStart_106542 baseEnd_106542 := by
    simpa [prefixWord, tailWord_106542, baseEnd_106542] using wordTrace_append hprefix tailTrace_106542
  have hstable : (prefixWord ++ tailWord_106542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106542).length < 2 ^ (prefixWord ++ tailWord_106542).sum := by decide
  have hdescent : baseEnd_106542 < baseStart_106542 := by decide
  rcases family_descends (prefixWord ++ tailWord_106542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106547 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_106547 : Nat := 118140960795 + 106547 * 2 ^ 59
def prefixEnd_106547 : Nat := 4983230072969 + 3 ^ 40 * 106547 * 2
def baseEnd_106547 : Nat := 54709823294699868072505

theorem tailTrace_106547 : CollatzResearch.WordTrace tailWord_106547 prefixEnd_106547 54709823294699868072505 := by
  unfold tailWord_106547
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886088345005890623989895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2590725563337260415993263 3886088345005890623989895)
  ·
    refine ⟨5829132517508835935984843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3886088345005890623989895 5829132517508835935984843)
    ·
      refine ⟨8743698776263253903977265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829132517508835935984843 8743698776263253903977265)
      ·
        refine ⟨6557774082197440427982949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8743698776263253903977265 6557774082197440427982949)
        ·
          refine ⟨1229582640412020080246803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6557774082197440427982949 1229582640412020080246803)
          ·
            refine ⟨1844373960618030120370205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229582640412020080246803 1844373960618030120370205)
            ·
              refine ⟨691640235231761295138827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1844373960618030120370205 691640235231761295138827)
              ·
                refine ⟨1037460352847641942708241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691640235231761295138827 1037460352847641942708241)
                ·
                  refine ⟨778095264635731457031181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037460352847641942708241 778095264635731457031181)
                  ·
                    refine ⟨291785724238399296386693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778095264635731457031181 291785724238399296386693)
                    ·
                      refine ⟨54709823294699868072505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 291785724238399296386693 54709823294699868072505)
                      ·
                        rfl

theorem cell23_106547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_106547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106547 prefixEnd_106547 := by exact prefixLift 106547
  have htrace : WordTrace (prefixWord ++ tailWord_106547) baseStart_106547 baseEnd_106547 := by
    simpa [prefixWord, tailWord_106547, baseEnd_106547] using wordTrace_append hprefix tailTrace_106547
  have hstable : (prefixWord ++ tailWord_106547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106547).length < 2 ^ (prefixWord ++ tailWord_106547).sum := by decide
  have hdescent : baseEnd_106547 < baseStart_106547 := by decide
  rcases family_descends (prefixWord ++ tailWord_106547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106548 : List Nat := [2, 5, 1, 2, 3, 1, 1, 8]
def baseStart_106548 : Nat := 118140960795 + 106548 * 2 ^ 59
def prefixEnd_106548 : Nat := 4983230072969 + 3 ^ 40 * 106548 * 2
def baseEnd_106548 : Nat := 2026308769457569042963

theorem tailTrace_106548 : CollatzResearch.WordTrace tailWord_106548 prefixEnd_106548 2026308769457569042963 := by
  unfold tailWord_106548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943062409001133897388149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2590749878668178529850865 1943062409001133897388149)
  ·
    refine ⟨182162100843856302880139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1943062409001133897388149 182162100843856302880139)
    ·
      refine ⟨273243151265784454320209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182162100843856302880139 273243151265784454320209)
      ·
        refine ⟨204932363449338340740157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273243151265784454320209 204932363449338340740157)
        ·
          refine ⟨76849636293501877777559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204932363449338340740157 76849636293501877777559)
          ·
            refine ⟨115274454440252816666339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76849636293501877777559 115274454440252816666339)
            ·
              refine ⟨172911681660379224999509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115274454440252816666339 172911681660379224999509)
              ·
                refine ⟨2026308769457569042963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 172911681660379224999509 2026308769457569042963)
                ·
                  rfl

theorem cell23_106548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 8].length) (baseStart_106548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106548 prefixEnd_106548 := by exact prefixLift 106548
  have htrace : WordTrace (prefixWord ++ tailWord_106548) baseStart_106548 baseEnd_106548 := by
    simpa [prefixWord, tailWord_106548, baseEnd_106548] using wordTrace_append hprefix tailTrace_106548
  have hstable : (prefixWord ++ tailWord_106548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106548).length < 2 ^ (prefixWord ++ tailWord_106548).sum := by decide
  have hdescent : baseEnd_106548 < baseStart_106548 := by decide
  rcases family_descends (prefixWord ++ tailWord_106548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106558 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_106558 : Nat := 118140960795 + 106558 * 2 ^ 59
def prefixEnd_106558 : Nat := 4983230072969 + 3 ^ 40 * 106558 * 2
def baseEnd_106558 : Nat := 54715471581899325034955

theorem tailTrace_106558 : CollatzResearch.WordTrace tailWord_106558 prefixEnd_106558 54715471581899325034955 := by
  unfold tailWord_106558
  simp only [CollatzResearch.WordTrace]
  refine ⟨485811193495754937830041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2590993031977359668426885 485811193495754937830041)
  ·
    refine ⟨364358395121816203372531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 485811193495754937830041 364358395121816203372531)
    ·
      refine ⟨546537592682724305058797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364358395121816203372531 546537592682724305058797)
      ·
        refine ⟨204951597256021614397049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546537592682724305058797 204951597256021614397049)
        ·
          refine ⟨153713697942016210797787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204951597256021614397049 153713697942016210797787)
          ·
            refine ⟨230570546913024316196681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153713697942016210797787 230570546913024316196681)
            ·
              refine ⟨172927910184768237147511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230570546913024316196681 172927910184768237147511)
              ·
                refine ⟨259391865277152355721267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172927910184768237147511 259391865277152355721267)
                ·
                  refine ⟨389087797915728533581901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259391865277152355721267 389087797915728533581901)
                  ·
                    refine ⟨145907924218398200093213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389087797915728533581901 145907924218398200093213)
                    ·
                      refine ⟨54715471581899325034955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 145907924218398200093213 54715471581899325034955)
                      ·
                        rfl

theorem cell23_106558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_106558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106558 prefixEnd_106558 := by exact prefixLift 106558
  have htrace : WordTrace (prefixWord ++ tailWord_106558) baseStart_106558 baseEnd_106558 := by
    simpa [prefixWord, tailWord_106558, baseEnd_106558] using wordTrace_append hprefix tailTrace_106558
  have hstable : (prefixWord ++ tailWord_106558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106558).length < 2 ^ (prefixWord ++ tailWord_106558).sum := by decide
  have hdescent : baseEnd_106558 < baseStart_106558 := by decide
  rcases family_descends (prefixWord ++ tailWord_106558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106577 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_106577 : Nat := 118140960795 + 106577 * 2 ^ 59
def prefixEnd_106577 : Nat := 4983230072969 + 3 ^ 40 * 106577 * 2
def baseEnd_106577 : Nat := 54725227714334750697367

theorem tailTrace_106577 : CollatzResearch.WordTrace tailWord_106577 prefixEnd_106577 54725227714334750697367 := by
  unfold tailWord_106577
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887182534897205747581985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2591455023264803831721323 3887182534897205747581985)
  ·
    refine ⟨2915386901172904310686489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3887182534897205747581985 2915386901172904310686489)
    ·
      refine ⟨2186540175879678233014867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2915386901172904310686489 2186540175879678233014867)
      ·
        refine ⟨3279810263819517349522301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186540175879678233014867 3279810263819517349522301)
        ·
          refine ⟨1229928848932319006070863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3279810263819517349522301 1229928848932319006070863)
          ·
            refine ⟨1844893273398478509106295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229928848932319006070863 1844893273398478509106295)
            ·
              refine ⟨2767339910097717763659443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844893273398478509106295 2767339910097717763659443)
              ·
                refine ⟨4151009865146576645489165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767339910097717763659443 4151009865146576645489165)
                ·
                  refine ⟨1556628699429966242058437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4151009865146576645489165 1556628699429966242058437)
                  ·
                    refine ⟨291867881143118670385957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556628699429966242058437 291867881143118670385957)
                    ·
                      refine ⟨54725227714334750697367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 291867881143118670385957 54725227714334750697367)
                      ·
                        rfl

theorem cell23_106577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_106577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106577 prefixEnd_106577 := by exact prefixLift 106577
  have htrace : WordTrace (prefixWord ++ tailWord_106577) baseStart_106577 baseEnd_106577 := by
    simpa [prefixWord, tailWord_106577, baseEnd_106577] using wordTrace_append hprefix tailTrace_106577
  have hstable : (prefixWord ++ tailWord_106577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106577).length < 2 ^ (prefixWord ++ tailWord_106577).sum := by decide
  have hdescent : baseEnd_106577 < baseStart_106577 := by decide
  rcases family_descends (prefixWord ++ tailWord_106577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106581 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_106581 : Nat := 118140960795 + 106581 * 2 ^ 59
def prefixEnd_106581 : Nat := 4983230072969 + 3 ^ 40 * 106581 * 2
def baseEnd_106581 : Nat := 54727281636952735047349

theorem tailTrace_106581 : CollatzResearch.WordTrace tailWord_106581 prefixEnd_106581 54727281636952735047349 := by
  unfold tailWord_106581
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887328426882714430727597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2591552284588476287151731 3887328426882714430727597)
  ·
    refine ⟨1457748160081017911522849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3887328426882714430727597 1457748160081017911522849)
    ·
      refine ⟨1093311120060763433642137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1457748160081017911522849 1093311120060763433642137)
      ·
        refine ⟨819983340045572575231603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1093311120060763433642137 819983340045572575231603)
        ·
          refine ⟨1229975010068358862847405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819983340045572575231603 1229975010068358862847405)
          ·
            refine ⟨461240628775634573567777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1229975010068358862847405 461240628775634573567777)
            ·
              refine ⟨345930471581725930175833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461240628775634573567777 345930471581725930175833)
              ·
                refine ⟨259447853686294447631875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345930471581725930175833 259447853686294447631875)
                ·
                  refine ⟨389171780529441671447813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259447853686294447631875 389171780529441671447813)
                  ·
                    refine ⟨72969708849270313396465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389171780529441671447813 72969708849270313396465)
                    ·
                      refine ⟨54727281636952735047349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72969708849270313396465 54727281636952735047349)
                      ·
                        rfl

theorem cell23_106581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_106581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106581 prefixEnd_106581 := by exact prefixLift 106581
  have htrace : WordTrace (prefixWord ++ tailWord_106581) baseStart_106581 baseEnd_106581 := by
    simpa [prefixWord, tailWord_106581, baseEnd_106581] using wordTrace_append hprefix tailTrace_106581
  have hstable : (prefixWord ++ tailWord_106581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106581).length < 2 ^ (prefixWord ++ tailWord_106581).sum := by decide
  have hdescent : baseEnd_106581 < baseStart_106581 := by decide
  rcases family_descends (prefixWord ++ tailWord_106581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106604 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 7]
def baseStart_106604 : Nat := 118140960795 + 106604 * 2 ^ 59
def prefixEnd_106604 : Nat := 4983230072969 + 3 ^ 40 * 106604 * 2
def baseEnd_106604 : Nat := 6082121299111793895527

theorem tailTrace_106604 : CollatzResearch.WordTrace tailWord_106604 prefixEnd_106604 6082121299111793895527 := by
  unfold tailWord_106604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944083652899694679407433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2592111537199592905876577 1944083652899694679407433)
  ·
    refine ⟨1458062739674771009555575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1944083652899694679407433 1458062739674771009555575)
    ·
      refine ⟨2187094109512156514333363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458062739674771009555575 2187094109512156514333363)
      ·
        refine ⟨3280641164268234771500045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187094109512156514333363 3280641164268234771500045)
        ·
          refine ⟨1230240436600588039312517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3280641164268234771500045 1230240436600588039312517)
          ·
            refine ⟨230670081862610257371097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1230240436600588039312517 230670081862610257371097)
            ·
              refine ⟨173002561396957693028323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230670081862610257371097 173002561396957693028323)
              ·
                refine ⟨259503842095436539542485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173002561396957693028323 259503842095436539542485)
                ·
                  refine ⟨6082121299111793895527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259503842095436539542485 6082121299111793895527)
                  ·
                    rfl

theorem cell23_106604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_106604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106604 prefixEnd_106604 := by exact prefixLift 106604
  have htrace : WordTrace (prefixWord ++ tailWord_106604) baseStart_106604 baseEnd_106604 := by
    simpa [prefixWord, tailWord_106604, baseEnd_106604] using wordTrace_append hprefix tailTrace_106604
  have hstable : (prefixWord ++ tailWord_106604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106604).length < 2 ^ (prefixWord ++ tailWord_106604).sum := by decide
  have hdescent : baseEnd_106604 < baseStart_106604 := by decide
  rcases family_descends (prefixWord ++ tailWord_106604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106615 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_106615 : Nat := 118140960795 + 106615 * 2 ^ 59
def prefixEnd_106615 : Nat := 4983230072969 + 3 ^ 40 * 106615 * 2
def baseEnd_106615 : Nat := 54744739979205602022193

theorem tailTrace_106615 : CollatzResearch.WordTrace tailWord_106615 prefixEnd_106615 54744739979205602022193 := by
  unfold tailWord_106615
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888568508759538237465299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2592379005839692158310199 3888568508759538237465299)
  ·
    refine ⟨5832852763139307356197949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3888568508759538237465299 5832852763139307356197949)
    ·
      refine ⟨2187319786177240258574231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5832852763139307356197949 2187319786177240258574231)
      ·
        refine ⟨3280979679265860387861347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187319786177240258574231 3280979679265860387861347)
        ·
          refine ⟨4921469518898790581792021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280979679265860387861347 4921469518898790581792021)
          ·
            refine ⟨230693883698380808521501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4921469518898790581792021 230693883698380808521501)
            ·
              refine ⟨86510206386892803195563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230693883698380808521501 86510206386892803195563)
              ·
                refine ⟨129765309580339204793345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86510206386892803195563 129765309580339204793345)
                ·
                  refine ⟨97323982185254403595009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129765309580339204793345 97323982185254403595009)
                  ·
                    refine ⟨72992986638940802696257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97323982185254403595009 72992986638940802696257)
                    ·
                      refine ⟨54744739979205602022193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72992986638940802696257 54744739979205602022193)
                      ·
                        rfl

theorem cell23_106615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_106615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106615 prefixEnd_106615 := by exact prefixLift 106615
  have htrace : WordTrace (prefixWord ++ tailWord_106615) baseStart_106615 baseEnd_106615 := by
    simpa [prefixWord, tailWord_106615, baseEnd_106615] using wordTrace_append hprefix tailTrace_106615
  have hstable : (prefixWord ++ tailWord_106615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106615).length < 2 ^ (prefixWord ++ tailWord_106615).sum := by decide
  have hdescent : baseEnd_106615 < baseStart_106615 := by decide
  rcases family_descends (prefixWord ++ tailWord_106615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106634 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_106634 : Nat := 118140960795 + 106634 * 2 ^ 59
def prefixEnd_106634 : Nat := 4983230072969 + 3 ^ 40 * 106634 * 2
def baseEnd_106634 : Nat := 18251498703880342561535

theorem tailTrace_106634 : CollatzResearch.WordTrace tailWord_106634 prefixEnd_106634 18251498703880342561535 := by
  unfold tailWord_106634
  simp only [CollatzResearch.WordTrace]
  refine ⟨972315373922676120601739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2592840997127136321604637 972315373922676120601739)
  ·
    refine ⟨1458473060884014180902609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972315373922676120601739 1458473060884014180902609)
    ·
      refine ⟨1093854795663010635676957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458473060884014180902609 1093854795663010635676957)
      ·
        refine ⟨410195548373628988378859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1093854795663010635676957 410195548373628988378859)
        ·
          refine ⟨615293322560443482568289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410195548373628988378859 615293322560443482568289)
          ·
            refine ⟨461469991920332611926217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615293322560443482568289 461469991920332611926217)
            ·
              refine ⟨346102493940249458944663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461469991920332611926217 346102493940249458944663)
              ·
                refine ⟨519153740910374188416995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346102493940249458944663 519153740910374188416995)
                ·
                  refine ⟨778730611365561282625493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519153740910374188416995 778730611365561282625493)
                  ·
                    refine ⟨18251498703880342561535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 778730611365561282625493 18251498703880342561535)
                    ·
                      rfl

theorem cell23_106634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_106634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106634 prefixEnd_106634 := by exact prefixLift 106634
  have htrace : WordTrace (prefixWord ++ tailWord_106634) baseStart_106634 baseEnd_106634 := by
    simpa [prefixWord, tailWord_106634, baseEnd_106634] using wordTrace_append hprefix tailTrace_106634
  have hstable : (prefixWord ++ tailWord_106634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106634).length < 2 ^ (prefixWord ++ tailWord_106634).sum := by decide
  have hdescent : baseEnd_106634 < baseStart_106634 := by decide
  rcases family_descends (prefixWord ++ tailWord_106634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106666 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_106666 : Nat := 118140960795 + 106666 * 2 ^ 59
def prefixEnd_106666 : Nat := 4983230072969 + 3 ^ 40 * 106666 * 2
def baseEnd_106666 : Nat := 54770927492584902484459

theorem tailTrace_106666 : CollatzResearch.WordTrace tailWord_106666 prefixEnd_106666 54770927492584902484459 := by
  unfold tailWord_106666
  simp only [CollatzResearch.WordTrace]
  refine ⟨972607157893693486892963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2593619087716515965047901 972607157893693486892963)
  ·
    refine ⟨1458910736840540230339445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972607157893693486892963 1458910736840540230339445)
    ·
      refine ⟨136772881578800646594323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1458910736840540230339445 136772881578800646594323)
      ·
        refine ⟨205159322368200969891485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136772881578800646594323 205159322368200969891485)
        ·
          refine ⟨76934745888075363709307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205159322368200969891485 76934745888075363709307)
          ·
            refine ⟨115402118832113045563961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76934745888075363709307 115402118832113045563961)
            ·
              refine ⟨86551589124084784172971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115402118832113045563961 86551589124084784172971)
              ·
                refine ⟨129827383686127176259457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86551589124084784172971 129827383686127176259457)
                ·
                  refine ⟨97370537764595382194593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129827383686127176259457 97370537764595382194593)
                  ·
                    refine ⟨73027903323446536645945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97370537764595382194593 73027903323446536645945)
                    ·
                      refine ⟨54770927492584902484459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73027903323446536645945 54770927492584902484459)
                      ·
                        rfl

theorem cell23_106666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_106666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106666 prefixEnd_106666 := by exact prefixLift 106666
  have htrace : WordTrace (prefixWord ++ tailWord_106666) baseStart_106666 baseEnd_106666 := by
    simpa [prefixWord, tailWord_106666, baseEnd_106666] using wordTrace_append hprefix tailTrace_106666
  have hstable : (prefixWord ++ tailWord_106666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106666).length < 2 ^ (prefixWord ++ tailWord_106666).sum := by decide
  have hdescent : baseEnd_106666 < baseStart_106666 := by decide
  rcases family_descends (prefixWord ++ tailWord_106666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106667 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_106667 : Nat := 118140960795 + 106667 * 2 ^ 59
def prefixEnd_106667 : Nat := 4983230072969 + 3 ^ 40 * 106667 * 2
def baseEnd_106667 : Nat := 54771440973239398571953

theorem tailTrace_106667 : CollatzResearch.WordTrace tailWord_106667 prefixEnd_106667 54771440973239398571953 := by
  unfold tailWord_106667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890465104571151118358255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2593643403047434078905503 3890465104571151118358255)
  ·
    refine ⟨5835697656856726677537383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3890465104571151118358255 5835697656856726677537383)
    ·
      refine ⟨8753546485285090016306075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5835697656856726677537383 8753546485285090016306075)
      ·
        refine ⟨13130319727927635024459113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8753546485285090016306075 13130319727927635024459113)
        ·
          refine ⟨9847739795945726268344335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13130319727927635024459113 9847739795945726268344335)
          ·
            refine ⟨14771609693918589402516503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847739795945726268344335 14771609693918589402516503)
            ·
              refine ⟨22157414540877884103774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14771609693918589402516503 22157414540877884103774755)
              ·
                refine ⟨33236121811316826155662133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22157414540877884103774755 33236121811316826155662133)
                ·
                  refine ⟨3115886419810952452093325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33236121811316826155662133 3115886419810952452093325)
                  ·
                    refine ⟨1168457407429107169534997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115886419810952452093325 1168457407429107169534997)
                    ·
                      refine ⟨54771440973239398571953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1168457407429107169534997 54771440973239398571953)
                      ·
                        rfl

theorem cell23_106667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_106667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106667 prefixEnd_106667 := by exact prefixLift 106667
  have htrace : WordTrace (prefixWord ++ tailWord_106667) baseStart_106667 baseEnd_106667 := by
    simpa [prefixWord, tailWord_106667, baseEnd_106667] using wordTrace_append hprefix tailTrace_106667
  have hstable : (prefixWord ++ tailWord_106667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106667).length < 2 ^ (prefixWord ++ tailWord_106667).sum := by decide
  have hdescent : baseEnd_106667 < baseStart_106667 := by decide
  rcases family_descends (prefixWord ++ tailWord_106667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106698 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_106698 : Nat := 118140960795 + 106698 * 2 ^ 59
def prefixEnd_106698 : Nat := 4983230072969 + 3 ^ 40 * 106698 * 2
def baseEnd_106698 : Nat := 18262452957842925761437

theorem tailTrace_106698 : CollatzResearch.WordTrace tailWord_106698 prefixEnd_106698 18262452957842925761437 := by
  unfold tailWord_106698
  simp only [CollatzResearch.WordTrace]
  refine ⟨972898941864710853184187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2594397178305895608491165 972898941864710853184187)
  ·
    refine ⟨1459348412797066279776281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972898941864710853184187 1459348412797066279776281)
    ·
      refine ⟨1094511309597799709832211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459348412797066279776281 1094511309597799709832211)
      ·
        refine ⟨1641766964396699564748317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094511309597799709832211 1641766964396699564748317)
        ·
          refine ⟨615662611648762336780619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1641766964396699564748317 615662611648762336780619)
          ·
            refine ⟨923493917473143505170929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615662611648762336780619 923493917473143505170929)
            ·
              refine ⟨692620438104857628878197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923493917473143505170929 692620438104857628878197)
              ·
                refine ⟨64933166072330402707331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692620438104857628878197 64933166072330402707331)
                ·
                  refine ⟨97399749108495604060997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64933166072330402707331 97399749108495604060997)
                  ·
                    refine ⟨18262452957842925761437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97399749108495604060997 18262452957842925761437)
                    ·
                      rfl

theorem cell23_106698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_106698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106698 prefixEnd_106698 := by exact prefixLift 106698
  have htrace : WordTrace (prefixWord ++ tailWord_106698) baseStart_106698 baseEnd_106698 := by
    simpa [prefixWord, tailWord_106698, baseEnd_106698] using wordTrace_append hprefix tailTrace_106698
  have hstable : (prefixWord ++ tailWord_106698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106698).length < 2 ^ (prefixWord ++ tailWord_106698).sum := by decide
  have hdescent : baseEnd_106698 < baseStart_106698 := by decide
  rcases family_descends (prefixWord ++ tailWord_106698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106731 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 5, 2]
def baseStart_106731 : Nat := 118140960795 + 106731 * 2 ^ 59
def prefixEnd_106731 : Nat := 4983230072969 + 3 ^ 40 * 106731 * 2
def baseEnd_106731 : Nat := 54804303735127148171659

theorem tailTrace_106731 : CollatzResearch.WordTrace tailWord_106731 prefixEnd_106731 54804303735127148171659 := by
  unfold tailWord_106731
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892799376339290048688047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2595199584226193365792031 3892799376339290048688047)
  ·
    refine ⟨5839199064508935073032071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3892799376339290048688047 5839199064508935073032071)
    ·
      refine ⟨8758798596763402609548107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839199064508935073032071 8758798596763402609548107)
      ·
        refine ⟨13138197895145103914322161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8758798596763402609548107 13138197895145103914322161)
        ·
          refine ⟨9853648421358827935741621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13138197895145103914322161 9853648421358827935741621)
          ·
            refine ⟨923779539502390118975777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9853648421358827935741621 923779539502390118975777)
            ·
              refine ⟨692834654626792589231833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923779539502390118975777 692834654626792589231833)
              ·
                refine ⟨519625990970094441923875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692834654626792589231833 519625990970094441923875)
                ·
                  refine ⟨779438986455141662885813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519625990970094441923875 779438986455141662885813)
                  ·
                    refine ⟨73072404980169530895545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 779438986455141662885813 73072404980169530895545)
                    ·
                      refine ⟨54804303735127148171659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73072404980169530895545 54804303735127148171659)
                      ·
                        rfl

theorem cell23_106731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5, 2].length) (baseStart_106731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106731 prefixEnd_106731 := by exact prefixLift 106731
  have htrace : WordTrace (prefixWord ++ tailWord_106731) baseStart_106731 baseEnd_106731 := by
    simpa [prefixWord, tailWord_106731, baseEnd_106731] using wordTrace_append hprefix tailTrace_106731
  have hstable : (prefixWord ++ tailWord_106731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106731).length < 2 ^ (prefixWord ++ tailWord_106731).sum := by decide
  have hdescent : baseEnd_106731 < baseStart_106731 := by decide
  rcases family_descends (prefixWord ++ tailWord_106731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106734 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_106734 : Nat := 118140960795 + 106734 * 2 ^ 59
def prefixEnd_106734 : Nat := 4983230072969 + 3 ^ 40 * 106734 * 2
def baseEnd_106734 : Nat := 54805844177090636434145

theorem tailTrace_106734 : CollatzResearch.WordTrace tailWord_106734 prefixEnd_106734 54805844177090636434145 := by
  unfold tailWord_106734
  simp only [CollatzResearch.WordTrace]
  refine ⟨486613599416052695130907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2595272530218947707364837 486613599416052695130907)
  ·
    refine ⟨729920399124079042696361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 486613599416052695130907 729920399124079042696361)
    ·
      refine ⟨547440299343059282022271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 729920399124079042696361 547440299343059282022271)
      ·
        refine ⟨821160449014588923033407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547440299343059282022271 821160449014588923033407)
        ·
          refine ⟨1231740673521883384550111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821160449014588923033407 1231740673521883384550111)
          ·
            refine ⟨1847611010282825076825167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231740673521883384550111 1847611010282825076825167)
            ·
              refine ⟨2771416515424237615237751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847611010282825076825167 2771416515424237615237751)
              ·
                refine ⟨4157124773136356422856627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771416515424237615237751 4157124773136356422856627)
                ·
                  refine ⟨6235687159704534634284941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157124773136356422856627 6235687159704534634284941)
                  ·
                    refine ⟨2338382684889200487856853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6235687159704534634284941 2338382684889200487856853)
                    ·
                      refine ⟨54805844177090636434145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2338382684889200487856853 54805844177090636434145)
                      ·
                        rfl

theorem cell23_106734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_106734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106734 prefixEnd_106734 := by exact prefixLift 106734
  have htrace : WordTrace (prefixWord ++ tailWord_106734) baseStart_106734 baseEnd_106734 := by
    simpa [prefixWord, tailWord_106734, baseEnd_106734] using wordTrace_append hprefix tailTrace_106734
  have hstable : (prefixWord ++ tailWord_106734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106734).length < 2 ^ (prefixWord ++ tailWord_106734).sum := by decide
  have hdescent : baseEnd_106734 < baseStart_106734 := by decide
  rcases family_descends (prefixWord ++ tailWord_106734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106738 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_106738 : Nat := 118140960795 + 106738 * 2 ^ 59
def prefixEnd_106738 : Nat := 4983230072969 + 3 ^ 40 * 106738 * 2
def baseEnd_106738 : Nat := 54807898099708620784127

theorem tailTrace_106738 : CollatzResearch.WordTrace tailWord_106738 prefixEnd_106738 54807898099708620784127 := by
  unfold tailWord_106738
  simp only [CollatzResearch.WordTrace]
  refine ⟨973263671828482561048217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2595369791542620162795245 973263671828482561048217)
  ·
    refine ⟨729947753871361920786163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 973263671828482561048217 729947753871361920786163)
    ·
      refine ⟨1094921630807042881179245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729947753871361920786163 1094921630807042881179245)
      ·
        refine ⟨410595611552641080442217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1094921630807042881179245 410595611552641080442217)
        ·
          refine ⟨307946708664480810331663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410595611552641080442217 307946708664480810331663)
          ·
            refine ⟨461920062996721215497495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307946708664480810331663 461920062996721215497495)
            ·
              refine ⟨692880094495081823246243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461920062996721215497495 692880094495081823246243)
              ·
                refine ⟨1039320141742622734869365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692880094495081823246243 1039320141742622734869365)
                ·
                  refine ⟨97436263288370881394003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1039320141742622734869365 97436263288370881394003)
                  ·
                    refine ⟨146154394932556322091005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97436263288370881394003 146154394932556322091005)
                    ·
                      refine ⟨54807898099708620784127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 146154394932556322091005 54807898099708620784127)
                      ·
                        rfl

theorem cell23_106738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_106738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106738 prefixEnd_106738 := by exact prefixLift 106738
  have htrace : WordTrace (prefixWord ++ tailWord_106738) baseStart_106738 baseEnd_106738 := by
    simpa [prefixWord, tailWord_106738, baseEnd_106738] using wordTrace_append hprefix tailTrace_106738
  have hstable : (prefixWord ++ tailWord_106738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106738).length < 2 ^ (prefixWord ++ tailWord_106738).sum := by decide
  have hdescent : baseEnd_106738 < baseStart_106738 := by decide
  rcases family_descends (prefixWord ++ tailWord_106738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106748 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_106748 : Nat := 118140960795 + 106748 * 2 ^ 59
def prefixEnd_106748 : Nat := 4983230072969 + 3 ^ 40 * 106748 * 2
def baseEnd_106748 : Nat := 54813032906253581659081

theorem tailTrace_106748 : CollatzResearch.WordTrace tailWord_106748 prefixEnd_106748 54813032906253581659081 := by
  unfold tailWord_106748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946709708638850976028449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2595612944851801301371265 1946709708638850976028449)
  ·
    refine ⟨1460032281479138232021337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946709708638850976028449 1460032281479138232021337)
    ·
      refine ⟨1095024211109353674016003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460032281479138232021337 1095024211109353674016003)
      ·
        refine ⟨1642536316664030511024005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095024211109353674016003 1642536316664030511024005)
        ·
          refine ⟨307975559374505720817001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1642536316664030511024005 307975559374505720817001)
          ·
            refine ⟨230981669530879290612751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307975559374505720817001 230981669530879290612751)
            ·
              refine ⟨346472504296318935919127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230981669530879290612751 346472504296318935919127)
              ·
                refine ⟨519708756444478403878691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346472504296318935919127 519708756444478403878691)
                ·
                  refine ⟨779563134666717605818037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519708756444478403878691 779563134666717605818037)
                  ·
                    refine ⟨73084043875004775545441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 779563134666717605818037 73084043875004775545441)
                    ·
                      refine ⟨54813032906253581659081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73084043875004775545441 54813032906253581659081)
                      ·
                        rfl

theorem cell23_106748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_106748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106748 prefixEnd_106748 := by exact prefixLift 106748
  have htrace : WordTrace (prefixWord ++ tailWord_106748) baseStart_106748 baseEnd_106748 := by
    simpa [prefixWord, tailWord_106748, baseEnd_106748] using wordTrace_append hprefix tailTrace_106748
  have hstable : (prefixWord ++ tailWord_106748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106748).length < 2 ^ (prefixWord ++ tailWord_106748).sum := by decide
  have hdescent : baseEnd_106748 < baseStart_106748 := by decide
  rcases family_descends (prefixWord ++ tailWord_106748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106755 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 1, 1, 3]
def baseStart_106755 : Nat := 118140960795 + 106755 * 2 ^ 59
def prefixEnd_106755 : Nat := 4983230072969 + 3 ^ 40 * 106755 * 2
def baseEnd_106755 : Nat := 54816627270835054271549

theorem tailTrace_106755 : CollatzResearch.WordTrace tailWord_106755 prefixEnd_106755 54816627270835054271549 := by
  unfold tailWord_106755
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893674728252342147561719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2595783152168228098374479 3893674728252342147561719)
  ·
    refine ⟨5840512092378513221342579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893674728252342147561719 5840512092378513221342579)
    ·
      refine ⟨8760768138567769832013869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840512092378513221342579 8760768138567769832013869)
      ·
        refine ⟨3285288051962913687005201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8760768138567769832013869 3285288051962913687005201)
        ·
          refine ⟨2463966038972185265253901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3285288051962913687005201 2463966038972185265253901)
          ·
            refine ⟨923987264614569474470213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2463966038972185265253901 923987264614569474470213)
            ·
              refine ⟨173247612115231776463165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 923987264614569474470213 173247612115231776463165)
              ·
                refine ⟨64967854543211916173687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173247612115231776463165 64967854543211916173687)
                ·
                  refine ⟨97451781814817874260531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64967854543211916173687 97451781814817874260531)
                  ·
                    refine ⟨146177672722226811390797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97451781814817874260531 146177672722226811390797)
                    ·
                      refine ⟨54816627270835054271549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 146177672722226811390797 54816627270835054271549)
                      ·
                        rfl

theorem cell23_106755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_106755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106755 prefixEnd_106755 := by exact prefixLift 106755
  have htrace : WordTrace (prefixWord ++ tailWord_106755) baseStart_106755 baseEnd_106755 := by
    simpa [prefixWord, tailWord_106755, baseEnd_106755] using wordTrace_append hprefix tailTrace_106755
  have hstable : (prefixWord ++ tailWord_106755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106755).length < 2 ^ (prefixWord ++ tailWord_106755).sum := by decide
  have hdescent : baseEnd_106755 < baseStart_106755 := by decide
  rcases family_descends (prefixWord ++ tailWord_106755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106788 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_106788 : Nat := 118140960795 + 106788 * 2 ^ 59
def prefixEnd_106788 : Nat := 4983230072969 + 3 ^ 40 * 106788 * 2
def baseEnd_106788 : Nat := 18277857377477808386299

theorem tailTrace_106788 : CollatzResearch.WordTrace tailWord_106788 prefixEnd_106788 18277857377477808386299 := by
  unfold tailWord_106788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947439168566394391756509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2596585558088525855675345 1947439168566394391756509)
  ·
    refine ⟨730289688212397896908691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1947439168566394391756509 730289688212397896908691)
    ·
      refine ⟨1095434532318596845363037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730289688212397896908691 1095434532318596845363037)
      ·
        refine ⟨410787949619473817011139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1095434532318596845363037 410787949619473817011139)
        ·
          refine ⟨616181924429210725516709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410787949619473817011139 616181924429210725516709)
          ·
            refine ⟨115534110830477011034383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 616181924429210725516709 115534110830477011034383)
            ·
              refine ⟨173301166245715516551575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115534110830477011034383 173301166245715516551575)
              ·
                refine ⟨259951749368573274827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173301166245715516551575 259951749368573274827363)
                ·
                  refine ⟨389927624052859912241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259951749368573274827363 389927624052859912241045)
                  ·
                    refine ⟨18277857377477808386299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 389927624052859912241045 18277857377477808386299)
                    ·
                      rfl

theorem cell23_106788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_106788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106788 prefixEnd_106788 := by exact prefixLift 106788
  have htrace : WordTrace (prefixWord ++ tailWord_106788) baseStart_106788 baseEnd_106788 := by
    simpa [prefixWord, tailWord_106788, baseEnd_106788] using wordTrace_append hprefix tailTrace_106788
  have hstable : (prefixWord ++ tailWord_106788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106788).length < 2 ^ (prefixWord ++ tailWord_106788).sum := by decide
  have hdescent : baseEnd_106788 < baseStart_106788 := by decide
  rcases family_descends (prefixWord ++ tailWord_106788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106801 : List Nat := [1, 2, 2, 3, 4, 1, 1, 9]
def baseStart_106801 : Nat := 118140960795 + 106801 * 2 ^ 59
def prefixEnd_106801 : Nat := 4983230072969 + 3 ^ 40 * 106801 * 2
def baseEnd_106801 : Nat := 2031120273368217566531

theorem tailTrace_106801 : CollatzResearch.WordTrace tailWord_106801 prefixEnd_106801 2031120273368217566531 := by
  unfold tailWord_106801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895352486085692003736257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2596901657390461335824171 3895352486085692003736257)
  ·
    refine ⟨2921514364564269002802193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3895352486085692003736257 2921514364564269002802193)
    ·
      refine ⟨2191135773423201752101645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2921514364564269002802193 2191135773423201752101645)
      ·
        refine ⟨821675915033700657038117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2191135773423201752101645 821675915033700657038117)
        ·
          refine ⟨154064234068818873194647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 821675915033700657038117 154064234068818873194647)
          ·
            refine ⟨231096351103228309791971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154064234068818873194647 231096351103228309791971)
            ·
              refine ⟨346644526654842464687957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231096351103228309791971 346644526654842464687957)
              ·
                refine ⟨2031120273368217566531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 346644526654842464687957 2031120273368217566531)
                ·
                  rfl

theorem cell23_106801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 9].length) (baseStart_106801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106801 prefixEnd_106801 := by exact prefixLift 106801
  have htrace : WordTrace (prefixWord ++ tailWord_106801) baseStart_106801 baseEnd_106801 := by
    simpa [prefixWord, tailWord_106801, baseEnd_106801] using wordTrace_append hprefix tailTrace_106801
  have hstable : (prefixWord ++ tailWord_106801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106801).length < 2 ^ (prefixWord ++ tailWord_106801).sum := by decide
  have hdescent : baseEnd_106801 < baseStart_106801 := by decide
  rcases family_descends (prefixWord ++ tailWord_106801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106828 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_106828 : Nat := 118140960795 + 106828 * 2 ^ 59
def prefixEnd_106828 : Nat := 4983230072969 + 3 ^ 40 * 106828 * 2
def baseEnd_106828 : Nat := 54854111358613268658713

theorem tailTrace_106828 : CollatzResearch.WordTrace tailWord_106828 prefixEnd_106828 54854111358613268658713 := by
  unfold tailWord_106828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948168628493937807484569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2597558171325250409979425 1948168628493937807484569)
  ·
    refine ⟨1461126471370453355613427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1948168628493937807484569 1461126471370453355613427)
    ·
      refine ⟨2191689707055680033420141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461126471370453355613427 2191689707055680033420141)
      ·
        refine ⟨821883640145880012532553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2191689707055680033420141 821883640145880012532553)
        ·
          refine ⟨616412730109410009399415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821883640145880012532553 616412730109410009399415)
          ·
            refine ⟨924619095164115014099123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616412730109410009399415 924619095164115014099123)
            ·
              refine ⟨1386928642746172521148685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924619095164115014099123 1386928642746172521148685)
              ·
                refine ⟨520098241029814695430757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386928642746172521148685 520098241029814695430757)
                ·
                  refine ⟨97518420193090255393267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520098241029814695430757 97518420193090255393267)
                  ·
                    refine ⟨146277630289635383089901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97518420193090255393267 146277630289635383089901)
                    ·
                      refine ⟨54854111358613268658713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 146277630289635383089901 54854111358613268658713)
                      ·
                        rfl

theorem cell23_106828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_106828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106828 prefixEnd_106828 := by exact prefixLift 106828
  have htrace : WordTrace (prefixWord ++ tailWord_106828) baseStart_106828 baseEnd_106828 := by
    simpa [prefixWord, tailWord_106828, baseEnd_106828] using wordTrace_append hprefix tailTrace_106828
  have hstable : (prefixWord ++ tailWord_106828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106828).length < 2 ^ (prefixWord ++ tailWord_106828).sum := by decide
  have hdescent : baseEnd_106828 < baseStart_106828 := by decide
  rcases family_descends (prefixWord ++ tailWord_106828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106855 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_106855 : Nat := 118140960795 + 106855 * 2 ^ 59
def prefixEnd_106855 : Nat := 4983230072969 + 3 ^ 40 * 106855 * 2
def baseEnd_106855 : Nat := 54867975336284663021089

theorem tailTrace_106855 : CollatzResearch.WordTrace tailWord_106855 prefixEnd_106855 54867975336284663021089 := by
  unfold tailWord_106855
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897322027890059226202019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2598214685260039484134679 3897322027890059226202019)
  ·
    refine ⟨5845983041835088839303029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3897322027890059226202019 5845983041835088839303029)
    ·
      refine ⟨548060910172039578684659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5845983041835088839303029 548060910172039578684659)
      ·
        refine ⟨822091365258059368026989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548060910172039578684659 822091365258059368026989)
        ·
          refine ⟨308284261971772263010121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822091365258059368026989 308284261971772263010121)
          ·
            refine ⟨231213196478829197257591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308284261971772263010121 231213196478829197257591)
            ·
              refine ⟨346819794718243795886387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231213196478829197257591 346819794718243795886387)
              ·
                refine ⟨520229692077365693829581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346819794718243795886387 520229692077365693829581)
                ·
                  refine ⟨195086134529012135186093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520229692077365693829581 195086134529012135186093)
                  ·
                    refine ⟨73157300448379550694785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195086134529012135186093 73157300448379550694785)
                    ·
                      refine ⟨54867975336284663021089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73157300448379550694785 54867975336284663021089)
                      ·
                        rfl

theorem cell23_106855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_106855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106855 prefixEnd_106855 := by exact prefixLift 106855
  have htrace : WordTrace (prefixWord ++ tailWord_106855) baseStart_106855 baseEnd_106855 := by
    simpa [prefixWord, tailWord_106855, baseEnd_106855] using wordTrace_append hprefix tailTrace_106855
  have hstable : (prefixWord ++ tailWord_106855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106855).length < 2 ^ (prefixWord ++ tailWord_106855).sum := by decide
  have hdescent : baseEnd_106855 < baseStart_106855 := by decide
  rcases family_descends (prefixWord ++ tailWord_106855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106985 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 1, 4]
def baseStart_106985 : Nat := 118140960795 + 106985 * 2 ^ 59
def prefixEnd_106985 : Nat := 4983230072969 + 3 ^ 40 * 106985 * 2
def baseEnd_106985 : Nat := 18311575940456384798497

theorem tailTrace_106985 : CollatzResearch.WordTrace tailWord_106985 prefixEnd_106985 18311575940456384798497 := by
  unfold tailWord_106985
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902063517419091428434409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2601375678279394285622939 3902063517419091428434409)
  ·
    refine ⟨2926547638064318571325807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3902063517419091428434409 2926547638064318571325807)
    ·
      refine ⟨4389821457096477856988711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926547638064318571325807 4389821457096477856988711)
      ·
        refine ⟨6584732185644716785483067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389821457096477856988711 6584732185644716785483067)
        ·
          refine ⟨9877098278467075178224601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584732185644716785483067 9877098278467075178224601)
          ·
            refine ⟨7407823708850306383668451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9877098278467075178224601 7407823708850306383668451)
            ·
              refine ⟨11111735563275459575502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407823708850306383668451 11111735563275459575502677)
              ·
                refine ⟨65107825566067145950211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11111735563275459575502677 65107825566067145950211)
                ·
                  refine ⟨97661738349100718925317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65107825566067145950211 97661738349100718925317)
                  ·
                    refine ⟨18311575940456384798497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97661738349100718925317 18311575940456384798497)
                    ·
                      rfl

theorem cell23_106985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 4].length) (baseStart_106985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106985 prefixEnd_106985 := by exact prefixLift 106985
  have htrace : WordTrace (prefixWord ++ tailWord_106985) baseStart_106985 baseEnd_106985 := by
    simpa [prefixWord, tailWord_106985, baseEnd_106985] using wordTrace_append hprefix tailTrace_106985
  have hstable : (prefixWord ++ tailWord_106985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106985).length < 2 ^ (prefixWord ++ tailWord_106985).sum := by decide
  have hdescent : baseEnd_106985 < baseStart_106985 := by decide
  rcases family_descends (prefixWord ++ tailWord_106985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106998 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_106998 : Nat := 118140960795 + 106998 * 2 ^ 59
def prefixEnd_106998 : Nat := 4983230072969 + 3 ^ 40 * 106998 * 2
def baseEnd_106998 : Nat := 6104600341097511503659

theorem tailTrace_106998 : CollatzResearch.WordTrace tailWord_106998 prefixEnd_106998 6104600341097511503659 := by
  unfold tailWord_106998
  simp only [CollatzResearch.WordTrace]
  refine ⟨243908604148249665541103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2601691777581329765771765 243908604148249665541103)
  ·
    refine ⟨365862906222374498311655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243908604148249665541103 365862906222374498311655)
    ·
      refine ⟨548794359333561747467483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365862906222374498311655 548794359333561747467483)
      ·
        refine ⟨823191539000342621201225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548794359333561747467483 823191539000342621201225)
        ·
          refine ⟨617393654250256965900919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823191539000342621201225 617393654250256965900919)
          ·
            refine ⟨926090481375385448851379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617393654250256965900919 926090481375385448851379)
            ·
              refine ⟨1389135722063078173277069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926090481375385448851379 1389135722063078173277069)
              ·
                refine ⟨520925895773654314978901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389135722063078173277069 520925895773654314978901)
                ·
                  refine ⟨6104600341097511503659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 520925895773654314978901 6104600341097511503659)
                  ·
                    rfl

theorem cell23_106998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_106998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_106998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_106998 prefixEnd_106998 := by exact prefixLift 106998
  have htrace : WordTrace (prefixWord ++ tailWord_106998) baseStart_106998 baseEnd_106998 := by
    simpa [prefixWord, tailWord_106998, baseEnd_106998] using wordTrace_append hprefix tailTrace_106998
  have hstable : (prefixWord ++ tailWord_106998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106998).length < 2 ^ (prefixWord ++ tailWord_106998).sum := by decide
  have hdescent : baseEnd_106998 < baseStart_106998 := by decide
  rcases family_descends (prefixWord ++ tailWord_106998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107001 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_107001 : Nat := 118140960795 + 107001 * 2 ^ 59
def prefixEnd_107001 : Nat := 4983230072969 + 3 ^ 40 * 107001 * 2
def baseEnd_107001 : Nat := 54942943511841091795417

theorem tailTrace_107001 : CollatzResearch.WordTrace tailWord_107001 prefixEnd_107001 54942943511841091795417 := by
  unfold tailWord_107001
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902647085361126161016857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2601764723574084107344571 3902647085361126161016857)
  ·
    refine ⟨2926985314020844620762643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3902647085361126161016857 2926985314020844620762643)
    ·
      refine ⟨4390477971031266931143965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926985314020844620762643 4390477971031266931143965)
      ·
        refine ⟨1646429239136725099178987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4390477971031266931143965 1646429239136725099178987)
        ·
          refine ⟨2469643858705087648768481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646429239136725099178987 2469643858705087648768481)
          ·
            refine ⟨1852232894028815736576361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469643858705087648768481 1852232894028815736576361)
            ·
              refine ⟨1389174670521611802432271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852232894028815736576361 1389174670521611802432271)
              ·
                refine ⟨2083762005782417703648407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389174670521611802432271 2083762005782417703648407)
                ·
                  refine ⟨3125643008673626555472611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083762005782417703648407 3125643008673626555472611)
                  ·
                    refine ⟨4688464513010439833208917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125643008673626555472611 4688464513010439833208917)
                    ·
                      refine ⟨54942943511841091795417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4688464513010439833208917 54942943511841091795417)
                      ·
                        rfl

theorem cell23_107001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_107001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107001 prefixEnd_107001 := by exact prefixLift 107001
  have htrace : WordTrace (prefixWord ++ tailWord_107001) baseStart_107001 baseEnd_107001 := by
    simpa [prefixWord, tailWord_107001, baseEnd_107001] using wordTrace_append hprefix tailTrace_107001
  have hstable : (prefixWord ++ tailWord_107001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107001).length < 2 ^ (prefixWord ++ tailWord_107001).sum := by decide
  have hdescent : baseEnd_107001 < baseStart_107001 := by decide
  rcases family_descends (prefixWord ++ tailWord_107001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107015 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 6]
def baseStart_107015 : Nat := 118140960795 + 107015 * 2 ^ 59
def prefixEnd_107015 : Nat := 4983230072969 + 3 ^ 40 * 107015 * 2
def baseEnd_107015 : Nat := 6105570249000448557817

theorem tailTrace_107015 : CollatzResearch.WordTrace tailWord_107015 prefixEnd_107015 6105570249000448557817 := by
  unfold tailWord_107015
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903157707310406552026499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2602105138206937701350999 3903157707310406552026499)
  ·
    refine ⟨5854736560965609828039749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903157707310406552026499 5854736560965609828039749)
    ·
      refine ⟨1097763105181051842757453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5854736560965609828039749 1097763105181051842757453)
      ·
        refine ⟨411661164442894441034045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1097763105181051842757453 411661164442894441034045)
        ·
          refine ⟨154372936666085415387767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411661164442894441034045 154372936666085415387767)
          ·
            refine ⟨231559404999128123081651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154372936666085415387767 231559404999128123081651)
            ·
              refine ⟨347339107498692184622477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231559404999128123081651 347339107498692184622477)
              ·
                refine ⟨130252165312009569233429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347339107498692184622477 130252165312009569233429)
                ·
                  refine ⟨6105570249000448557817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130252165312009569233429 6105570249000448557817)
                  ·
                    rfl

theorem cell23_107015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 6].length) (baseStart_107015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107015 prefixEnd_107015 := by exact prefixLift 107015
  have htrace : WordTrace (prefixWord ++ tailWord_107015) baseStart_107015 baseEnd_107015 := by
    simpa [prefixWord, tailWord_107015, baseEnd_107015] using wordTrace_append hprefix tailTrace_107015
  have hstable : (prefixWord ++ tailWord_107015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107015).length < 2 ^ (prefixWord ++ tailWord_107015).sum := by decide
  have hdescent : baseEnd_107015 < baseStart_107015 := by decide
  rcases family_descends (prefixWord ++ tailWord_107015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107053 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_107053 : Nat := 118140960795 + 107053 * 2 ^ 59
def prefixEnd_107053 : Nat := 4983230072969 + 3 ^ 40 * 107053 * 2
def baseEnd_107053 : Nat := 18323214835291629448393

theorem tailTrace_107053 : CollatzResearch.WordTrace tailWord_107053 prefixEnd_107053 18323214835291629448393 := by
  unfold tailWord_107053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904543681172739041909813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2603029120781826027939875 3904543681172739041909813)
  ·
    refine ⟨366050970109944285179045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3904543681172739041909813 366050970109944285179045)
    ·
      refine ⟨68634556895614553471071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366050970109944285179045 68634556895614553471071)
      ·
        refine ⟨102951835343421830206607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68634556895614553471071 102951835343421830206607)
        ·
          refine ⟨154427753015132745309911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102951835343421830206607 154427753015132745309911)
          ·
            refine ⟨231641629522699117964867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154427753015132745309911 231641629522699117964867)
            ·
              refine ⟨347462444284048676947301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231641629522699117964867 347462444284048676947301)
              ·
                refine ⟨65149208303259126927619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347462444284048676947301 65149208303259126927619)
                ·
                  refine ⟨97723812454888690391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65149208303259126927619 97723812454888690391429)
                  ·
                    refine ⟨18323214835291629448393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97723812454888690391429 18323214835291629448393)
                    ·
                      rfl

theorem cell23_107053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_107053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107053 prefixEnd_107053 := by exact prefixLift 107053
  have htrace : WordTrace (prefixWord ++ tailWord_107053) baseStart_107053 baseEnd_107053 := by
    simpa [prefixWord, tailWord_107053, baseEnd_107053] using wordTrace_append hprefix tailTrace_107053
  have hstable : (prefixWord ++ tailWord_107053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107053).length < 2 ^ (prefixWord ++ tailWord_107053).sum := by decide
  have hdescent : baseEnd_107053 < baseStart_107053 := by decide
  rcases family_descends (prefixWord ++ tailWord_107053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107082 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_107082 : Nat := 118140960795 + 107082 * 2 ^ 59
def prefixEnd_107082 : Nat := 4983230072969 + 3 ^ 40 * 107082 * 2
def baseEnd_107082 : Nat := 54984535444855274882545

theorem tailTrace_107082 : CollatzResearch.WordTrace tailWord_107082 prefixEnd_107082 54984535444855274882545 := by
  unfold tailWord_107082
  simp only [CollatzResearch.WordTrace]
  refine ⟨976400349516919248678875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2603734265378451329810333 976400349516919248678875)
  ·
    refine ⟨1464600524275378873018313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976400349516919248678875 1464600524275378873018313)
    ·
      refine ⟨1098450393206534154763735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464600524275378873018313 1098450393206534154763735)
      ·
        refine ⟨1647675589809801232145603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098450393206534154763735 1647675589809801232145603)
        ·
          refine ⟨2471513384714701848218405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647675589809801232145603 2471513384714701848218405)
          ·
            refine ⟨463408759634006596540951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2471513384714701848218405 463408759634006596540951)
            ·
              refine ⟨695113139451009894811427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463408759634006596540951 695113139451009894811427)
              ·
                refine ⟨1042669709176514842217141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695113139451009894811427 1042669709176514842217141)
                ·
                  refine ⟨97750285235298266457857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1042669709176514842217141 97750285235298266457857)
                  ·
                    refine ⟨73312713926473699843393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97750285235298266457857 73312713926473699843393)
                    ·
                      refine ⟨54984535444855274882545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73312713926473699843393 54984535444855274882545)
                      ·
                        rfl

theorem cell23_107082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_107082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107082 prefixEnd_107082 := by exact prefixLift 107082
  have htrace : WordTrace (prefixWord ++ tailWord_107082) baseStart_107082 baseEnd_107082 := by
    simpa [prefixWord, tailWord_107082, baseEnd_107082] using wordTrace_append hprefix tailTrace_107082
  have hstable : (prefixWord ++ tailWord_107082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107082).length < 2 ^ (prefixWord ++ tailWord_107082).sum := by decide
  have hdescent : baseEnd_107082 < baseStart_107082 := by decide
  rcases family_descends (prefixWord ++ tailWord_107082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107109 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_107109 : Nat := 118140960795 + 107109 * 2 ^ 59
def prefixEnd_107109 : Nat := 4983230072969 + 3 ^ 40 * 107109 * 2
def baseEnd_107109 : Nat := 18332799807508889748307

theorem tailTrace_107109 : CollatzResearch.WordTrace tailWord_107109 prefixEnd_107109 18332799807508889748307 := by
  unfold tailWord_107109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906586168969860605948381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2604390779313240403965587 3906586168969860605948381)
  ·
    refine ⟨1464969813363697727230643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3906586168969860605948381 1464969813363697727230643)
    ·
      refine ⟨2197454720045546590845965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464969813363697727230643 2197454720045546590845965)
      ·
        refine ⟨824045520017079971567237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2197454720045546590845965 824045520017079971567237)
        ·
          refine ⟨154508535003202494668857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 824045520017079971567237 154508535003202494668857)
          ·
            refine ⟨115881401252401871001643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154508535003202494668857 115881401252401871001643)
            ·
              refine ⟨173822101878602806502465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115881401252401871001643 173822101878602806502465)
              ·
                refine ⟨130366576408952104876849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173822101878602806502465 130366576408952104876849)
                ·
                  refine ⟨97774932306714078657637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130366576408952104876849 97774932306714078657637)
                  ·
                    refine ⟨18332799807508889748307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97774932306714078657637 18332799807508889748307)
                    ·
                      rfl

theorem cell23_107109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_107109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107109 prefixEnd_107109 := by exact prefixLift 107109
  have htrace : WordTrace (prefixWord ++ tailWord_107109) baseStart_107109 baseEnd_107109 := by
    simpa [prefixWord, tailWord_107109, baseEnd_107109] using wordTrace_append hprefix tailTrace_107109
  have hstable : (prefixWord ++ tailWord_107109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107109).length < 2 ^ (prefixWord ++ tailWord_107109).sum := by decide
  have hdescent : baseEnd_107109 < baseStart_107109 := by decide
  rcases family_descends (prefixWord ++ tailWord_107109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107126 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_107126 : Nat := 118140960795 + 107126 * 2 ^ 59
def prefixEnd_107126 : Nat := 4983230072969 + 3 ^ 40 * 107126 * 2
def baseEnd_107126 : Nat := 18335709531217700910781

theorem tailTrace_107126 : CollatzResearch.WordTrace tailWord_107126 prefixEnd_107126 18335709531217700910781 := by
  unfold tailWord_107126
  simp only [CollatzResearch.WordTrace]
  refine ⟨244200388119267031832327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2604804139938848339544821 244200388119267031832327)
  ·
    refine ⟨366300582178900547748491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244200388119267031832327 366300582178900547748491)
    ·
      refine ⟨549450873268350821622737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366300582178900547748491 549450873268350821622737)
      ·
        refine ⟨412088154951263116217053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549450873268350821622737 412088154951263116217053)
        ·
          refine ⟨154533058106723668581395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412088154951263116217053 154533058106723668581395)
          ·
            refine ⟨231799587160085502872093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154533058106723668581395 231799587160085502872093)
            ·
              refine ⟨86924845185032063577035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231799587160085502872093 86924845185032063577035)
              ·
                refine ⟨130387267777548095365553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86924845185032063577035 130387267777548095365553)
                ·
                  refine ⟨97790450833161071524165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130387267777548095365553 97790450833161071524165)
                  ·
                    refine ⟨18335709531217700910781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97790450833161071524165 18335709531217700910781)
                    ·
                      rfl

theorem cell23_107126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_107126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107126 prefixEnd_107126 := by exact prefixLift 107126
  have htrace : WordTrace (prefixWord ++ tailWord_107126) baseStart_107126 baseEnd_107126 := by
    simpa [prefixWord, tailWord_107126, baseEnd_107126] using wordTrace_append hprefix tailTrace_107126
  have hstable : (prefixWord ++ tailWord_107126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107126).length < 2 ^ (prefixWord ++ tailWord_107126).sum := by decide
  have hdescent : baseEnd_107126 < baseStart_107126 := by decide
  rcases family_descends (prefixWord ++ tailWord_107126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107132 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_107132 : Nat := 118140960795 + 107132 * 2 ^ 59
def prefixEnd_107132 : Nat := 4983230072969 + 3 ^ 40 * 107132 * 2
def baseEnd_107132 : Nat := 55010209477580079257315

theorem tailTrace_107132 : CollatzResearch.WordTrace tailWord_107132 prefixEnd_107132 55010209477580079257315 := by
  unfold tailWord_107132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953712523943267767017825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2604950031924357022690433 1953712523943267767017825)
  ·
    refine ⟨1465284392957450825263369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1953712523943267767017825 1465284392957450825263369)
    ·
      refine ⟨1098963294718088118947527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1465284392957450825263369 1098963294718088118947527)
      ·
        refine ⟨1648444942077132178421291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098963294718088118947527 1648444942077132178421291)
        ·
          refine ⟨2472667413115698267631937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648444942077132178421291 2472667413115698267631937)
          ·
            refine ⟨1854500559836773700723953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472667413115698267631937 1854500559836773700723953)
            ·
              refine ⟨1390875419877580275542965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854500559836773700723953 1390875419877580275542965)
              ·
                refine ⟨130394570613523150832153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390875419877580275542965 130394570613523150832153)
                ·
                  refine ⟨97795927960142363124115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130394570613523150832153 97795927960142363124115)
                  ·
                    refine ⟨146693891940213544686173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97795927960142363124115 146693891940213544686173)
                    ·
                      refine ⟨55010209477580079257315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 146693891940213544686173 55010209477580079257315)
                      ·
                        rfl

theorem cell23_107132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_107132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107132 prefixEnd_107132 := by exact prefixLift 107132
  have htrace : WordTrace (prefixWord ++ tailWord_107132) baseStart_107132 baseEnd_107132 := by
    simpa [prefixWord, tailWord_107132, baseEnd_107132] using wordTrace_append hprefix tailTrace_107132
  have hstable : (prefixWord ++ tailWord_107132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107132).length < 2 ^ (prefixWord ++ tailWord_107132).sum := by decide
  have hdescent : baseEnd_107132 < baseStart_107132 := by decide
  rcases family_descends (prefixWord ++ tailWord_107132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107148 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_107148 : Nat := 118140960795 + 107148 * 2 ^ 59
def prefixEnd_107148 : Nat := 4983230072969 + 3 ^ 40 * 107148 * 2
def baseEnd_107148 : Nat := 18339475056017338885747

theorem tailTrace_107148 : CollatzResearch.WordTrace tailWord_107148 prefixEnd_107148 18339475056017338885747 := by
  unfold tailWord_107148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954004307914285133309049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2605339077219046844412065 1954004307914285133309049)
  ·
    refine ⟨1465503230935713849981787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954004307914285133309049 1465503230935713849981787)
    ·
      refine ⟨2198254846403570774972681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465503230935713849981787 2198254846403570774972681)
      ·
        refine ⟨1648691134802678081229511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198254846403570774972681 1648691134802678081229511)
        ·
          refine ⟨2473036702204017121844267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648691134802678081229511 2473036702204017121844267)
          ·
            refine ⟨3709555053306025682766401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473036702204017121844267 3709555053306025682766401)
            ·
              refine ⟨2782166289979519262074801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709555053306025682766401 2782166289979519262074801)
              ·
                refine ⟨2086624717484639446556101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782166289979519262074801 2086624717484639446556101)
                ·
                  refine ⟨391242134528369896229269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086624717484639446556101 391242134528369896229269)
                  ·
                    refine ⟨18339475056017338885747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 391242134528369896229269 18339475056017338885747)
                    ·
                      rfl

theorem cell23_107148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_107148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107148 prefixEnd_107148 := by exact prefixLift 107148
  have htrace : WordTrace (prefixWord ++ tailWord_107148) baseStart_107148 baseEnd_107148 := by
    simpa [prefixWord, tailWord_107148, baseEnd_107148] using wordTrace_append hprefix tailTrace_107148
  have hstable : (prefixWord ++ tailWord_107148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107148).length < 2 ^ (prefixWord ++ tailWord_107148).sum := by decide
  have hdescent : baseEnd_107148 < baseStart_107148 := by decide
  rcases family_descends (prefixWord ++ tailWord_107148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107225 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_107225 : Nat := 118140960795 + 107225 * 2 ^ 59
def prefixEnd_107225 : Nat := 4983230072969 + 3 ^ 40 * 107225 * 2
def baseEnd_107225 : Nat := 18352654392816071798129

theorem tailTrace_107225 : CollatzResearch.WordTrace tailWord_107225 prefixEnd_107225 18352654392816071798129 := by
  unfold tailWord_107225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910817036549612417171129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2607211357699741611447419 3910817036549612417171129)
  ·
    refine ⟨2933112777412209312878347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3910817036549612417171129 2933112777412209312878347)
    ·
      refine ⟨4399669166118313969317521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933112777412209312878347 4399669166118313969317521)
      ·
        refine ⟨3299751874588735476988141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399669166118313969317521 3299751874588735476988141)
        ·
          refine ⟨1237406952970775803870553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3299751874588735476988141 1237406952970775803870553)
          ·
            refine ⟨928055214728081852902915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237406952970775803870553 928055214728081852902915)
            ·
              refine ⟨1392082822092122779354373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928055214728081852902915 1392082822092122779354373)
              ·
                refine ⟨261015529142273021128945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1392082822092122779354373 261015529142273021128945)
                ·
                  refine ⟨195761646856704765846709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261015529142273021128945 195761646856704765846709)
                  ·
                    refine ⟨18352654392816071798129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195761646856704765846709 18352654392816071798129)
                    ·
                      rfl

theorem cell23_107225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_107225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107225 prefixEnd_107225 := by exact prefixLift 107225
  have htrace : WordTrace (prefixWord ++ tailWord_107225) baseStart_107225 baseEnd_107225 := by
    simpa [prefixWord, tailWord_107225, baseEnd_107225] using wordTrace_append hprefix tailTrace_107225
  have hstable : (prefixWord ++ tailWord_107225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107225).length < 2 ^ (prefixWord ++ tailWord_107225).sum := by decide
  have hdescent : baseEnd_107225 < baseStart_107225 := by decide
  rcases family_descends (prefixWord ++ tailWord_107225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107285 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 8]
def baseStart_107285 : Nat := 118140960795 + 107285 * 2 ^ 59
def prefixEnd_107285 : Nat := 4983230072969 + 3 ^ 40 * 107285 * 2
def baseEnd_107285 : Nat := 6120974668635331182679

theorem tailTrace_107285 : CollatzResearch.WordTrace tailWord_107285 prefixEnd_107285 6120974668635331182679 := by
  unfold tailWord_107285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913005416332242664355309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2608670277554828442903539 3913005416332242664355309)
  ·
    refine ⟨1467377031124590999133241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3913005416332242664355309 1467377031124590999133241)
    ·
      refine ⟨1100532773343443249349931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1467377031124590999133241 1100532773343443249349931)
      ·
        refine ⟨1650799160015164874024897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100532773343443249349931 1650799160015164874024897)
        ·
          refine ⟨1238099370011373655518673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1650799160015164874024897 1238099370011373655518673)
          ·
            refine ⟨928574527508530241639005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238099370011373655518673 928574527508530241639005)
            ·
              refine ⟨348215447815698840614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928574527508530241639005 348215447815698840614627)
              ·
                refine ⟨522323171723548260921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348215447815698840614627 522323171723548260921941)
                ·
                  refine ⟨6120974668635331182679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 522323171723548260921941 6120974668635331182679)
                  ·
                    rfl

theorem cell23_107285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_107285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107285 prefixEnd_107285 := by exact prefixLift 107285
  have htrace : WordTrace (prefixWord ++ tailWord_107285) baseStart_107285 baseEnd_107285 := by
    simpa [prefixWord, tailWord_107285, baseEnd_107285] using wordTrace_append hprefix tailTrace_107285
  have hstable : (prefixWord ++ tailWord_107285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107285).length < 2 ^ (prefixWord ++ tailWord_107285).sum := by decide
  have hdescent : baseEnd_107285 < baseStart_107285 := by decide
  rcases family_descends (prefixWord ++ tailWord_107285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107355 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_107355 : Nat := 118140960795 + 107355 * 2 ^ 59
def prefixEnd_107355 : Nat := 4983230072969 + 3 ^ 40 * 107355 * 2
def baseEnd_107355 : Nat := 55124715663532706768789

theorem tailTrace_107355 : CollatzResearch.WordTrace tailWord_107355 prefixEnd_107355 55124715663532706768789 := by
  unfold tailWord_107355
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915558526078644619403519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2610372350719096412935679 3915558526078644619403519)
  ·
    refine ⟨5873337789117966929105279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915558526078644619403519 5873337789117966929105279)
    ·
      refine ⟨8810006683676950393657919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873337789117966929105279 8810006683676950393657919)
      ·
        refine ⟨13215010025515425590486879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810006683676950393657919 13215010025515425590486879)
        ·
          refine ⟨19822515038273138385730319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13215010025515425590486879 19822515038273138385730319)
          ·
            refine ⟨29733772557409707578595479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19822515038273138385730319 29733772557409707578595479)
            ·
              refine ⟨44600658836114561367893219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29733772557409707578595479 44600658836114561367893219)
              ·
                refine ⟨66900988254171842051839829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44600658836114561367893219 66900988254171842051839829)
                ·
                  refine ⟨391997978051788137022499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66900988254171842051839829 391997978051788137022499)
                  ·
                    refine ⟨587996967077682205533749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391997978051788137022499 587996967077682205533749)
                    ·
                      refine ⟨55124715663532706768789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 587996967077682205533749 55124715663532706768789)
                      ·
                        rfl

theorem cell23_107355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_107355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107355 prefixEnd_107355 := by exact prefixLift 107355
  have htrace : WordTrace (prefixWord ++ tailWord_107355) baseStart_107355 baseEnd_107355 := by
    simpa [prefixWord, tailWord_107355, baseEnd_107355] using wordTrace_append hprefix tailTrace_107355
  have hstable : (prefixWord ++ tailWord_107355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107355).length < 2 ^ (prefixWord ++ tailWord_107355).sum := by decide
  have hdescent : baseEnd_107355 < baseStart_107355 := by decide
  rcases family_descends (prefixWord ++ tailWord_107355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107389 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_107389 : Nat := 118140960795 + 107389 * 2 ^ 59
def prefixEnd_107389 : Nat := 4983230072969 + 3 ^ 40 * 107389 * 2
def baseEnd_107389 : Nat := 55142174005785573743633

theorem tailTrace_107389 : CollatzResearch.WordTrace tailWord_107389 prefixEnd_107389 55142174005785573743633 := by
  unfold tailWord_107389
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916798607955468426141221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2611199071970312284094147 3916798607955468426141221)
  ·
    refine ⟨734399738991650329901479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3916798607955468426141221 734399738991650329901479)
    ·
      refine ⟨1101599608487475494852219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734399738991650329901479 1101599608487475494852219)
      ·
        refine ⟨1652399412731213242278329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101599608487475494852219 1652399412731213242278329)
        ·
          refine ⟨1239299559548409931708747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652399412731213242278329 1239299559548409931708747)
          ·
            refine ⟨1858949339322614897563121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239299559548409931708747 1858949339322614897563121)
            ·
              refine ⟨1394212004491961173172341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858949339322614897563121 1394212004491961173172341)
              ·
                refine ⟨130707375421121359984907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1394212004491961173172341 130707375421121359984907)
                ·
                  refine ⟨196061063131682039977361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130707375421121359984907 196061063131682039977361)
                  ·
                    refine ⟨147045797348761529983021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196061063131682039977361 147045797348761529983021)
                    ·
                      refine ⟨55142174005785573743633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147045797348761529983021 55142174005785573743633)
                      ·
                        rfl

theorem cell23_107389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_107389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107389 prefixEnd_107389 := by exact prefixLift 107389
  have htrace : WordTrace (prefixWord ++ tailWord_107389) baseStart_107389 baseEnd_107389 := by
    simpa [prefixWord, tailWord_107389, baseEnd_107389] using wordTrace_append hprefix tailTrace_107389
  have hstable : (prefixWord ++ tailWord_107389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107389).length < 2 ^ (prefixWord ++ tailWord_107389).sum := by decide
  have hdescent : baseEnd_107389 < baseStart_107389 := by decide
  rcases family_descends (prefixWord ++ tailWord_107389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107437 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_107437 : Nat := 118140960795 + 107437 * 2 ^ 59
def prefixEnd_107437 : Nat := 4983230072969 + 3 ^ 40 * 107437 * 2
def baseEnd_107437 : Nat := 55166821077201385943413

theorem tailTrace_107437 : CollatzResearch.WordTrace tailWord_107437 prefixEnd_107437 55166821077201385943413 := by
  unfold tailWord_107437
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918549311781572623888565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2612366207854381749259043 3918549311781572623888565)
  ·
    refine ⟨367363997979522433489553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3918549311781572623888565 367363997979522433489553)
    ·
      refine ⟨275522998484641825117165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367363997979522433489553 275522998484641825117165)
      ·
        refine ⟨103321124431740684418937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275522998484641825117165 103321124431740684418937)
        ·
          refine ⟨77490843323805513314203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103321124431740684418937 77490843323805513314203)
          ·
            refine ⟨116236264985708269971305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77490843323805513314203 116236264985708269971305)
            ·
              refine ⟨87177198739281202478479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116236264985708269971305 87177198739281202478479)
              ·
                refine ⟨130765798108921803717719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87177198739281202478479 130765798108921803717719)
                ·
                  refine ⟨196148697163382705576579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130765798108921803717719 196148697163382705576579)
                  ·
                    refine ⟨294223045745074058364869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196148697163382705576579 294223045745074058364869)
                    ·
                      refine ⟨55166821077201385943413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 294223045745074058364869 55166821077201385943413)
                      ·
                        rfl

theorem cell23_107437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_107437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107437 prefixEnd_107437 := by exact prefixLift 107437
  have htrace : WordTrace (prefixWord ++ tailWord_107437) baseStart_107437 baseEnd_107437 := by
    simpa [prefixWord, tailWord_107437, baseEnd_107437] using wordTrace_append hprefix tailTrace_107437
  have hstable : (prefixWord ++ tailWord_107437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107437).length < 2 ^ (prefixWord ++ tailWord_107437).sum := by decide
  have hdescent : baseEnd_107437 < baseStart_107437 := by decide
  rcases family_descends (prefixWord ++ tailWord_107437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107566 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_107566 : Nat := 118140960795 + 107566 * 2 ^ 59
def prefixEnd_107566 : Nat := 4983230072969 + 3 ^ 40 * 107566 * 2
def baseEnd_107566 : Nat := 55233060081631381230319

theorem tailTrace_107566 : CollatzResearch.WordTrace tailWord_107566 prefixEnd_107566 55233060081631381230319 := by
  unfold tailWord_107566
  simp only [CollatzResearch.WordTrace]
  refine ⟨490406791039278456916819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2615502885542818436889701 490406791039278456916819)
  ·
    refine ⟨735610186558917685375229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 490406791039278456916819 735610186558917685375229)
    ·
      refine ⟨275853819959594132015711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 735610186558917685375229 275853819959594132015711)
      ·
        refine ⟨413780729939391198023567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275853819959594132015711 413780729939391198023567)
        ·
          refine ⟨620671094909086797035351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413780729939391198023567 620671094909086797035351)
          ·
            refine ⟨931006642363630195553027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620671094909086797035351 931006642363630195553027)
            ·
              refine ⟨1396509963545445293329541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931006642363630195553027 1396509963545445293329541)
              ·
                refine ⟨261845618164770992499289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1396509963545445293329541 261845618164770992499289)
                ·
                  refine ⟨196384213623578244374467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261845618164770992499289 196384213623578244374467)
                  ·
                    refine ⟨294576320435367366561701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196384213623578244374467 294576320435367366561701)
                    ·
                      refine ⟨55233060081631381230319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 294576320435367366561701 55233060081631381230319)
                      ·
                        rfl

theorem cell23_107566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_107566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107566 prefixEnd_107566 := by exact prefixLift 107566
  have htrace : WordTrace (prefixWord ++ tailWord_107566) baseStart_107566 baseEnd_107566 := by
    simpa [prefixWord, tailWord_107566, baseEnd_107566] using wordTrace_append hprefix tailTrace_107566
  have hstable : (prefixWord ++ tailWord_107566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107566).length < 2 ^ (prefixWord ++ tailWord_107566).sum := by decide
  have hdescent : baseEnd_107566 < baseStart_107566 := by decide
  rcases family_descends (prefixWord ++ tailWord_107566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107589 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 6]
def baseStart_107589 : Nat := 118140960795 + 107589 * 2 ^ 59
def prefixEnd_107589 : Nat := 4983230072969 + 3 ^ 40 * 107589 * 2
def baseEnd_107589 : Nat := 6138318904076087915857

theorem tailTrace_107589 : CollatzResearch.WordTrace tailWord_107589 prefixEnd_107589 6138318904076087915857 := by
  unfold tailWord_107589
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924093207230902583421821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2616062138153935055614547 3924093207230902583421821)
  ·
    refine ⟨1471534952711588468783183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3924093207230902583421821 1471534952711588468783183)
    ·
      refine ⟨2207302429067382703174775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471534952711588468783183 2207302429067382703174775)
      ·
        refine ⟨3310953643601074054762163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207302429067382703174775 3310953643601074054762163)
        ·
          refine ⟨4966430465401611082143245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310953643601074054762163 4966430465401611082143245)
          ·
            refine ⟨1862411424525604155803717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4966430465401611082143245 1862411424525604155803717)
            ·
              refine ⟨349202142098550779213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1862411424525604155803717 349202142098550779213197)
              ·
                refine ⟨130950803286956542204949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349202142098550779213197 130950803286956542204949)
                ·
                  refine ⟨6138318904076087915857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130950803286956542204949 6138318904076087915857)
                  ·
                    rfl

theorem cell23_107589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_107589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107589 prefixEnd_107589 := by exact prefixLift 107589
  have htrace : WordTrace (prefixWord ++ tailWord_107589) baseStart_107589 baseEnd_107589 := by
    simpa [prefixWord, tailWord_107589, baseEnd_107589] using wordTrace_append hprefix tailTrace_107589
  have hstable : (prefixWord ++ tailWord_107589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107589).length < 2 ^ (prefixWord ++ tailWord_107589).sum := by decide
  have hdescent : baseEnd_107589 < baseStart_107589 := by decide
  rcases family_descends (prefixWord ++ tailWord_107589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107616 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3]
def baseStart_107616 : Nat := 118140960795 + 107616 * 2 ^ 59
def prefixEnd_107616 : Nat := 4983230072969 + 3 ^ 40 * 107616 * 2
def baseEnd_107616 : Nat := 55258734114356185605089

theorem tailTrace_107616 : CollatzResearch.WordTrace tailWord_107616 prefixEnd_107616 55258734114356185605089 := by
  unfold tailWord_107616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962538989066543097327351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2616718652088724129769801 1962538989066543097327351)
  ·
    refine ⟨2943808483599814645991027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962538989066543097327351 2943808483599814645991027)
    ·
      refine ⟨4415712725399721968986541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943808483599814645991027 4415712725399721968986541)
      ·
        refine ⟨1655892272024895738369953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4415712725399721968986541 1655892272024895738369953)
        ·
          refine ⟨1241919204018671803777465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655892272024895738369953 1241919204018671803777465)
          ·
            refine ⟨931439403014003852833099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241919204018671803777465 931439403014003852833099)
            ·
              refine ⟨1397159104521005779249649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931439403014003852833099 1397159104521005779249649)
              ·
                refine ⟨1047869328390754334437237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397159104521005779249649 1047869328390754334437237)
                ·
                  refine ⟨98237749536633218853491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1047869328390754334437237 98237749536633218853491)
                  ·
                    refine ⟨147356624304949828280237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98237749536633218853491 147356624304949828280237)
                    ·
                      refine ⟨55258734114356185605089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147356624304949828280237 55258734114356185605089)
                      ·
                        rfl

theorem cell23_107616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_107616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107616 prefixEnd_107616 := by exact prefixLift 107616
  have htrace : WordTrace (prefixWord ++ tailWord_107616) baseStart_107616 baseEnd_107616 := by
    simpa [prefixWord, tailWord_107616, baseEnd_107616] using wordTrace_append hprefix tailTrace_107616
  have hstable : (prefixWord ++ tailWord_107616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107616).length < 2 ^ (prefixWord ++ tailWord_107616).sum := by decide
  have hdescent : baseEnd_107616 < baseStart_107616 := by decide
  rcases family_descends (prefixWord ++ tailWord_107616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107653 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_107653 : Nat := 118140960795 + 107653 * 2 ^ 59
def prefixEnd_107653 : Nat := 4983230072969 + 3 ^ 40 * 107653 * 2
def baseEnd_107653 : Nat := 18425910966190846947473

theorem tailTrace_107653 : CollatzResearch.WordTrace tailWord_107653 prefixEnd_107653 18425910966190846947473 := by
  unfold tailWord_107653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926427478999041513751613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2617618319332694342501075 3926427478999041513751613)
  ·
    refine ⟨1472410304624640567656855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3926427478999041513751613 1472410304624640567656855)
    ·
      refine ⟨2208615456936960851485283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472410304624640567656855 2208615456936960851485283)
      ·
        refine ⟨3312923185405441277227925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208615456936960851485283 3312923185405441277227925)
        ·
          refine ⟨155293274315880059870059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3312923185405441277227925 155293274315880059870059)
          ·
            refine ⟨232939911473820089805089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155293274315880059870059 232939911473820089805089)
            ·
              refine ⟨174704933605365067353817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232939911473820089805089 174704933605365067353817)
              ·
                refine ⟨131028700204023800515363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174704933605365067353817 131028700204023800515363)
                ·
                  refine ⟨196543050306035700773045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131028700204023800515363 196543050306035700773045)
                  ·
                    refine ⟨18425910966190846947473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196543050306035700773045 18425910966190846947473)
                    ·
                      rfl

theorem cell23_107653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_107653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107653 prefixEnd_107653 := by exact prefixLift 107653
  have htrace : WordTrace (prefixWord ++ tailWord_107653) baseStart_107653 baseEnd_107653 := by
    simpa [prefixWord, tailWord_107653, baseEnd_107653] using wordTrace_append hprefix tailTrace_107653
  have hstable : (prefixWord ++ tailWord_107653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107653).length < 2 ^ (prefixWord ++ tailWord_107653).sum := by decide
  have hdescent : baseEnd_107653 < baseStart_107653 := by decide
  rcases family_descends (prefixWord ++ tailWord_107653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107659 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3]
def baseStart_107659 : Nat := 118140960795 + 107659 * 2 ^ 59
def prefixEnd_107659 : Nat := 4983230072969 + 3 ^ 40 * 107659 * 2
def baseEnd_107659 : Nat := 55280813782499517367391

theorem tailTrace_107659 : CollatzResearch.WordTrace tailWord_107659 prefixEnd_107659 55280813782499517367391 := by
  unfold tailWord_107659
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926646316977304538470031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2617764211318203025646687 3926646316977304538470031)
  ·
    refine ⟨5889969475465956807705047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926646316977304538470031 5889969475465956807705047)
    ·
      refine ⟨8834954213198935211557571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5889969475465956807705047 8834954213198935211557571)
      ·
        refine ⟨13252431319798402817336357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834954213198935211557571 13252431319798402817336357)
        ·
          refine ⟨2484830872462200528250567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13252431319798402817336357 2484830872462200528250567)
          ·
            refine ⟨3727246308693300792375851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484830872462200528250567 3727246308693300792375851)
            ·
              refine ⟨5590869463039951188563777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727246308693300792375851 5590869463039951188563777)
              ·
                refine ⟨4193152097279963391422833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590869463039951188563777 4193152097279963391422833)
                ·
                  refine ⟨3144864072959972543567125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193152097279963391422833 3144864072959972543567125)
                  ·
                    refine ⟨147415503419998712979709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3144864072959972543567125 147415503419998712979709)
                    ·
                      refine ⟨55280813782499517367391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147415503419998712979709 55280813782499517367391)
                      ·
                        rfl

theorem cell23_107659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3].length) (baseStart_107659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107659 prefixEnd_107659 := by exact prefixLift 107659
  have htrace : WordTrace (prefixWord ++ tailWord_107659) baseStart_107659 baseEnd_107659 := by
    simpa [prefixWord, tailWord_107659, baseEnd_107659] using wordTrace_append hprefix tailTrace_107659
  have hstable : (prefixWord ++ tailWord_107659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107659).length < 2 ^ (prefixWord ++ tailWord_107659).sum := by decide
  have hdescent : baseEnd_107659 < baseStart_107659 := by decide
  rcases family_descends (prefixWord ++ tailWord_107659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107676 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_107676 : Nat := 118140960795 + 107676 * 2 ^ 59
def prefixEnd_107676 : Nat := 4983230072969 + 3 ^ 40 * 107676 * 2
def baseEnd_107676 : Nat := 55289542953625950854813

theorem tailTrace_107676 : CollatzResearch.WordTrace tailWord_107676 prefixEnd_107676 55289542953625950854813 := by
  unfold tailWord_107676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963633178957858220919441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2618177571943810961225921 1963633178957858220919441)
  ·
    refine ⟨1472724884218393665689581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1963633178957858220919441 1472724884218393665689581)
    ·
      refine ⟨552271831581897624633593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1472724884218393665689581 552271831581897624633593)
      ·
        refine ⟨414203873686423218475195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552271831581897624633593 414203873686423218475195)
        ·
          refine ⟨621305810529634827712793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414203873686423218475195 621305810529634827712793)
          ·
            refine ⟨465979357897226120784595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621305810529634827712793 465979357897226120784595)
            ·
              refine ⟨698969036845839181176893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465979357897226120784595 698969036845839181176893)
              ·
                refine ⟨262113388817189692941335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698969036845839181176893 262113388817189692941335)
                ·
                  refine ⟨393170083225784539412003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262113388817189692941335 393170083225784539412003)
                  ·
                    refine ⟨589755124838676809118005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393170083225784539412003 589755124838676809118005)
                    ·
                      refine ⟨55289542953625950854813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 589755124838676809118005 55289542953625950854813)
                      ·
                        rfl

theorem cell23_107676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_107676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107676 prefixEnd_107676 := by exact prefixLift 107676
  have htrace : WordTrace (prefixWord ++ tailWord_107676) baseStart_107676 baseEnd_107676 := by
    simpa [prefixWord, tailWord_107676, baseEnd_107676] using wordTrace_append hprefix tailTrace_107676
  have hstable : (prefixWord ++ tailWord_107676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107676).length < 2 ^ (prefixWord ++ tailWord_107676).sum := by decide
  have hdescent : baseEnd_107676 < baseStart_107676 := by decide
  rcases family_descends (prefixWord ++ tailWord_107676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107706 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_107706 : Nat := 118140960795 + 107706 * 2 ^ 59
def prefixEnd_107706 : Nat := 4983230072969 + 3 ^ 40 * 107706 * 2
def baseEnd_107706 : Nat := 55304947373260833479675

theorem tailTrace_107706 : CollatzResearch.WordTrace tailWord_107706 prefixEnd_107706 55304947373260833479675 := by
  unfold tailWord_107706
  simp only [CollatzResearch.WordTrace]
  refine ⟨982090136951757891357743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2618907031871354376953981 982090136951757891357743)
  ·
    refine ⟨1473135205427636837036615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982090136951757891357743 1473135205427636837036615)
    ·
      refine ⟨2209702808141455255554923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473135205427636837036615 2209702808141455255554923)
      ·
        refine ⟨3314554212212182883332385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209702808141455255554923 3314554212212182883332385)
        ·
          refine ⟨2485915659159137162499289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3314554212212182883332385 2485915659159137162499289)
          ·
            refine ⟨1864436744369352871874467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485915659159137162499289 1864436744369352871874467)
            ·
              refine ⟨2796655116554029307811701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864436744369352871874467 2796655116554029307811701)
              ·
                refine ⟨262186417176940247607347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2796655116554029307811701 262186417176940247607347)
                ·
                  refine ⟨393279625765410371411021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262186417176940247607347 393279625765410371411021)
                  ·
                    refine ⟨147479859662028889279133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393279625765410371411021 147479859662028889279133)
                    ·
                      refine ⟨55304947373260833479675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147479859662028889279133 55304947373260833479675)
                      ·
                        rfl

theorem cell23_107706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_107706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107706 prefixEnd_107706 := by exact prefixLift 107706
  have htrace : WordTrace (prefixWord ++ tailWord_107706) baseStart_107706 baseEnd_107706 := by
    simpa [prefixWord, tailWord_107706, baseEnd_107706] using wordTrace_append hprefix tailTrace_107706
  have hstable : (prefixWord ++ tailWord_107706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107706).length < 2 ^ (prefixWord ++ tailWord_107706).sum := by decide
  have hdescent : baseEnd_107706 < baseStart_107706 := by decide
  rcases family_descends (prefixWord ++ tailWord_107706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107710 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_107710 : Nat := 118140960795 + 107710 * 2 ^ 59
def prefixEnd_107710 : Nat := 4983230072969 + 3 ^ 40 * 107710 * 2
def baseEnd_107710 : Nat := 55307001295878817829657

theorem tailTrace_107710 : CollatzResearch.WordTrace tailWord_107710 prefixEnd_107710 55307001295878817829657 := by
  unfold tailWord_107710
  simp only [CollatzResearch.WordTrace]
  refine ⟨491063304974067531072073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2619004293195026832384389 491063304974067531072073)
  ·
    refine ⟨368297478730550648304055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 491063304974067531072073 368297478730550648304055)
    ·
      refine ⟨552446218095825972456083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368297478730550648304055 552446218095825972456083)
      ·
        refine ⟨828669327143738958684125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552446218095825972456083 828669327143738958684125)
        ·
          refine ⟨310750997678902109506547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828669327143738958684125 310750997678902109506547)
          ·
            refine ⟨466126496518353164259821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310750997678902109506547 466126496518353164259821)
            ·
              refine ⟨174797436194382436597433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466126496518353164259821 174797436194382436597433)
              ·
                refine ⟨131098077145786827448075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174797436194382436597433 131098077145786827448075)
                ·
                  refine ⟨196647115718680241172113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131098077145786827448075 196647115718680241172113)
                  ·
                    refine ⟨147485336789010180879085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196647115718680241172113 147485336789010180879085)
                    ·
                      refine ⟨55307001295878817829657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147485336789010180879085 55307001295878817829657)
                      ·
                        rfl

theorem cell23_107710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_107710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107710 prefixEnd_107710 := by exact prefixLift 107710
  have htrace : WordTrace (prefixWord ++ tailWord_107710) baseStart_107710 baseEnd_107710 := by
    simpa [prefixWord, tailWord_107710, baseEnd_107710] using wordTrace_append hprefix tailTrace_107710
  have hstable : (prefixWord ++ tailWord_107710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107710).length < 2 ^ (prefixWord ++ tailWord_107710).sum := by decide
  have hdescent : baseEnd_107710 < baseStart_107710 := by decide
  rcases family_descends (prefixWord ++ tailWord_107710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107719 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_107719 : Nat := 118140960795 + 107719 * 2 ^ 59
def prefixEnd_107719 : Nat := 4983230072969 + 3 ^ 40 * 107719 * 2
def baseEnd_107719 : Nat := 55311622621769282617115

theorem tailTrace_107719 : CollatzResearch.WordTrace tailWord_107719 prefixEnd_107719 55311622621769282617115 := by
  unfold tailWord_107719
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928834696759934785654211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2619223131173289857102807 3928834696759934785654211)
  ·
    refine ⟨5893252045139902178481317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928834696759934785654211 5893252045139902178481317)
    ·
      refine ⟨1104984758463731658465247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5893252045139902178481317 1104984758463731658465247)
      ·
        refine ⟨1657477137695597487697871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104984758463731658465247 1657477137695597487697871)
        ·
          refine ⟨2486215706543396231546807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657477137695597487697871 2486215706543396231546807)
          ·
            refine ⟨3729323559815094347320211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486215706543396231546807 3729323559815094347320211)
            ·
              refine ⟨5593985339722641520980317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729323559815094347320211 5593985339722641520980317)
              ·
                refine ⟨2097744502395990570367619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5593985339722641520980317 2097744502395990570367619)
                ·
                  refine ⟨3146616753593985855551429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097744502395990570367619 3146616753593985855551429)
                  ·
                    refine ⟨589990641298872347915893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146616753593985855551429 589990641298872347915893)
                    ·
                      refine ⟨55311622621769282617115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 589990641298872347915893 55311622621769282617115)
                      ·
                        rfl

theorem cell23_107719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_107719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107719 prefixEnd_107719 := by exact prefixLift 107719
  have htrace : WordTrace (prefixWord ++ tailWord_107719) baseStart_107719 baseEnd_107719 := by
    simpa [prefixWord, tailWord_107719, baseEnd_107719] using wordTrace_append hprefix tailTrace_107719
  have hstable : (prefixWord ++ tailWord_107719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107719).length < 2 ^ (prefixWord ++ tailWord_107719).sum := by decide
  have hdescent : baseEnd_107719 < baseStart_107719 := by decide
  rcases family_descends (prefixWord ++ tailWord_107719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107756 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_107756 : Nat := 118140960795 + 107756 * 2 ^ 59
def prefixEnd_107756 : Nat := 4983230072969 + 3 ^ 40 * 107756 * 2
def baseEnd_107756 : Nat := 18443540468661879284815

theorem tailTrace_107756 : CollatzResearch.WordTrace tailWord_107756 prefixEnd_107756 18443540468661879284815 := by
  unfold tailWord_107756
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965092098812945052375561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2620122798417260069834081 1965092098812945052375561)
  ·
    refine ⟨1473819074109708789281671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1965092098812945052375561 1473819074109708789281671)
    ·
      refine ⟨2210728611164563183922507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473819074109708789281671 2210728611164563183922507)
      ·
        refine ⟨3316092916746844775883761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210728611164563183922507 3316092916746844775883761)
        ·
          refine ⟨2487069687560133581912821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316092916746844775883761 2487069687560133581912821)
          ·
            refine ⟨233162783208762523304327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2487069687560133581912821 233162783208762523304327)
            ·
              refine ⟨349744174813143784956491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233162783208762523304327 349744174813143784956491)
              ·
                refine ⟨524616262219715677434737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349744174813143784956491 524616262219715677434737)
                ·
                  refine ⟨393462196664786758076053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524616262219715677434737 393462196664786758076053)
                  ·
                    refine ⟨18443540468661879284815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 393462196664786758076053 18443540468661879284815)
                    ·
                      rfl

theorem cell23_107756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_107756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107756 prefixEnd_107756 := by exact prefixLift 107756
  have htrace : WordTrace (prefixWord ++ tailWord_107756) baseStart_107756 baseEnd_107756 := by
    simpa [prefixWord, tailWord_107756, baseEnd_107756] using wordTrace_append hprefix tailTrace_107756
  have hstable : (prefixWord ++ tailWord_107756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107756).length < 2 ^ (prefixWord ++ tailWord_107756).sum := by decide
  have hdescent : baseEnd_107756 < baseStart_107756 := by decide
  rcases family_descends (prefixWord ++ tailWord_107756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107763 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 1, 4, 2]
def baseStart_107763 : Nat := 118140960795 + 107763 * 2 ^ 59
def prefixEnd_107763 : Nat := 4983230072969 + 3 ^ 40 * 107763 * 2
def baseEnd_107763 : Nat := 55334215770567110466913

theorem tailTrace_107763 : CollatzResearch.WordTrace tailWord_107763 prefixEnd_107763 55334215770567110466913 := by
  unfold tailWord_107763
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930439508600530300255943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2620293005733686866837295 3930439508600530300255943)
  ·
    refine ⟨5895659262900795450383915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930439508600530300255943 5895659262900795450383915)
    ·
      refine ⟨8843488894351193175575873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895659262900795450383915 8843488894351193175575873)
      ·
        refine ⟨6632616670763394881681905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8843488894351193175575873 6632616670763394881681905)
        ·
          refine ⟨4974462503072546161261429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6632616670763394881681905 4974462503072546161261429)
          ·
            refine ⟨466355859663051202618259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4974462503072546161261429 466355859663051202618259)
            ·
              refine ⟨699533789494576803927389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466355859663051202618259 699533789494576803927389)
              ·
                refine ⟨262325171060466301472771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699533789494576803927389 262325171060466301472771)
                ·
                  refine ⟨393487756590699452209157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262325171060466301472771 393487756590699452209157)
                  ·
                    refine ⟨73778954360756147289217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393487756590699452209157 73778954360756147289217)
                    ·
                      refine ⟨55334215770567110466913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73778954360756147289217 55334215770567110466913)
                      ·
                        rfl

theorem cell23_107763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4, 2].length) (baseStart_107763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107763 prefixEnd_107763 := by exact prefixLift 107763
  have htrace : WordTrace (prefixWord ++ tailWord_107763) baseStart_107763 baseEnd_107763 := by
    simpa [prefixWord, tailWord_107763, baseEnd_107763] using wordTrace_append hprefix tailTrace_107763
  have hstable : (prefixWord ++ tailWord_107763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107763).length < 2 ^ (prefixWord ++ tailWord_107763).sum := by decide
  have hdescent : baseEnd_107763 < baseStart_107763 := by decide
  rcases family_descends (prefixWord ++ tailWord_107763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107780 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_107780 : Nat := 118140960795 + 107780 * 2 ^ 59
def prefixEnd_107780 : Nat := 4983230072969 + 3 ^ 40 * 107780 * 2
def baseEnd_107780 : Nat := 55342944941693543954335

theorem tailTrace_107780 : CollatzResearch.WordTrace tailWord_107780 prefixEnd_107780 55342944941693543954335 := by
  unfold tailWord_107780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965529774769471101812397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2620706366359294802416529 1965529774769471101812397)
  ·
    refine ⟨737073665538551663179649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1965529774769471101812397 737073665538551663179649)
    ·
      refine ⟨552805249153913747384737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 737073665538551663179649 552805249153913747384737)
      ·
        refine ⟨414603936865435310538553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552805249153913747384737 414603936865435310538553)
        ·
          refine ⟨310952952649076482903915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414603936865435310538553 310952952649076482903915)
          ·
            refine ⟨466429428973614724355873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310952952649076482903915 466429428973614724355873)
            ·
              refine ⟨349822071730211043266905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466429428973614724355873 349822071730211043266905)
              ·
                refine ⟨262366553797658282450179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349822071730211043266905 262366553797658282450179)
                ·
                  refine ⟨393549830696487423675269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262366553797658282450179 393549830696487423675269)
                  ·
                    refine ⟨73790593255591391939113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393549830696487423675269 73790593255591391939113)
                    ·
                      refine ⟨55342944941693543954335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73790593255591391939113 55342944941693543954335)
                      ·
                        rfl

theorem cell23_107780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_107780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107780 prefixEnd_107780 := by exact prefixLift 107780
  have htrace : WordTrace (prefixWord ++ tailWord_107780) baseStart_107780 baseEnd_107780 := by
    simpa [prefixWord, tailWord_107780, baseEnd_107780] using wordTrace_append hprefix tailTrace_107780
  have hstable : (prefixWord ++ tailWord_107780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107780).length < 2 ^ (prefixWord ++ tailWord_107780).sum := by decide
  have hdescent : baseEnd_107780 < baseStart_107780 := by decide
  rcases family_descends (prefixWord ++ tailWord_107780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107784 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_107784 : Nat := 118140960795 + 107784 * 2 ^ 59
def prefixEnd_107784 : Nat := 4983230072969 + 3 ^ 40 * 107784 * 2
def baseEnd_107784 : Nat := 55344998864311528304317

theorem tailTrace_107784 : CollatzResearch.WordTrace tailWord_107784 prefixEnd_107784 55344998864311528304317 := by
  unfold tailWord_107784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965602720762225443385203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2620803627682967257846937 1965602720762225443385203)
  ·
    refine ⟨2948404081143338165077805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965602720762225443385203 2948404081143338165077805)
    ·
      refine ⟨1105651530428751811904177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2948404081143338165077805 1105651530428751811904177)
      ·
        refine ⟨829238647821563858928133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1105651530428751811904177 829238647821563858928133)
        ·
          refine ⟨155482246466543223549025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 829238647821563858928133 155482246466543223549025)
          ·
            refine ⟨116611684849907417661769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155482246466543223549025 116611684849907417661769)
            ·
              refine ⟨87458763637430563246327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116611684849907417661769 87458763637430563246327)
              ·
                refine ⟨131188145456145844869491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87458763637430563246327 131188145456145844869491)
                ·
                  refine ⟨196782218184218767304237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131188145456145844869491 196782218184218767304237)
                  ·
                    refine ⟨73793331819082037739089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196782218184218767304237 73793331819082037739089)
                    ·
                      refine ⟨55344998864311528304317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73793331819082037739089 55344998864311528304317)
                      ·
                        rfl

theorem cell23_107784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_107784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107784 prefixEnd_107784 := by exact prefixLift 107784
  have htrace : WordTrace (prefixWord ++ tailWord_107784) baseStart_107784 baseEnd_107784 := by
    simpa [prefixWord, tailWord_107784, baseEnd_107784] using wordTrace_append hprefix tailTrace_107784
  have hstable : (prefixWord ++ tailWord_107784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107784).length < 2 ^ (prefixWord ++ tailWord_107784).sum := by decide
  have hdescent : baseEnd_107784 < baseStart_107784 := by decide
  rcases family_descends (prefixWord ++ tailWord_107784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107813 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_107813 : Nat := 118140960795 + 107813 * 2 ^ 59
def prefixEnd_107813 : Nat := 4983230072969 + 3 ^ 40 * 107813 * 2
def baseEnd_107813 : Nat := 55359889803291914841683

theorem tailTrace_107813 : CollatzResearch.WordTrace tailWord_107813 prefixEnd_107813 55359889803291914841683 := by
  unfold tailWord_107813
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932263158419388839576093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2621508772279592559717395 3932263158419388839576093)
  ·
    refine ⟨1474598684407270814841035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3932263158419388839576093 1474598684407270814841035)
    ·
      refine ⟨2211898026610906222261553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474598684407270814841035 2211898026610906222261553)
      ·
        refine ⟨1658923519958179666696165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211898026610906222261553 1658923519958179666696165)
        ·
          refine ⟨311048159992158687505531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1658923519958179666696165 311048159992158687505531)
          ·
            refine ⟨466572239988238031258297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311048159992158687505531 466572239988238031258297)
            ·
              refine ⟨349929179991178523443723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466572239988238031258297 349929179991178523443723)
              ·
                refine ⟨524893769986767785165585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349929179991178523443723 524893769986767785165585)
                ·
                  refine ⟨393670327490075838874189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524893769986767785165585 393670327490075838874189)
                  ·
                    refine ⟨147626372808778439577821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393670327490075838874189 147626372808778439577821)
                    ·
                      refine ⟨55359889803291914841683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147626372808778439577821 55359889803291914841683)
                      ·
                        rfl

theorem cell23_107813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_107813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107813 prefixEnd_107813 := by exact prefixLift 107813
  have htrace : WordTrace (prefixWord ++ tailWord_107813) baseStart_107813 baseEnd_107813 := by
    simpa [prefixWord, tailWord_107813, baseEnd_107813] using wordTrace_append hprefix tailTrace_107813
  have hstable : (prefixWord ++ tailWord_107813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107813).length < 2 ^ (prefixWord ++ tailWord_107813).sum := by decide
  have hdescent : baseEnd_107813 < baseStart_107813 := by decide
  rcases family_descends (prefixWord ++ tailWord_107813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107866 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_107866 : Nat := 118140960795 + 107866 * 2 ^ 59
def prefixEnd_107866 : Nat := 4983230072969 + 3 ^ 40 * 107866 * 2
def baseEnd_107866 : Nat := 55387104277980207478939

theorem tailTrace_107866 : CollatzResearch.WordTrace tailWord_107866 prefixEnd_107866 55387104277980207478939 := by
  unfold tailWord_107866
  simp only [CollatzResearch.WordTrace]
  refine ⟨983549056806844722813863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2622797484818252594170301 983549056806844722813863)
  ·
    refine ⟨1475323585210267084220795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983549056806844722813863 1475323585210267084220795)
    ·
      refine ⟨2212985377815400626331193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475323585210267084220795 2212985377815400626331193)
      ·
        refine ⟨1659739033361550469748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2212985377815400626331193 1659739033361550469748395)
        ·
          refine ⟨2489608550042325704622593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659739033361550469748395 2489608550042325704622593)
          ·
            refine ⟨1867206412531744278466945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489608550042325704622593 1867206412531744278466945)
            ·
              refine ⟨1400404809398808208850209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867206412531744278466945 1400404809398808208850209)
              ·
                refine ⟨1050303607049106156637657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400404809398808208850209 1050303607049106156637657)
                ·
                  refine ⟨787727705286829617478243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050303607049106156637657 787727705286829617478243)
                  ·
                    refine ⟨1181591557930244426217365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 787727705286829617478243 1181591557930244426217365)
                    ·
                      refine ⟨55387104277980207478939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1181591557930244426217365 55387104277980207478939)
                      ·
                        rfl

theorem cell23_107866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_107866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107866 prefixEnd_107866 := by exact prefixLift 107866
  have htrace : WordTrace (prefixWord ++ tailWord_107866) baseStart_107866 baseEnd_107866 := by
    simpa [prefixWord, tailWord_107866, baseEnd_107866] using wordTrace_append hprefix tailTrace_107866
  have hstable : (prefixWord ++ tailWord_107866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107866).length < 2 ^ (prefixWord ++ tailWord_107866).sum := by decide
  have hdescent : baseEnd_107866 < baseStart_107866 := by decide
  rcases family_descends (prefixWord ++ tailWord_107866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107890 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_107890 : Nat := 118140960795 + 107890 * 2 ^ 59
def prefixEnd_107890 : Nat := 4983230072969 + 3 ^ 40 * 107890 * 2
def baseEnd_107890 : Nat := 55399427813688113578829

theorem tailTrace_107890 : CollatzResearch.WordTrace tailWord_107890 prefixEnd_107890 55399427813688113578829 := by
  unfold tailWord_107890
  simp only [CollatzResearch.WordTrace]
  refine ⟨983767894785107747532281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2623381052760287326752749 983767894785107747532281)
  ·
    refine ⟨737825921088830810649211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 983767894785107747532281 737825921088830810649211)
    ·
      refine ⟨1106738881633246215973817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737825921088830810649211 1106738881633246215973817)
      ·
        refine ⟨830054161224934661980363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1106738881633246215973817 830054161224934661980363)
        ·
          refine ⟨1245081241837401992970545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830054161224934661980363 1245081241837401992970545)
          ·
            refine ⟨933810931378051494727909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245081241837401992970545 933810931378051494727909)
            ·
              refine ⟨175089549633384655261483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 933810931378051494727909 175089549633384655261483)
              ·
                refine ⟨262634324450076982892225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175089549633384655261483 262634324450076982892225)
                ·
                  refine ⟨196975743337557737169169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262634324450076982892225 196975743337557737169169)
                  ·
                    refine ⟨147731807503168302876877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196975743337557737169169 147731807503168302876877)
                    ·
                      refine ⟨55399427813688113578829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147731807503168302876877 55399427813688113578829)
                      ·
                        rfl

theorem cell23_107890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_107890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107890 prefixEnd_107890 := by exact prefixLift 107890
  have htrace : WordTrace (prefixWord ++ tailWord_107890) baseStart_107890 baseEnd_107890 := by
    simpa [prefixWord, tailWord_107890, baseEnd_107890] using wordTrace_append hprefix tailTrace_107890
  have hstable : (prefixWord ++ tailWord_107890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107890).length < 2 ^ (prefixWord ++ tailWord_107890).sum := by decide
  have hdescent : baseEnd_107890 < baseStart_107890 := by decide
  rcases family_descends (prefixWord ++ tailWord_107890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107930 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_107930 : Nat := 118140960795 + 107930 * 2 ^ 59
def prefixEnd_107930 : Nat := 4983230072969 + 3 ^ 40 * 107930 * 2
def baseEnd_107930 : Nat := 55419967039867957078645

theorem tailTrace_107930 : CollatzResearch.WordTrace tailWord_107930 prefixEnd_107930 55419967039867957078645 := by
  unfold tailWord_107930
  simp only [CollatzResearch.WordTrace]
  refine ⟨984132624748879455396311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2624353665997011881056829 984132624748879455396311)
  ·
    refine ⟨1476198937123319183094467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984132624748879455396311 1476198937123319183094467)
    ·
      refine ⟨2214298405684978774641701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476198937123319183094467 2214298405684978774641701)
      ·
        refine ⟨415180951065933520245319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2214298405684978774641701 415180951065933520245319)
        ·
          refine ⟨622771426598900280367979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415180951065933520245319 622771426598900280367979)
          ·
            refine ⟨934157139898350420551969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622771426598900280367979 934157139898350420551969)
            ·
              refine ⟨700617854923762815413977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934157139898350420551969 700617854923762815413977)
              ·
                refine ⟨525463391192822111560483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700617854923762815413977 525463391192822111560483)
                ·
                  refine ⟨788195086789233167340725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525463391192822111560483 788195086789233167340725)
                  ·
                    refine ⟨73893289386490609438193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 788195086789233167340725 73893289386490609438193)
                    ·
                      refine ⟨55419967039867957078645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 73893289386490609438193 55419967039867957078645)
                      ·
                        rfl

theorem cell23_107930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_107930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107930 prefixEnd_107930 := by exact prefixLift 107930
  have htrace : WordTrace (prefixWord ++ tailWord_107930) baseStart_107930 baseEnd_107930 := by
    simpa [prefixWord, tailWord_107930, baseEnd_107930] using wordTrace_append hprefix tailTrace_107930
  have hstable : (prefixWord ++ tailWord_107930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107930).length < 2 ^ (prefixWord ++ tailWord_107930).sum := by decide
  have hdescent : baseEnd_107930 < baseStart_107930 := by decide
  rcases family_descends (prefixWord ++ tailWord_107930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107953 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_107953 : Nat := 118140960795 + 107953 * 2 ^ 59
def prefixEnd_107953 : Nat := 4983230072969 + 3 ^ 40 * 107953 * 2
def baseEnd_107953 : Nat := 18477259031640455697013

theorem tailTrace_107953 : CollatzResearch.WordTrace tailWord_107953 prefixEnd_107953 18477259031640455697013 := by
  unfold tailWord_107953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937369377912192749672513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2624912918608128499781675 3937369377912192749672513)
  ·
    refine ⟨2953027033434144562254385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3937369377912192749672513 2953027033434144562254385)
    ·
      refine ⟨2214770275075608421690789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953027033434144562254385 2214770275075608421690789)
      ·
        refine ⟨415269426576676579067023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2214770275075608421690789 415269426576676579067023)
        ·
          refine ⟨622904139865014868600535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415269426576676579067023 622904139865014868600535)
          ·
            refine ⟨934356209797522302900803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622904139865014868600535 934356209797522302900803)
            ·
              refine ⟨1401534314696283454351205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934356209797522302900803 1401534314696283454351205)
              ·
                refine ⟨262787684005553147690851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1401534314696283454351205 262787684005553147690851)
                ·
                  refine ⟨394181526008329721536277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262787684005553147690851 394181526008329721536277)
                  ·
                    refine ⟨18477259031640455697013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 394181526008329721536277 18477259031640455697013)
                    ·
                      rfl

theorem cell23_107953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_107953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107953 prefixEnd_107953 := by exact prefixLift 107953
  have htrace : WordTrace (prefixWord ++ tailWord_107953) baseStart_107953 baseEnd_107953 := by
    simpa [prefixWord, tailWord_107953, baseEnd_107953] using wordTrace_append hprefix tailTrace_107953
  have hstable : (prefixWord ++ tailWord_107953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107953).length < 2 ^ (prefixWord ++ tailWord_107953).sum := by decide
  have hdescent : baseEnd_107953 < baseStart_107953 := by decide
  rcases family_descends (prefixWord ++ tailWord_107953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107957 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_107957 : Nat := 118140960795 + 107957 * 2 ^ 59
def prefixEnd_107957 : Nat := 4983230072969 + 3 ^ 40 * 107957 * 2
def baseEnd_107957 : Nat := 18477943672513117147007

theorem tailTrace_107957 : CollatzResearch.WordTrace tailWord_107957 prefixEnd_107957 18477943672513117147007 := by
  unfold tailWord_107957
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937515269897701432818125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2625010179931800955212083 3937515269897701432818125)
  ·
    refine ⟨1476568226211638037306797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3937515269897701432818125 1476568226211638037306797)
    ·
      refine ⟨553713084829364263990049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1476568226211638037306797 553713084829364263990049)
      ·
        refine ⟨415284813622023197992537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553713084829364263990049 415284813622023197992537)
        ·
          refine ⟨311463610216517398494403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415284813622023197992537 311463610216517398494403)
          ·
            refine ⟨467195415324776097741605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311463610216517398494403 467195415324776097741605)
            ·
              refine ⟨87599140373395518326551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467195415324776097741605 87599140373395518326551)
              ·
                refine ⟨131398710560093277489827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87599140373395518326551 131398710560093277489827)
                ·
                  refine ⟨197098065840139916234741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131398710560093277489827 197098065840139916234741)
                  ·
                    refine ⟨18477943672513117147007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197098065840139916234741 18477943672513117147007)
                    ·
                      rfl

theorem cell23_107957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_107957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107957 prefixEnd_107957 := by exact prefixLift 107957
  have htrace : WordTrace (prefixWord ++ tailWord_107957) baseStart_107957 baseEnd_107957 := by
    simpa [prefixWord, tailWord_107957, baseEnd_107957] using wordTrace_append hprefix tailTrace_107957
  have hstable : (prefixWord ++ tailWord_107957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107957).length < 2 ^ (prefixWord ++ tailWord_107957).sum := by decide
  have hdescent : baseEnd_107957 < baseStart_107957 := by decide
  rcases family_descends (prefixWord ++ tailWord_107957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107980 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_107980 : Nat := 118140960795 + 107980 * 2 ^ 59
def prefixEnd_107980 : Nat := 4983230072969 + 3 ^ 40 * 107980 * 2
def baseEnd_107980 : Nat := 55445641072592761453415

theorem tailTrace_107980 : CollatzResearch.WordTrace tailWord_107980 prefixEnd_107980 55445641072592761453415 := by
  unfold tailWord_107980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1969177074407188180452697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2625569432542917573936929 1969177074407188180452697)
  ·
    refine ⟨1476882805805391135339523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1969177074407188180452697 1476882805805391135339523)
    ·
      refine ⟨2215324208708086703009285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476882805805391135339523 2215324208708086703009285)
      ·
        refine ⟨415373289132766256814241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2215324208708086703009285 415373289132766256814241)
        ·
          refine ⟨311529966849574692610681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415373289132766256814241 311529966849574692610681)
          ·
            refine ⟨233647475137181019458011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311529966849574692610681 233647475137181019458011)
            ·
              refine ⟨350471212705771529187017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233647475137181019458011 350471212705771529187017)
              ·
                refine ⟨262853409529328646890263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350471212705771529187017 262853409529328646890263)
                ·
                  refine ⟨394280114293992970335395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262853409529328646890263 394280114293992970335395)
                  ·
                    refine ⟨591420171440989455503093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394280114293992970335395 591420171440989455503093)
                    ·
                      refine ⟨55445641072592761453415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 591420171440989455503093 55445641072592761453415)
                      ·
                        rfl

theorem cell23_107980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_107980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107980 prefixEnd_107980 := by exact prefixLift 107980
  have htrace : WordTrace (prefixWord ++ tailWord_107980) baseStart_107980 baseEnd_107980 := by
    simpa [prefixWord, tailWord_107980, baseEnd_107980] using wordTrace_append hprefix tailTrace_107980
  have hstable : (prefixWord ++ tailWord_107980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107980).length < 2 ^ (prefixWord ++ tailWord_107980).sum := by decide
  have hdescent : baseEnd_107980 < baseStart_107980 := by decide
  rcases family_descends (prefixWord ++ tailWord_107980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107997 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_107997 : Nat := 118140960795 + 107997 * 2 ^ 59
def prefixEnd_107997 : Nat := 4983230072969 + 3 ^ 40 * 107997 * 2
def baseEnd_107997 : Nat := 55454370243719194940837

theorem tailTrace_107997 : CollatzResearch.WordTrace tailWord_107997 prefixEnd_107997 55454370243719194940837 := by
  unfold tailWord_107997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3938974189752788264274245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2625982793168525509516163 3938974189752788264274245)
  ·
    refine ⟨738557660578647799551421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3938974189752788264274245 738557660578647799551421)
    ·
      refine ⟨276959122716992924831783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 738557660578647799551421 276959122716992924831783)
      ·
        refine ⟨415438684075489387247675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276959122716992924831783 415438684075489387247675)
        ·
          refine ⟨623158026113234080871513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415438684075489387247675 623158026113234080871513)
          ·
            refine ⟨467368519584925560653635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623158026113234080871513 467368519584925560653635)
            ·
              refine ⟨701052779377388340980453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467368519584925560653635 701052779377388340980453)
              ·
                refine ⟨131447396133260313933835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701052779377388340980453 131447396133260313933835)
                ·
                  refine ⟨197171094199890470900753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131447396133260313933835 197171094199890470900753)
                  ·
                    refine ⟨147878320649917853175565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197171094199890470900753 147878320649917853175565)
                    ·
                      refine ⟨55454370243719194940837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147878320649917853175565 55454370243719194940837)
                      ·
                        rfl

theorem cell23_107997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_107997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_107997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_107997 prefixEnd_107997 := by exact prefixLift 107997
  have htrace : WordTrace (prefixWord ++ tailWord_107997) baseStart_107997 baseEnd_107997 := by
    simpa [prefixWord, tailWord_107997, baseEnd_107997] using wordTrace_append hprefix tailTrace_107997
  have hstable : (prefixWord ++ tailWord_107997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107997).length < 2 ^ (prefixWord ++ tailWord_107997).sum := by decide
  have hdescent : baseEnd_107997 < baseStart_107997 := by decide
  rcases family_descends (prefixWord ++ tailWord_107997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108038 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_108038 : Nat := 118140960795 + 108038 * 2 ^ 59
def prefixEnd_108038 : Nat := 4983230072969 + 3 ^ 40 * 108038 * 2
def baseEnd_108038 : Nat := 18491807650184511509383

theorem tailTrace_108038 : CollatzResearch.WordTrace tailWord_108038 prefixEnd_108038 18491807650184511509383 := by
  unfold tailWord_108038
  simp only [CollatzResearch.WordTrace]
  refine ⟨123139674456382883328649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2626979721736168177677845 123139674456382883328649)
  ·
    refine ⟨92354755842287162496487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123139674456382883328649 92354755842287162496487)
    ·
      refine ⟨138532133763430743744731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92354755842287162496487 138532133763430743744731)
      ·
        refine ⟨207798200645146115617097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138532133763430743744731 207798200645146115617097)
        ·
          refine ⟨155848650483859586712823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207798200645146115617097 155848650483859586712823)
          ·
            refine ⟨233772975725789380069235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155848650483859586712823 233772975725789380069235)
            ·
              refine ⟨350659463588684070103853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233772975725789380069235 350659463588684070103853)
              ·
                refine ⟨131497298845756526288945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350659463588684070103853 131497298845756526288945)
                ·
                  refine ⟨98622974134317394716709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131497298845756526288945 98622974134317394716709)
                  ·
                    refine ⟨18491807650184511509383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98622974134317394716709 18491807650184511509383)
                    ·
                      rfl

theorem cell23_108038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_108038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108038 prefixEnd_108038 := by exact prefixLift 108038
  have htrace : WordTrace (prefixWord ++ tailWord_108038) baseStart_108038 baseEnd_108038 := by
    simpa [prefixWord, tailWord_108038, baseEnd_108038] using wordTrace_append hprefix tailTrace_108038
  have hstable : (prefixWord ++ tailWord_108038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108038).length < 2 ^ (prefixWord ++ tailWord_108038).sum := by decide
  have hdescent : baseEnd_108038 < baseStart_108038 := by decide
  rcases family_descends (prefixWord ++ tailWord_108038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108044 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_108044 : Nat := 118140960795 + 108044 * 2 ^ 59
def prefixEnd_108044 : Nat := 4983230072969 + 3 ^ 40 * 108044 * 2
def baseEnd_108044 : Nat := 55478503834480511053121

theorem tailTrace_108044 : CollatzResearch.WordTrace tailWord_108044 prefixEnd_108044 55478503834480511053121 := by
  unfold tailWord_108044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970344210291257645617593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2627125613721676860823457 1970344210291257645617593)
  ·
    refine ⟨1477758157718443234213195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1970344210291257645617593 1477758157718443234213195)
    ·
      refine ⟨2216637236577664851319793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477758157718443234213195 2216637236577664851319793)
      ·
        refine ⟨1662477927433248638489845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2216637236577664851319793 1662477927433248638489845)
        ·
          refine ⟨155857305696867059858423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1662477927433248638489845 155857305696867059858423)
          ·
            refine ⟨233785958545300589787635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155857305696867059858423 233785958545300589787635)
            ·
              refine ⟨350678937817950884681453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233785958545300589787635 350678937817950884681453)
              ·
                refine ⟨131504601681731581755545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350678937817950884681453 131504601681731581755545)
                ·
                  refine ⟨98628451261298686316659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131504601681731581755545 98628451261298686316659)
                  ·
                    refine ⟨147942676891948029474989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98628451261298686316659 147942676891948029474989)
                    ·
                      refine ⟨55478503834480511053121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 147942676891948029474989 55478503834480511053121)
                      ·
                        rfl

theorem cell23_108044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_108044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108044 prefixEnd_108044 := by exact prefixLift 108044
  have htrace : WordTrace (prefixWord ++ tailWord_108044) baseStart_108044 baseEnd_108044 := by
    simpa [prefixWord, tailWord_108044, baseEnd_108044] using wordTrace_append hprefix tailTrace_108044
  have hstable : (prefixWord ++ tailWord_108044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108044).length < 2 ^ (prefixWord ++ tailWord_108044).sum := by decide
  have hdescent : baseEnd_108044 < baseStart_108044 := by decide
  rcases family_descends (prefixWord ++ tailWord_108044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108124 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 5]
def baseStart_108124 : Nat := 118140960795 + 108124 * 2 ^ 59
def prefixEnd_108124 : Nat := 4983230072969 + 3 ^ 40 * 108124 * 2
def baseEnd_108124 : Nat := 6168842476315577561417

theorem tailTrace_108124 : CollatzResearch.WordTrace tailWord_108124 prefixEnd_108124 6168842476315577561417 := by
  unfold tailWord_108124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971803130146344477073713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2629070840195125969431617 1971803130146344477073713)
  ·
    refine ⟨1478852347609758357805285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1971803130146344477073713 1478852347609758357805285)
    ·
      refine ⟨277284815176829692088491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1478852347609758357805285 277284815176829692088491)
      ·
        refine ⟨415927222765244538132737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277284815176829692088491 415927222765244538132737)
        ·
          refine ⟨311945417073933403599553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415927222765244538132737 311945417073933403599553)
          ·
            refine ⟨233959062805450052699665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311945417073933403599553 233959062805450052699665)
            ·
              refine ⟨175469297104087539524749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233959062805450052699665 175469297104087539524749)
              ·
                refine ⟨65800986414032827321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175469297104087539524749 65800986414032827321781)
                ·
                  refine ⟨6168842476315577561417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65800986414032827321781 6168842476315577561417)
                  ·
                    rfl

theorem cell23_108124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_108124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108124 prefixEnd_108124 := by exact prefixLift 108124
  have htrace : WordTrace (prefixWord ++ tailWord_108124) baseStart_108124 baseEnd_108124 := by
    simpa [prefixWord, tailWord_108124, baseEnd_108124] using wordTrace_append hprefix tailTrace_108124
  have hstable : (prefixWord ++ tailWord_108124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108124).length < 2 ^ (prefixWord ++ tailWord_108124).sum := by decide
  have hdescent : baseEnd_108124 < baseStart_108124 := by decide
  rcases family_descends (prefixWord ++ tailWord_108124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108140 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_108140 : Nat := 118140960795 + 108140 * 2 ^ 59
def prefixEnd_108140 : Nat := 4983230072969 + 3 ^ 40 * 108140 * 2
def baseEnd_108140 : Nat := 55527797977312135452679

theorem tailTrace_108140 : CollatzResearch.WordTrace tailWord_108140 prefixEnd_108140 55527797977312135452679 := by
  unfold tailWord_108140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972094914117361843364937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2629459885489815791153249 1972094914117361843364937)
  ·
    refine ⟨1479071185588021382523703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1972094914117361843364937 1479071185588021382523703)
    ·
      refine ⟨2218606778382032073785555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479071185588021382523703 2218606778382032073785555)
      ·
        refine ⟨3327910167573048110678333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218606778382032073785555 3327910167573048110678333)
        ·
          refine ⟨1247966312839893041504375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3327910167573048110678333 1247966312839893041504375)
          ·
            refine ⟨1871949469259839562256563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247966312839893041504375 1871949469259839562256563)
            ·
              refine ⟨2807924203889759343384845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871949469259839562256563 2807924203889759343384845)
              ·
                refine ⟨1052971576458659753769317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2807924203889759343384845 1052971576458659753769317)
                ·
                  refine ⟨197432170585998703831747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052971576458659753769317 197432170585998703831747)
                  ·
                    refine ⟨296148255878998055747621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197432170585998703831747 296148255878998055747621)
                    ·
                      refine ⟨55527797977312135452679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 296148255878998055747621 55527797977312135452679)
                      ·
                        rfl

theorem cell23_108140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_108140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108140 prefixEnd_108140 := by exact prefixLift 108140
  have htrace : WordTrace (prefixWord ++ tailWord_108140) baseStart_108140 baseEnd_108140 := by
    simpa [prefixWord, tailWord_108140, baseEnd_108140] using wordTrace_append hprefix tailTrace_108140
  have hstable : (prefixWord ++ tailWord_108140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108140).length < 2 ^ (prefixWord ++ tailWord_108140).sum := by decide
  have hdescent : baseEnd_108140 < baseStart_108140 := by decide
  rcases family_descends (prefixWord ++ tailWord_108140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108160 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_108160 : Nat := 118140960795 + 108160 * 2 ^ 59
def prefixEnd_108160 : Nat := 4983230072969 + 3 ^ 40 * 108160 * 2
def baseEnd_108160 : Nat := 55538067590402057202587

theorem tailTrace_108160 : CollatzResearch.WordTrace tailWord_108160 prefixEnd_108160 55538067590402057202587 := by
  unfold tailWord_108160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972459644081133551228967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2629946192108178068305289 1972459644081133551228967)
  ·
    refine ⟨2958689466121700326843451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972459644081133551228967 2958689466121700326843451)
    ·
      refine ⟨4438034199182550490265177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958689466121700326843451 4438034199182550490265177)
      ·
        refine ⟨3328525649386912867698883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438034199182550490265177 3328525649386912867698883)
        ·
          refine ⟨4992788474080369301548325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328525649386912867698883 4992788474080369301548325)
          ·
            refine ⟨936147838890069244040311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4992788474080369301548325 936147838890069244040311)
            ·
              refine ⟨1404221758335103866060467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936147838890069244040311 1404221758335103866060467)
              ·
                refine ⟨2106332637502655799090701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404221758335103866060467 2106332637502655799090701)
                ·
                  refine ⟨789874739063495924659013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2106332637502655799090701 789874739063495924659013)
                  ·
                    refine ⟨148101513574405485873565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789874739063495924659013 148101513574405485873565)
                    ·
                      refine ⟨55538067590402057202587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148101513574405485873565 55538067590402057202587)
                      ·
                        rfl

theorem cell23_108160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_108160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108160 prefixEnd_108160 := by exact prefixLift 108160
  have htrace : WordTrace (prefixWord ++ tailWord_108160) baseStart_108160 baseEnd_108160 := by
    simpa [prefixWord, tailWord_108160, baseEnd_108160] using wordTrace_append hprefix tailTrace_108160
  have hstable : (prefixWord ++ tailWord_108160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108160).length < 2 ^ (prefixWord ++ tailWord_108160).sum := by decide
  have hdescent : baseEnd_108160 < baseStart_108160 := by decide
  rcases family_descends (prefixWord ++ tailWord_108160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108167 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 3, 4]
def baseStart_108167 : Nat := 118140960795 + 108167 * 2 ^ 59
def prefixEnd_108167 : Nat := 4983230072969 + 3 ^ 40 * 108167 * 2
def baseEnd_108167 : Nat := 18513887318327843271685

theorem tailTrace_108167 : CollatzResearch.WordTrace tailWord_108167 prefixEnd_108167 18513887318327843271685 := by
  unfold tailWord_108167
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945174599136907297962755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2630116399424604865308503 3945174599136907297962755)
  ·
    refine ⟨5917761898705360946944133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3945174599136907297962755 5917761898705360946944133)
    ·
      refine ⟨1109580356007255177552025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5917761898705360946944133 1109580356007255177552025)
      ·
        refine ⟨832185267005441383164019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109580356007255177552025 832185267005441383164019)
        ·
          refine ⟨1248277900508162074746029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832185267005441383164019 1248277900508162074746029)
          ·
            refine ⟨468104212690560778029761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1248277900508162074746029 468104212690560778029761)
            ·
              refine ⟨351078159517920583522321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468104212690560778029761 351078159517920583522321)
              ·
                refine ⟨263308619638440437641741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351078159517920583522321 263308619638440437641741)
                ·
                  refine ⟨98740732364415164115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263308619638440437641741 98740732364415164115653)
                  ·
                    refine ⟨18513887318327843271685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98740732364415164115653 18513887318327843271685)
                    ·
                      rfl

theorem cell23_108167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_108167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108167 prefixEnd_108167 := by exact prefixLift 108167
  have htrace : WordTrace (prefixWord ++ tailWord_108167) baseStart_108167 baseEnd_108167 := by
    simpa [prefixWord, tailWord_108167, baseEnd_108167] using wordTrace_append hprefix tailTrace_108167
  have hstable : (prefixWord ++ tailWord_108167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108167).length < 2 ^ (prefixWord ++ tailWord_108167).sum := by decide
  have hdescent : baseEnd_108167 < baseStart_108167 := by decide
  rcases family_descends (prefixWord ++ tailWord_108167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108217 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 5, 2]
def baseStart_108217 : Nat := 118140960795 + 108217 * 2 ^ 59
def prefixEnd_108217 : Nat := 4983230072969 + 3 ^ 40 * 108217 * 2
def baseEnd_108217 : Nat := 55567335987708334189825

theorem tailTrace_108217 : CollatzResearch.WordTrace tailWord_108217 prefixEnd_108217 55567335987708334189825 := by
  unfold tailWord_108217
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946998248955765837282905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2631332165970510558188603 3946998248955765837282905)
  ·
    refine ⟨2960248686716824377962179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3946998248955765837282905 2960248686716824377962179)
    ·
      refine ⟨4440373030075236566943269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960248686716824377962179 4440373030075236566943269)
      ·
        refine ⟨832569943139106856301863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4440373030075236566943269 832569943139106856301863)
        ·
          refine ⟨1248854914708660284452795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832569943139106856301863 1248854914708660284452795)
          ·
            refine ⟨1873282372062990426679193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248854914708660284452795 1873282372062990426679193)
            ·
              refine ⟨1404961779047242820009395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873282372062990426679193 1404961779047242820009395)
              ·
                refine ⟨2107442668570864230014093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404961779047242820009395 2107442668570864230014093)
                ·
                  refine ⟨790291000714074086255285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2107442668570864230014093 790291000714074086255285)
                  ·
                    refine ⟨74089781316944445586433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 790291000714074086255285 74089781316944445586433)
                    ·
                      refine ⟨55567335987708334189825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74089781316944445586433 55567335987708334189825)
                      ·
                        rfl

theorem cell23_108217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_108217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108217 prefixEnd_108217 := by exact prefixLift 108217
  have htrace : WordTrace (prefixWord ++ tailWord_108217) baseStart_108217 baseEnd_108217 := by
    simpa [prefixWord, tailWord_108217, baseEnd_108217] using wordTrace_append hprefix tailTrace_108217
  have hstable : (prefixWord ++ tailWord_108217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108217).length < 2 ^ (prefixWord ++ tailWord_108217).sum := by decide
  have hdescent : baseEnd_108217 < baseStart_108217 := by decide
  rcases family_descends (prefixWord ++ tailWord_108217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108252 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_108252 : Nat := 118140960795 + 108252 * 2 ^ 59
def prefixEnd_108252 : Nat := 4983230072969 + 3 ^ 40 * 108252 * 2
def baseEnd_108252 : Nat := 18528435936871899084055

theorem tailTrace_108252 : CollatzResearch.WordTrace tailWord_108252 prefixEnd_108252 18528435936871899084055 := by
  unfold tailWord_108252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974137401914483407403505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2632183202552644543204673 1974137401914483407403505)
  ·
    refine ⟨1480603051435862555552629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1974137401914483407403505 1480603051435862555552629)
    ·
      refine ⟨138806536072112114583059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1480603051435862555552629 138806536072112114583059)
      ·
        refine ⟨208209804108168171874589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138806536072112114583059 208209804108168171874589)
        ·
          refine ⟨78078676540563064452971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208209804108168171874589 78078676540563064452971)
          ·
            refine ⟨117118014810844596679457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78078676540563064452971 117118014810844596679457)
            ·
              refine ⟨87838511108133447509593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117118014810844596679457 87838511108133447509593)
              ·
                refine ⟨65878883331100085632195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87838511108133447509593 65878883331100085632195)
                ·
                  refine ⟨98818324996650128448293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65878883331100085632195 98818324996650128448293)
                  ·
                    refine ⟨18528435936871899084055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98818324996650128448293 18528435936871899084055)
                    ·
                      rfl

theorem cell23_108252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_108252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108252 prefixEnd_108252 := by exact prefixLift 108252
  have htrace : WordTrace (prefixWord ++ tailWord_108252) baseStart_108252 baseEnd_108252 := by
    simpa [prefixWord, tailWord_108252, baseEnd_108252] using wordTrace_append hprefix tailTrace_108252
  have hstable : (prefixWord ++ tailWord_108252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108252).length < 2 ^ (prefixWord ++ tailWord_108252).sum := by decide
  have hdescent : baseEnd_108252 < baseStart_108252 := by decide
  rcases family_descends (prefixWord ++ tailWord_108252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108267 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3]
def baseStart_108267 : Nat := 118140960795 + 108267 * 2 ^ 59
def prefixEnd_108267 : Nat := 4983230072969 + 3 ^ 40 * 108267 * 2
def baseEnd_108267 : Nat := 55593010020433138564595

theorem tailTrace_108267 : CollatzResearch.WordTrace tailWord_108267 prefixEnd_108267 55593010020433138564595 := by
  unfold tailWord_108267
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948821898774624376603055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2632547932516416251068703 3948821898774624376603055)
  ·
    refine ⟨5923232848161936564904583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948821898774624376603055 5923232848161936564904583)
    ·
      refine ⟨8884849272242904847356875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923232848161936564904583 8884849272242904847356875)
      ·
        refine ⟨13327273908364357271035313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8884849272242904847356875 13327273908364357271035313)
        ·
          refine ⟨9995455431273267953276485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13327273908364357271035313 9995455431273267953276485)
          ·
            refine ⟨1874147893363737741239341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9995455431273267953276485 1874147893363737741239341)
            ·
              refine ⟨702805460011401652964753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874147893363737741239341 702805460011401652964753)
              ·
                refine ⟨527104095008551239723565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702805460011401652964753 527104095008551239723565)
                ·
                  refine ⟨197664035628206714896337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527104095008551239723565 197664035628206714896337)
                  ·
                    refine ⟨148248026721155036172253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197664035628206714896337 148248026721155036172253)
                    ·
                      refine ⟨55593010020433138564595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148248026721155036172253 55593010020433138564595)
                      ·
                        rfl

theorem cell23_108267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3].length) (baseStart_108267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108267 prefixEnd_108267 := by exact prefixLift 108267
  have htrace : WordTrace (prefixWord ++ tailWord_108267) baseStart_108267 baseEnd_108267 := by
    simpa [prefixWord, tailWord_108267, baseEnd_108267] using wordTrace_append hprefix tailTrace_108267
  have hstable : (prefixWord ++ tailWord_108267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108267).length < 2 ^ (prefixWord ++ tailWord_108267).sum := by decide
  have hdescent : baseEnd_108267 < baseStart_108267 := by decide
  rcases family_descends (prefixWord ++ tailWord_108267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108274 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_108274 : Nat := 118140960795 + 108274 * 2 ^ 59
def prefixEnd_108274 : Nat := 4983230072969 + 3 ^ 40 * 108274 * 2
def baseEnd_108274 : Nat := 18532201461671537059021

theorem tailTrace_108274 : CollatzResearch.WordTrace tailWord_108274 prefixEnd_108274 18532201461671537059021 := by
  unfold tailWord_108274
  simp only [CollatzResearch.WordTrace]
  refine ⟨987269302437316143026969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2632718139832843048071917 987269302437316143026969)
  ·
    refine ⟨740451976827987107270227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 987269302437316143026969 740451976827987107270227)
    ·
      refine ⟨1110677965241980660905341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740451976827987107270227 1110677965241980660905341)
      ·
        refine ⟨416504236965742747839503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1110677965241980660905341 416504236965742747839503)
        ·
          refine ⟨624756355448614121759255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416504236965742747839503 624756355448614121759255)
          ·
            refine ⟨937134533172921182638883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624756355448614121759255 937134533172921182638883)
            ·
              refine ⟨1405701799759381773958325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937134533172921182638883 1405701799759381773958325)
              ·
                refine ⟨131784543727442041308593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1405701799759381773958325 131784543727442041308593)
                ·
                  refine ⟨98838407795581530981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131784543727442041308593 98838407795581530981445)
                  ·
                    refine ⟨18532201461671537059021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98838407795581530981445 18532201461671537059021)
                    ·
                      rfl

theorem cell23_108274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_108274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108274 prefixEnd_108274 := by exact prefixLift 108274
  have htrace : WordTrace (prefixWord ++ tailWord_108274) baseStart_108274 baseEnd_108274 := by
    simpa [prefixWord, tailWord_108274, baseEnd_108274] using wordTrace_append hprefix tailTrace_108274
  have hstable : (prefixWord ++ tailWord_108274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108274).length < 2 ^ (prefixWord ++ tailWord_108274).sum := by decide
  have hdescent : baseEnd_108274 < baseStart_108274 := by decide
  rcases family_descends (prefixWord ++ tailWord_108274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108284 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_108284 : Nat := 118140960795 + 108284 * 2 ^ 59
def prefixEnd_108284 : Nat := 4983230072969 + 3 ^ 40 * 108284 * 2
def baseEnd_108284 : Nat := 55601739191559572052017

theorem tailTrace_108284 : CollatzResearch.WordTrace tailWord_108284 prefixEnd_108284 55601739191559572052017 := by
  unfold tailWord_108284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974720969856518139985953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2632961293142024186647937 1974720969856518139985953)
  ·
    refine ⟨1481040727392388604989465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1974720969856518139985953 1481040727392388604989465)
    ·
      refine ⟨1110780545544291453742099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1481040727392388604989465 1110780545544291453742099)
      ·
        refine ⟨1666170818316437180613149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110780545544291453742099 1666170818316437180613149)
        ·
          refine ⟨624814056868663942729931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1666170818316437180613149 624814056868663942729931)
          ·
            refine ⟨937221085302995914094897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624814056868663942729931 937221085302995914094897)
            ·
              refine ⟨702915813977246935571173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937221085302995914094897 702915813977246935571173)
              ·
                refine ⟨131796715120733800419595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702915813977246935571173 131796715120733800419595)
                ·
                  refine ⟨197695072681100700629393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131796715120733800419595 197695072681100700629393)
                  ·
                    refine ⟨148271304510825525472045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197695072681100700629393 148271304510825525472045)
                    ·
                      refine ⟨55601739191559572052017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148271304510825525472045 55601739191559572052017)
                      ·
                        rfl

theorem cell23_108284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_108284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108284 prefixEnd_108284 := by exact prefixLift 108284
  have htrace : WordTrace (prefixWord ++ tailWord_108284) baseStart_108284 baseEnd_108284 := by
    simpa [prefixWord, tailWord_108284, baseEnd_108284] using wordTrace_append hprefix tailTrace_108284
  have hstable : (prefixWord ++ tailWord_108284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108284).length < 2 ^ (prefixWord ++ tailWord_108284).sum := by decide
  have hdescent : baseEnd_108284 < baseStart_108284 := by decide
  rcases family_descends (prefixWord ++ tailWord_108284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108298 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_108298 : Nat := 118140960795 + 108298 * 2 ^ 59
def prefixEnd_108298 : Nat := 4983230072969 + 3 ^ 40 * 108298 * 2
def baseEnd_108298 : Nat := 55608927920722517276953

theorem tailTrace_108298 : CollatzResearch.WordTrace tailWord_108298 prefixEnd_108298 55608927920722517276953 := by
  unfold tailWord_108298
  simp only [CollatzResearch.WordTrace]
  refine ⟨987488140415579167745387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2633301707774877780654365 987488140415579167745387)
  ·
    refine ⟨1481232210623368751618081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987488140415579167745387 1481232210623368751618081)
    ·
      refine ⟨1110924157967526563713561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1481232210623368751618081 1110924157967526563713561)
      ·
        refine ⟨833193118475644922785171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110924157967526563713561 833193118475644922785171)
        ·
          refine ⟨1249789677713467384177757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833193118475644922785171 1249789677713467384177757)
          ·
            refine ⟨468671129142550269066659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1249789677713467384177757 468671129142550269066659)
            ·
              refine ⟨703006693713825403599989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468671129142550269066659 703006693713825403599989)
              ·
                refine ⟨65906877535671131587499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703006693713825403599989 65906877535671131587499)
                ·
                  refine ⟨98860316303506697381249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65906877535671131587499 98860316303506697381249)
                  ·
                    refine ⟨74145237227630023035937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98860316303506697381249 74145237227630023035937)
                    ·
                      refine ⟨55608927920722517276953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74145237227630023035937 55608927920722517276953)
                      ·
                        rfl

theorem cell23_108298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_108298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108298 prefixEnd_108298 := by exact prefixLift 108298
  have htrace : WordTrace (prefixWord ++ tailWord_108298) baseStart_108298 baseEnd_108298 := by
    simpa [prefixWord, tailWord_108298, baseEnd_108298] using wordTrace_append hprefix tailTrace_108298
  have hstable : (prefixWord ++ tailWord_108298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108298).length < 2 ^ (prefixWord ++ tailWord_108298).sum := by decide
  have hdescent : baseEnd_108298 < baseStart_108298 := by decide
  rcases family_descends (prefixWord ++ tailWord_108298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108318 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_108318 : Nat := 118140960795 + 108318 * 2 ^ 59
def prefixEnd_108318 : Nat := 4983230072969 + 3 ^ 40 * 108318 * 2
def baseEnd_108318 : Nat := 55619197533812439026861

theorem tailTrace_108318 : CollatzResearch.WordTrace tailWord_108318 prefixEnd_108318 55619197533812439026861 := by
  unfold tailWord_108318
  simp only [CollatzResearch.WordTrace]
  refine ⟨493835252698732510838701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2633788014393240057806405 493835252698732510838701)
  ·
    refine ⟨185188219762024691564513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 493835252698732510838701 185188219762024691564513)
    ·
      refine ⟨138891164821518518673385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185188219762024691564513 138891164821518518673385)
      ·
        refine ⟨104168373616138889005039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138891164821518518673385 104168373616138889005039)
        ·
          refine ⟨156252560424208333507559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104168373616138889005039 156252560424208333507559)
          ·
            refine ⟨234378840636312500261339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156252560424208333507559 234378840636312500261339)
            ·
              refine ⟨351568260954468750392009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234378840636312500261339 351568260954468750392009)
              ·
                refine ⟨263676195715851562794007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351568260954468750392009 263676195715851562794007)
                ·
                  refine ⟨395514293573777344191011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263676195715851562794007 395514293573777344191011)
                  ·
                    refine ⟨593271440360666016286517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395514293573777344191011 593271440360666016286517)
                    ·
                      refine ⟨55619197533812439026861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 593271440360666016286517 55619197533812439026861)
                      ·
                        rfl

theorem cell23_108318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_108318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108318 prefixEnd_108318 := by exact prefixLift 108318
  have htrace : WordTrace (prefixWord ++ tailWord_108318) baseStart_108318 baseEnd_108318 := by
    simpa [prefixWord, tailWord_108318, baseEnd_108318] using wordTrace_append hprefix tailTrace_108318
  have hstable : (prefixWord ++ tailWord_108318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108318).length < 2 ^ (prefixWord ++ tailWord_108318).sum := by decide
  have hdescent : baseEnd_108318 < baseStart_108318 := by decide
  rcases family_descends (prefixWord ++ tailWord_108318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108357 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_108357 : Nat := 118140960795 + 108357 * 2 ^ 59
def prefixEnd_108357 : Nat := 4983230072969 + 3 ^ 40 * 108357 * 2
def baseEnd_108357 : Nat := 55639223279337786439181

theorem tailTrace_108357 : CollatzResearch.WordTrace tailWord_108357 prefixEnd_108357 55639223279337786439181 := by
  unfold tailWord_108357
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952104468448569747379325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2634736312299046498252883 3952104468448569747379325)
  ·
    refine ⟨1482039175668213655267247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3952104468448569747379325 1482039175668213655267247)
    ·
      refine ⟨2223058763502320482900871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482039175668213655267247 2223058763502320482900871)
      ·
        refine ⟨3334588145253480724351307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223058763502320482900871 3334588145253480724351307)
        ·
          refine ⟨5001882217880221086526961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334588145253480724351307 5001882217880221086526961)
          ·
            refine ⟨3751411663410165814895221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001882217880221086526961 3751411663410165814895221)
            ·
              refine ⟨351694843444703045146427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3751411663410165814895221 351694843444703045146427)
              ·
                refine ⟨527542265167054567719641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351694843444703045146427 527542265167054567719641)
                ·
                  refine ⟨395656698875290925789731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527542265167054567719641 395656698875290925789731)
                  ·
                    refine ⟨593485048312936388684597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395656698875290925789731 593485048312936388684597)
                    ·
                      refine ⟨55639223279337786439181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 593485048312936388684597 55639223279337786439181)
                      ·
                        rfl

theorem cell23_108357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_108357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108357 prefixEnd_108357 := by exact prefixLift 108357
  have htrace : WordTrace (prefixWord ++ tailWord_108357) baseStart_108357 baseEnd_108357 := by
    simpa [prefixWord, tailWord_108357, baseEnd_108357] using wordTrace_append hprefix tailTrace_108357
  have hstable : (prefixWord ++ tailWord_108357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108357).length < 2 ^ (prefixWord ++ tailWord_108357).sum := by decide
  have hdescent : baseEnd_108357 < baseStart_108357 := by decide
  rcases family_descends (prefixWord ++ tailWord_108357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108427 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_108427 : Nat := 118140960795 + 108427 * 2 ^ 59
def prefixEnd_108427 : Nat := 4983230072969 + 3 ^ 40 * 108427 * 2
def baseEnd_108427 : Nat := 55675166925152512563859

theorem tailTrace_108427 : CollatzResearch.WordTrace tailWord_108427 prefixEnd_108427 55675166925152512563859 := by
  unfold tailWord_108427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954657578194971702427535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2636438385463314468285023 3954657578194971702427535)
  ·
    refine ⟨5931986367292457553641303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954657578194971702427535 5931986367292457553641303)
    ·
      refine ⟨8897979550938686330461955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5931986367292457553641303 8897979550938686330461955)
      ·
        refine ⟨13346969326408029495692933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897979550938686330461955 13346969326408029495692933)
        ·
          refine ⟨2502556748701505530442425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13346969326408029495692933 2502556748701505530442425)
          ·
            refine ⟨1876917561526129147831819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502556748701505530442425 1876917561526129147831819)
            ·
              refine ⟨2815376342289193721747729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876917561526129147831819 2815376342289193721747729)
              ·
                refine ⟨2111532256716895291310797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815376342289193721747729 2111532256716895291310797)
                ·
                  refine ⟨791824596268835734241549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2111532256716895291310797 791824596268835734241549)
                  ·
                    refine ⟨296934223600813400340581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791824596268835734241549 296934223600813400340581)
                    ·
                      refine ⟨55675166925152512563859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 296934223600813400340581 55675166925152512563859)
                      ·
                        rfl

theorem cell23_108427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_108427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108427 prefixEnd_108427 := by exact prefixLift 108427
  have htrace : WordTrace (prefixWord ++ tailWord_108427) baseStart_108427 baseEnd_108427 := by
    simpa [prefixWord, tailWord_108427, baseEnd_108427] using wordTrace_append hprefix tailTrace_108427
  have hstable : (prefixWord ++ tailWord_108427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108427).length < 2 ^ (prefixWord ++ tailWord_108427).sum := by decide
  have hdescent : baseEnd_108427 < baseStart_108427 := by decide
  rcases family_descends (prefixWord ++ tailWord_108427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108457 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_108457 : Nat := 118140960795 + 108457 * 2 ^ 59
def prefixEnd_108457 : Nat := 4983230072969 + 3 ^ 40 * 108457 * 2
def baseEnd_108457 : Nat := 55690571344787395188721

theorem tailTrace_108457 : CollatzResearch.WordTrace tailWord_108457 prefixEnd_108457 55690571344787395188721 := by
  unfold tailWord_108457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955751768086286826019625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2637167845390857884013083 3955751768086286826019625)
  ·
    refine ⟨2966813826064715119514719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955751768086286826019625 2966813826064715119514719)
    ·
      refine ⟨4450220739097072679272079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966813826064715119514719 4450220739097072679272079)
      ·
        refine ⟨6675331108645609018908119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450220739097072679272079 6675331108645609018908119)
        ·
          refine ⟨10012996662968413528362179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675331108645609018908119 10012996662968413528362179)
          ·
            refine ⟨15019494994452620292543269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10012996662968413528362179 15019494994452620292543269)
            ·
              refine ⟨2816155311459866304851863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15019494994452620292543269 2816155311459866304851863)
              ·
                refine ⟨4224232967189799457277795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816155311459866304851863 4224232967189799457277795)
                ·
                  refine ⟨6336349450784699185916693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224232967189799457277795 6336349450784699185916693)
                  ·
                    refine ⟨297016380505532774339845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6336349450784699185916693 297016380505532774339845)
                    ·
                      refine ⟨55690571344787395188721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 297016380505532774339845 55690571344787395188721)
                      ·
                        rfl

theorem cell23_108457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_108457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108457 prefixEnd_108457 := by exact prefixLift 108457
  have htrace : WordTrace (prefixWord ++ tailWord_108457) baseStart_108457 baseEnd_108457 := by
    simpa [prefixWord, tailWord_108457, baseEnd_108457] using wordTrace_append hprefix tailTrace_108457
  have hstable : (prefixWord ++ tailWord_108457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108457).length < 2 ^ (prefixWord ++ tailWord_108457).sum := by decide
  have hdescent : baseEnd_108457 < baseStart_108457 := by decide
  rcases family_descends (prefixWord ++ tailWord_108457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108462 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_108462 : Nat := 118140960795 + 108462 * 2 ^ 59
def prefixEnd_108462 : Nat := 4983230072969 + 3 ^ 40 * 108462 * 2
def baseEnd_108462 : Nat := 6188126527562208402911

theorem tailTrace_108462 : CollatzResearch.WordTrace tailWord_108462 prefixEnd_108462 6188126527562208402911 := by
  unfold tailWord_108462
  simp only [CollatzResearch.WordTrace]
  refine ⟨494491766633521584993955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2637289422045448453301093 494491766633521584993955)
  ·
    refine ⟨741737649950282377490933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494491766633521584993955 741737649950282377490933)
    ·
      refine ⟨69537904682838972889775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 741737649950282377490933 69537904682838972889775)
      ·
        refine ⟨104306857024258459334663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69537904682838972889775 104306857024258459334663)
        ·
          refine ⟨156460285536387689001995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104306857024258459334663 156460285536387689001995)
          ·
            refine ⟨234690428304581533502993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156460285536387689001995 234690428304581533502993)
            ·
              refine ⟨176017821228436150127245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234690428304581533502993 176017821228436150127245)
              ·
                refine ⟨66006682960663556297717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176017821228436150127245 66006682960663556297717)
                ·
                  refine ⟨6188126527562208402911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66006682960663556297717 6188126527562208402911)
                  ·
                    rfl

theorem cell23_108462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_108462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108462 prefixEnd_108462 := by exact prefixLift 108462
  have htrace : WordTrace (prefixWord ++ tailWord_108462) baseStart_108462 baseEnd_108462 := by
    simpa [prefixWord, tailWord_108462, baseEnd_108462] using wordTrace_append hprefix tailTrace_108462
  have hstable : (prefixWord ++ tailWord_108462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108462).length < 2 ^ (prefixWord ++ tailWord_108462).sum := by decide
  have hdescent : baseEnd_108462 < baseStart_108462 := by decide
  rcases family_descends (prefixWord ++ tailWord_108462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108467 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 8]
def baseStart_108467 : Nat := 118140960795 + 108467 * 2 ^ 59
def prefixEnd_108467 : Nat := 4983230072969 + 3 ^ 40 * 108467 * 2
def baseEnd_108467 : Nat := 6188411794592484007075

theorem tailTrace_108467 : CollatzResearch.WordTrace tailWord_108467 prefixEnd_108467 6188411794592484007075 := by
  unfold tailWord_108467
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956116498050058533883655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2637410998700039022589103 3956116498050058533883655)
  ·
    refine ⟨5934174747075087800825483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956116498050058533883655 5934174747075087800825483)
    ·
      refine ⟨8901262120612631701238225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934174747075087800825483 8901262120612631701238225)
      ·
        refine ⟨6675946590459473775928669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8901262120612631701238225 6675946590459473775928669)
        ·
          refine ⟨2503479971422302665973251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6675946590459473775928669 2503479971422302665973251)
          ·
            refine ⟨3755219957133453998959877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503479971422302665973251 3755219957133453998959877)
            ·
              refine ⟨704103741962522624804977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3755219957133453998959877 704103741962522624804977)
              ·
                refine ⟨528077806471891968603733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704103741962522624804977 528077806471891968603733)
                ·
                  refine ⟨6188411794592484007075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 528077806471891968603733 6188411794592484007075)
                  ·
                    rfl

theorem cell23_108467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 8].length) (baseStart_108467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108467 prefixEnd_108467 := by exact prefixLift 108467
  have htrace : WordTrace (prefixWord ++ tailWord_108467) baseStart_108467 baseEnd_108467 := by
    simpa [prefixWord, tailWord_108467, baseEnd_108467] using wordTrace_append hprefix tailTrace_108467
  have hstable : (prefixWord ++ tailWord_108467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108467).length < 2 ^ (prefixWord ++ tailWord_108467).sum := by decide
  have hdescent : baseEnd_108467 < baseStart_108467 := by decide
  rcases family_descends (prefixWord ++ tailWord_108467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108488 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 1, 4]
def baseStart_108488 : Nat := 118140960795 + 108488 * 2 ^ 59
def prefixEnd_108488 : Nat := 4983230072969 + 3 ^ 40 * 108488 * 2
def baseEnd_108488 : Nat := 18568829748358924633693

theorem tailTrace_108488 : CollatzResearch.WordTrace tailWord_108488 prefixEnd_108488 18568829748358924633693 := by
  unfold tailWord_108488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978441215486989560199059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2637921620649319413598745 1978441215486989560199059)
  ·
    refine ⟨2967661823230484340298589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978441215486989560199059 2967661823230484340298589)
    ·
      refine ⟨1112873183711431627611971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2967661823230484340298589 1112873183711431627611971)
      ·
        refine ⟨1669309775567147441417957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112873183711431627611971 1669309775567147441417957)
        ·
          refine ⟨312995582918840145265867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1669309775567147441417957 312995582918840145265867)
          ·
            refine ⟨469493374378260217898801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312995582918840145265867 469493374378260217898801)
            ·
              refine ⟨352120030783695163424101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469493374378260217898801 352120030783695163424101)
              ·
                refine ⟨66022505771942843142019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352120030783695163424101 66022505771942843142019)
                ·
                  refine ⟨99033758657914264713029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66022505771942843142019 99033758657914264713029)
                  ·
                    refine ⟨18568829748358924633693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99033758657914264713029 18568829748358924633693)
                    ·
                      rfl

theorem cell23_108488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_108488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108488 prefixEnd_108488 := by exact prefixLift 108488
  have htrace : WordTrace (prefixWord ++ tailWord_108488) baseStart_108488 baseEnd_108488 := by
    simpa [prefixWord, tailWord_108488, baseEnd_108488] using wordTrace_append hprefix tailTrace_108488
  have hstable : (prefixWord ++ tailWord_108488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108488).length < 2 ^ (prefixWord ++ tailWord_108488).sum := by decide
  have hdescent : baseEnd_108488 < baseStart_108488 := by decide
  rcases family_descends (prefixWord ++ tailWord_108488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108497 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_108497 : Nat := 118140960795 + 108497 * 2 ^ 59
def prefixEnd_108497 : Nat := 4983230072969 + 3 ^ 40 * 108497 * 2
def baseEnd_108497 : Nat := 18570370190322412896179

theorem tailTrace_108497 : CollatzResearch.WordTrace tailWord_108497 prefixEnd_108497 18570370190322412896179 := by
  unfold tailWord_108497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957210687941373657475745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2638140458627582438317163 3957210687941373657475745)
  ·
    refine ⟨2967908015956030243106809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3957210687941373657475745 2967908015956030243106809)
    ·
      refine ⟨2225931011967022682330107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2967908015956030243106809 2225931011967022682330107)
      ·
        refine ⟨3338896517950534023495161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225931011967022682330107 3338896517950534023495161)
        ·
          refine ⟨2504172388462900517621371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3338896517950534023495161 2504172388462900517621371)
          ·
            refine ⟨3756258582694350776432057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504172388462900517621371 3756258582694350776432057)
            ·
              refine ⟨2817193937020763082324043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756258582694350776432057 2817193937020763082324043)
              ·
                refine ⟨4225790905531144623486065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817193937020763082324043 4225790905531144623486065)
                ·
                  refine ⟨3169343179148358467614549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225790905531144623486065 3169343179148358467614549)
                  ·
                    refine ⟨18570370190322412896179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3169343179148358467614549 18570370190322412896179)
                    ·
                      rfl

theorem cell23_108497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_108497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108497 prefixEnd_108497 := by exact prefixLift 108497
  have htrace : WordTrace (prefixWord ++ tailWord_108497) baseStart_108497 baseEnd_108497 := by
    simpa [prefixWord, tailWord_108497, baseEnd_108497] using wordTrace_append hprefix tailTrace_108497
  have hstable : (prefixWord ++ tailWord_108497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108497).length < 2 ^ (prefixWord ++ tailWord_108497).sum := by decide
  have hdescent : baseEnd_108497 < baseStart_108497 := by decide
  rcases family_descends (prefixWord ++ tailWord_108497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108565 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_108565 : Nat := 118140960795 + 108565 * 2 ^ 59
def prefixEnd_108565 : Nat := 4983230072969 + 3 ^ 40 * 108565 * 2
def baseEnd_108565 : Nat := 18582009085157657546075

theorem tailTrace_108565 : CollatzResearch.WordTrace tailWord_108565 prefixEnd_108565 18582009085157657546075 := by
  unfold tailWord_108565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959690851695021270951149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639793901130014180634099 3959690851695021270951149)
  ·
    refine ⟨1484884069385632976606681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3959690851695021270951149 1484884069385632976606681)
    ·
      refine ⟨1113663052039224732455011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484884069385632976606681 1113663052039224732455011)
      ·
        refine ⟨1670494578058837098682517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113663052039224732455011 1670494578058837098682517)
        ·
          refine ⟨78304433346507989000743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1670494578058837098682517 78304433346507989000743)
          ·
            refine ⟨117456650019761983501115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78304433346507989000743 117456650019761983501115)
            ·
              refine ⟨176184975029642975251673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117456650019761983501115 176184975029642975251673)
              ·
                refine ⟨132138731272232231438755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176184975029642975251673 132138731272232231438755)
                ·
                  refine ⟨198208096908348347158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132138731272232231438755 198208096908348347158133)
                  ·
                    refine ⟨18582009085157657546075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198208096908348347158133 18582009085157657546075)
                    ·
                      rfl

theorem cell23_108565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_108565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108565 prefixEnd_108565 := by exact prefixLift 108565
  have htrace : WordTrace (prefixWord ++ tailWord_108565) baseStart_108565 baseEnd_108565 := by
    simpa [prefixWord, tailWord_108565, baseEnd_108565] using wordTrace_append hprefix tailTrace_108565
  have hstable : (prefixWord ++ tailWord_108565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108565).length < 2 ^ (prefixWord ++ tailWord_108565).sum := by decide
  have hdescent : baseEnd_108565 < baseStart_108565 := by decide
  rcases family_descends (prefixWord ++ tailWord_108565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108568 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_108568 : Nat := 118140960795 + 108568 * 2 ^ 59
def prefixEnd_108568 : Nat := 4983230072969 + 3 ^ 40 * 108568 * 2
def baseEnd_108568 : Nat := 55747567697436460900711

theorem tailTrace_108568 : CollatzResearch.WordTrace tailWord_108568 prefixEnd_108568 55747567697436460900711 := by
  unfold tailWord_108568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979900135342076391655179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2639866847122768522206905 1979900135342076391655179)
  ·
    refine ⟨2969850203013114587482769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1979900135342076391655179 2969850203013114587482769)
    ·
      refine ⟨2227387652259835940612077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2969850203013114587482769 2227387652259835940612077)
      ·
        refine ⟨835270369597438477729529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2227387652259835940612077 835270369597438477729529)
        ·
          refine ⟨626452777198078858297147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835270369597438477729529 626452777198078858297147)
          ·
            refine ⟨939679165797118287445721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626452777198078858297147 939679165797118287445721)
            ·
              refine ⟨704759374347838715584291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939679165797118287445721 704759374347838715584291)
              ·
                refine ⟨1057139061521758073376437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704759374347838715584291 1057139061521758073376437)
                ·
                  refine ⟨99106787017664819379041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1057139061521758073376437 99106787017664819379041)
                  ·
                    refine ⟨74330090263248614534281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99106787017664819379041 74330090263248614534281)
                    ·
                      refine ⟨55747567697436460900711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74330090263248614534281 55747567697436460900711)
                      ·
                        rfl

theorem cell23_108568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_108568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108568 prefixEnd_108568 := by exact prefixLift 108568
  have htrace : WordTrace (prefixWord ++ tailWord_108568) baseStart_108568 baseEnd_108568 := by
    simpa [prefixWord, tailWord_108568, baseEnd_108568] using wordTrace_append hprefix tailTrace_108568
  have hstable : (prefixWord ++ tailWord_108568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108568).length < 2 ^ (prefixWord ++ tailWord_108568).sum := by decide
  have hdescent : baseEnd_108568 < baseStart_108568 := by decide
  rcases family_descends (prefixWord ++ tailWord_108568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108571 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 3]
def baseStart_108571 : Nat := 118140960795 + 108571 * 2 ^ 59
def prefixEnd_108571 : Nat := 4983230072969 + 3 ^ 40 * 108571 * 2
def baseEnd_108571 : Nat := 55749108139399949163197

theorem tailTrace_108571 : CollatzResearch.WordTrace tailWord_108571 prefixEnd_108571 55749108139399949163197 := by
  unfold tailWord_108571
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959909689673284295669567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639939793115522863779711 3959909689673284295669567)
  ·
    refine ⟨5939864534509926443504351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959909689673284295669567 5939864534509926443504351)
    ·
      refine ⟨8909796801764889665256527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5939864534509926443504351 8909796801764889665256527)
      ·
        refine ⟨13364695202647334497884791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8909796801764889665256527 13364695202647334497884791)
        ·
          refine ⟨20047042803971001746827187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364695202647334497884791 20047042803971001746827187)
          ·
            refine ⟨30070564205956502620240781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20047042803971001746827187 30070564205956502620240781)
            ·
              refine ⟨11276461577233688482590293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30070564205956502620240781 11276461577233688482590293)
              ·
                refine ⟨132146034108207286905355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11276461577233688482590293 132146034108207286905355)
                ·
                  refine ⟨198219051162310930358033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132146034108207286905355 198219051162310930358033)
                  ·
                    refine ⟨148664288371733197768525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198219051162310930358033 148664288371733197768525)
                    ·
                      refine ⟨55749108139399949163197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148664288371733197768525 55749108139399949163197)
                      ·
                        rfl

theorem cell23_108571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 3].length) (baseStart_108571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108571 prefixEnd_108571 := by exact prefixLift 108571
  have htrace : WordTrace (prefixWord ++ tailWord_108571) baseStart_108571 baseEnd_108571 := by
    simpa [prefixWord, tailWord_108571, baseEnd_108571] using wordTrace_append hprefix tailTrace_108571
  have hstable : (prefixWord ++ tailWord_108571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108571).length < 2 ^ (prefixWord ++ tailWord_108571).sum := by decide
  have hdescent : baseEnd_108571 < baseStart_108571 := by decide
  rcases family_descends (prefixWord ++ tailWord_108571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108581 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_108581 : Nat := 118140960795 + 108581 * 2 ^ 59
def prefixEnd_108581 : Nat := 4983230072969 + 3 ^ 40 * 108581 * 2
def baseEnd_108581 : Nat := 55754242945944910038151

theorem tailTrace_108581 : CollatzResearch.WordTrace tailWord_108581 prefixEnd_108581 55754242945944910038151 := by
  unfold tailWord_108581
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960274419637056003533597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2640182946424704002355731 3960274419637056003533597)
  ·
    refine ⟨1485102907363896001325099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3960274419637056003533597 1485102907363896001325099)
    ·
      refine ⟨2227654361045844001987649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485102907363896001325099 2227654361045844001987649)
      ·
        refine ⟨1670740770784383001490737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2227654361045844001987649 1670740770784383001490737)
        ·
          refine ⟨1253055578088287251118053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670740770784383001490737 1253055578088287251118053)
          ·
            refine ⟨234947920891553859584635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1253055578088287251118053 234947920891553859584635)
            ·
              refine ⟨352421881337330789376953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234947920891553859584635 352421881337330789376953)
              ·
                refine ⟨264316411002998092032715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352421881337330789376953 264316411002998092032715)
                ·
                  refine ⟨396474616504497138049073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264316411002998092032715 396474616504497138049073)
                  ·
                    refine ⟨297355962378372853536805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396474616504497138049073 297355962378372853536805)
                    ·
                      refine ⟨55754242945944910038151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 297355962378372853536805 55754242945944910038151)
                      ·
                        rfl

theorem cell23_108581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_108581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108581 prefixEnd_108581 := by exact prefixLift 108581
  have htrace : WordTrace (prefixWord ++ tailWord_108581) baseStart_108581 baseEnd_108581 := by
    simpa [prefixWord, tailWord_108581, baseEnd_108581] using wordTrace_append hprefix tailTrace_108581
  have hstable : (prefixWord ++ tailWord_108581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108581).length < 2 ^ (prefixWord ++ tailWord_108581).sum := by decide
  have hdescent : baseEnd_108581 < baseStart_108581 := by decide
  rcases family_descends (prefixWord ++ tailWord_108581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108596 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_108596 : Nat := 118140960795 + 108596 * 2 ^ 59
def prefixEnd_108596 : Nat := 4983230072969 + 3 ^ 40 * 108596 * 2
def baseEnd_108596 : Nat := 55761945155762351350583

theorem tailTrace_108596 : CollatzResearch.WordTrace tailWord_108596 prefixEnd_108596 55761945155762351350583 := by
  unfold tailWord_108596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980410757291356782664821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2640547676388475710219761 1980410757291356782664821)
  ·
    refine ⟨185663508496064698374827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1980410757291356782664821 185663508496064698374827)
    ·
      refine ⟨278495262744097047562241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185663508496064698374827 278495262744097047562241)
      ·
        refine ⟨208871447058072785671681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278495262744097047562241 208871447058072785671681)
        ·
          refine ⟨156653585293554589253761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208871447058072785671681 156653585293554589253761)
          ·
            refine ⟨117490188970165941940321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156653585293554589253761 117490188970165941940321)
            ·
              refine ⟨88117641727624456455241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117490188970165941940321 88117641727624456455241)
              ·
                refine ⟨66088231295718342341431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88117641727624456455241 66088231295718342341431)
                ·
                  refine ⟨99132346943577513512147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66088231295718342341431 99132346943577513512147)
                  ·
                    refine ⟨148698520415366270268221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99132346943577513512147 148698520415366270268221)
                    ·
                      refine ⟨55761945155762351350583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148698520415366270268221 55761945155762351350583)
                      ·
                        rfl

theorem cell23_108596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_108596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108596 prefixEnd_108596 := by exact prefixLift 108596
  have htrace : WordTrace (prefixWord ++ tailWord_108596) baseStart_108596 baseEnd_108596 := by
    simpa [prefixWord, tailWord_108596, baseEnd_108596] using wordTrace_append hprefix tailTrace_108596
  have hstable : (prefixWord ++ tailWord_108596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108596).length < 2 ^ (prefixWord ++ tailWord_108596).sum := by decide
  have hdescent : baseEnd_108596 < baseStart_108596 := by decide
  rcases family_descends (prefixWord ++ tailWord_108596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108604 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_108604 : Nat := 118140960795 + 108604 * 2 ^ 59
def prefixEnd_108604 : Nat := 4983230072969 + 3 ^ 40 * 108604 * 2
def baseEnd_108604 : Nat := 18588684333666106683515

theorem tailTrace_108604 : CollatzResearch.WordTrace tailWord_108604 prefixEnd_108604 18588684333666106683515 := by
  unfold tailWord_108604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980556649276865465810433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2640742199035820621080577 1980556649276865465810433)
  ·
    refine ⟨1485417486957649099357825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1980556649276865465810433 1485417486957649099357825)
    ·
      refine ⟨1114063115218236824518369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485417486957649099357825 1114063115218236824518369)
      ·
        refine ⟨835547336413677618388777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114063115218236824518369 835547336413677618388777)
        ·
          refine ⟨626660502310258213791583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835547336413677618388777 626660502310258213791583)
          ·
            refine ⟨939990753465387320687375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626660502310258213791583 939990753465387320687375)
            ·
              refine ⟨1409986130198080981031063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939990753465387320687375 1409986130198080981031063)
              ·
                refine ⟨2114979195297121471546595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409986130198080981031063 2114979195297121471546595)
                ·
                  refine ⟨3172468792945682207319893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114979195297121471546595 3172468792945682207319893)
                  ·
                    refine ⟨18588684333666106683515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3172468792945682207319893 18588684333666106683515)
                    ·
                      rfl

theorem cell23_108604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_108604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108604 prefixEnd_108604 := by exact prefixLift 108604
  have htrace : WordTrace (prefixWord ++ tailWord_108604) baseStart_108604 baseEnd_108604 := by
    simpa [prefixWord, tailWord_108604, baseEnd_108604] using wordTrace_append hprefix tailTrace_108604
  have hstable : (prefixWord ++ tailWord_108604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108604).length < 2 ^ (prefixWord ++ tailWord_108604).sum := by decide
  have hdescent : baseEnd_108604 < baseStart_108604 := by decide
  rcases family_descends (prefixWord ++ tailWord_108604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108621 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_108621 : Nat := 118140960795 + 108621 * 2 ^ 59
def prefixEnd_108621 : Nat := 4983230072969 + 3 ^ 40 * 108621 * 2
def baseEnd_108621 : Nat := 18591594057374917845989

theorem tailTrace_108621 : CollatzResearch.WordTrace tailWord_108621 prefixEnd_108621 18591594057374917845989 := by
  unfold tailWord_108621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961733339492142834989717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2641155559661428556659811 3961733339492142834989717)
  ·
    refine ⟨185706250288694195390143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3961733339492142834989717 185706250288694195390143)
    ·
      refine ⟨278559375433041293085215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185706250288694195390143 278559375433041293085215)
      ·
        refine ⟨417839063149561939627823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278559375433041293085215 417839063149561939627823)
        ·
          refine ⟨626758594724342909441735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417839063149561939627823 626758594724342909441735)
          ·
            refine ⟨940137892086514364162603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626758594724342909441735 940137892086514364162603)
            ·
              refine ⟨1410206838129771546243905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940137892086514364162603 1410206838129771546243905)
              ·
                refine ⟨1057655128597328659682929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410206838129771546243905 1057655128597328659682929)
                ·
                  refine ⟨793241346447996494762197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057655128597328659682929 793241346447996494762197)
                  ·
                    refine ⟨18591594057374917845989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 793241346447996494762197 18591594057374917845989)
                    ·
                      rfl

theorem cell23_108621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_108621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108621 prefixEnd_108621 := by exact prefixLift 108621
  have htrace : WordTrace (prefixWord ++ tailWord_108621) baseStart_108621 baseEnd_108621 := by
    simpa [prefixWord, tailWord_108621, baseEnd_108621] using wordTrace_append hprefix tailTrace_108621
  have hstable : (prefixWord ++ tailWord_108621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108621).length < 2 ^ (prefixWord ++ tailWord_108621).sum := by decide
  have hdescent : baseEnd_108621 < baseStart_108621 := by decide
  rcases family_descends (prefixWord ++ tailWord_108621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108634 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_108634 : Nat := 118140960795 + 108634 * 2 ^ 59
def prefixEnd_108634 : Nat := 4983230072969 + 3 ^ 40 * 108634 * 2
def baseEnd_108634 : Nat := 18593819140211067558469

theorem tailTrace_108634 : CollatzResearch.WordTrace tailWord_108634 prefixEnd_108634 18593819140211067558469 := by
  unfold tailWord_108634
  simp only [CollatzResearch.WordTrace]
  refine ⟨990551872111261513803239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2641471658963364036808637 990551872111261513803239)
  ·
    refine ⟨1485827808166892270704859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990551872111261513803239 1485827808166892270704859)
    ·
      refine ⟨2228741712250338406057289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485827808166892270704859 2228741712250338406057289)
      ·
        refine ⟨1671556284187753804542967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2228741712250338406057289 1671556284187753804542967)
        ·
          refine ⟨2507334426281630706814451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671556284187753804542967 2507334426281630706814451)
          ·
            refine ⟨3761001639422446060221677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507334426281630706814451 3761001639422446060221677)
            ·
              refine ⟨1410375614783417272583129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3761001639422446060221677 1410375614783417272583129)
              ·
                refine ⟨1057781711087562954437347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410375614783417272583129 1057781711087562954437347)
                ·
                  refine ⟨1586672566631344431656021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057781711087562954437347 1586672566631344431656021)
                  ·
                    refine ⟨18593819140211067558469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1586672566631344431656021 18593819140211067558469)
                    ·
                      rfl

theorem cell23_108634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_108634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108634 prefixEnd_108634 := by exact prefixLift 108634
  have htrace : WordTrace (prefixWord ++ tailWord_108634) baseStart_108634 baseEnd_108634 := by
    simpa [prefixWord, tailWord_108634, baseEnd_108634] using wordTrace_append hprefix tailTrace_108634
  have hstable : (prefixWord ++ tailWord_108634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108634).length < 2 ^ (prefixWord ++ tailWord_108634).sum := by decide
  have hdescent : baseEnd_108634 < baseStart_108634 := by decide
  rcases family_descends (prefixWord ++ tailWord_108634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108645 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_108645 : Nat := 118140960795 + 108645 * 2 ^ 59
def prefixEnd_108645 : Nat := 4983230072969 + 3 ^ 40 * 108645 * 2
def baseEnd_108645 : Nat := 55787105707832659637857

theorem tailTrace_108645 : CollatzResearch.WordTrace tailWord_108645 prefixEnd_108645 55787105707832659637857 := by
  unfold tailWord_108645
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962608691405194933863389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2641739127603463289242259 3962608691405194933863389)
  ·
    refine ⟨1485978259276948100198771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3962608691405194933863389 1485978259276948100198771)
    ·
      refine ⟨2228967388915422150298157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485978259276948100198771 2228967388915422150298157)
      ·
        refine ⟨835862770843283306361809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2228967388915422150298157 835862770843283306361809)
        ·
          refine ⟨626897078132462479771357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835862770843283306361809 626897078132462479771357)
          ·
            refine ⟨235086404299673429914259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626897078132462479771357 235086404299673429914259)
            ·
              refine ⟨352629606449510144871389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235086404299673429914259 352629606449510144871389)
              ·
                refine ⟨132236102418566304326771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352629606449510144871389 132236102418566304326771)
                ·
                  refine ⟨198354153627849456490157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132236102418566304326771 198354153627849456490157)
                  ·
                    refine ⟨74382807610443546183809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198354153627849456490157 74382807610443546183809)
                    ·
                      refine ⟨55787105707832659637857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74382807610443546183809 55787105707832659637857)
                      ·
                        rfl

theorem cell23_108645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_108645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108645 prefixEnd_108645 := by exact prefixLift 108645
  have htrace : WordTrace (prefixWord ++ tailWord_108645) baseStart_108645 baseEnd_108645 := by
    simpa [prefixWord, tailWord_108645, baseEnd_108645] using wordTrace_append hprefix tailTrace_108645
  have hstable : (prefixWord ++ tailWord_108645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108645).length < 2 ^ (prefixWord ++ tailWord_108645).sum := by decide
  have hdescent : baseEnd_108645 < baseStart_108645 := by decide
  rcases family_descends (prefixWord ++ tailWord_108645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108675 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 1, 4, 2]
def baseStart_108675 : Nat := 118140960795 + 108675 * 2 ^ 59
def prefixEnd_108675 : Nat := 4983230072969 + 3 ^ 40 * 108675 * 2
def baseEnd_108675 : Nat := 55802510127467542262719

theorem tailTrace_108675 : CollatzResearch.WordTrace tailWord_108675 prefixEnd_108675 55802510127467542262719 := by
  unfold tailWord_108675
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963702881296510057455479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2642468587531006704970319 3963702881296510057455479)
  ·
    refine ⟨5945554321944765086183219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3963702881296510057455479 5945554321944765086183219)
    ·
      refine ⟨8918331482917147629274829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945554321944765086183219 8918331482917147629274829)
      ·
        refine ⟨3344374306093930360978061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8918331482917147629274829 3344374306093930360978061)
        ·
          refine ⟨1254140364785223885366773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3344374306093930360978061 1254140364785223885366773)
          ·
            refine ⟨117575659198614739253135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1254140364785223885366773 117575659198614739253135)
            ·
              refine ⟨176363488797922108879703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117575659198614739253135 176363488797922108879703)
              ·
                refine ⟨264545233196883163319555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176363488797922108879703 264545233196883163319555)
                ·
                  refine ⟨396817849795324744979333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264545233196883163319555 396817849795324744979333)
                  ·
                    refine ⟨74403346836623389683625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396817849795324744979333 74403346836623389683625)
                    ·
                      refine ⟨55802510127467542262719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74403346836623389683625 55802510127467542262719)
                      ·
                        rfl

theorem cell23_108675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_108675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108675 prefixEnd_108675 := by exact prefixLift 108675
  have htrace : WordTrace (prefixWord ++ tailWord_108675) baseStart_108675 baseEnd_108675 := by
    simpa [prefixWord, tailWord_108675, baseEnd_108675] using wordTrace_append hprefix tailTrace_108675
  have hstable : (prefixWord ++ tailWord_108675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108675).length < 2 ^ (prefixWord ++ tailWord_108675).sum := by decide
  have hdescent : baseEnd_108675 < baseStart_108675 := by decide
  rcases family_descends (prefixWord ++ tailWord_108675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108731 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4]
def baseStart_108731 : Nat := 118140960795 + 108731 * 2 ^ 59
def prefixEnd_108731 : Nat := 4983230072969 + 3 ^ 40 * 108731 * 2
def baseEnd_108731 : Nat := 55831265044119323162461

theorem tailTrace_108731 : CollatzResearch.WordTrace tailWord_108731 prefixEnd_108731 55831265044119323162461 := by
  unfold tailWord_108731
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965745369093631621494047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2643830246062421080996031 3965745369093631621494047)
  ·
    refine ⟨5948618053640447432241071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965745369093631621494047 5948618053640447432241071)
    ·
      refine ⟨8922927080460671148361607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948618053640447432241071 8922927080460671148361607)
      ·
        refine ⟨13384390620691006722542411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922927080460671148361607 13384390620691006722542411)
        ·
          refine ⟨20076585931036510083813617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384390620691006722542411 20076585931036510083813617)
          ·
            refine ⟨15057439448277382562860213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20076585931036510083813617 15057439448277382562860213)
            ·
              refine ⟨1411634948276004615268145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15057439448277382562860213 1411634948276004615268145)
              ·
                refine ⟨1058726211207003461451109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411634948276004615268145 1058726211207003461451109)
                ·
                  refine ⟨198511164601313149022083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058726211207003461451109 198511164601313149022083)
                  ·
                    refine ⟨297766746901969723533125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198511164601313149022083 297766746901969723533125)
                    ·
                      refine ⟨55831265044119323162461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 297766746901969723533125 55831265044119323162461)
                      ·
                        rfl

theorem cell23_108731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4].length) (baseStart_108731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108731 prefixEnd_108731 := by exact prefixLift 108731
  have htrace : WordTrace (prefixWord ++ tailWord_108731) baseStart_108731 baseEnd_108731 := by
    simpa [prefixWord, tailWord_108731, baseEnd_108731] using wordTrace_append hprefix tailTrace_108731
  have hstable : (prefixWord ++ tailWord_108731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108731).length < 2 ^ (prefixWord ++ tailWord_108731).sum := by decide
  have hdescent : baseEnd_108731 < baseStart_108731 := by decide
  rcases family_descends (prefixWord ++ tailWord_108731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108765 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_108765 : Nat := 118140960795 + 108765 * 2 ^ 59
def prefixEnd_108765 : Nat := 4983230072969 + 3 ^ 40 * 108765 * 2
def baseEnd_108765 : Nat := 55848723386372190137305

theorem tailTrace_108765 : CollatzResearch.WordTrace tailWord_108765 prefixEnd_108765 55848723386372190137305 := by
  unfold tailWord_108765
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966985450970455428231749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2644656967313636952154499 3966985450970455428231749)
  ·
    refine ⟨743809772056960392793453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3966985450970455428231749 743809772056960392793453)
    ·
      refine ⟨278928664521360147297545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 743809772056960392793453 278928664521360147297545)
      ·
        refine ⟨209196498391020110473159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278928664521360147297545 209196498391020110473159)
        ·
          refine ⟨313794747586530165709739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209196498391020110473159 313794747586530165709739)
          ·
            refine ⟨470692121379795248564609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313794747586530165709739 470692121379795248564609)
            ·
              refine ⟨353019091034846436423457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470692121379795248564609 353019091034846436423457)
              ·
                refine ⟨264764318276134827317593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353019091034846436423457 264764318276134827317593)
                ·
                  refine ⟨198573238707101120488195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264764318276134827317593 198573238707101120488195)
                  ·
                    refine ⟨297859858060651680732293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198573238707101120488195 297859858060651680732293)
                    ·
                      refine ⟨55848723386372190137305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 297859858060651680732293 55848723386372190137305)
                      ·
                        rfl

theorem cell23_108765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_108765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108765 prefixEnd_108765 := by exact prefixLift 108765
  have htrace : WordTrace (prefixWord ++ tailWord_108765) baseStart_108765 baseEnd_108765 := by
    simpa [prefixWord, tailWord_108765, baseEnd_108765] using wordTrace_append hprefix tailTrace_108765
  have hstable : (prefixWord ++ tailWord_108765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108765).length < 2 ^ (prefixWord ++ tailWord_108765).sum := by decide
  have hdescent : baseEnd_108765 < baseStart_108765 := by decide
  rcases family_descends (prefixWord ++ tailWord_108765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108768 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_108768 : Nat := 118140960795 + 108768 * 2 ^ 59
def prefixEnd_108768 : Nat := 4983230072969 + 3 ^ 40 * 108768 * 2
def baseEnd_108768 : Nat := 55850263828335678399791

theorem tailTrace_108768 : CollatzResearch.WordTrace tailWord_108768 prefixEnd_108768 55850263828335678399791 := by
  unfold tailWord_108768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983547434979793470295479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2644729913306391293727305 1983547434979793470295479)
  ·
    refine ⟨2975321152469690205443219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983547434979793470295479 2975321152469690205443219)
    ·
      refine ⟨4462981728704535308164829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975321152469690205443219 4462981728704535308164829)
      ·
        refine ⟨1673618148264200740561811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4462981728704535308164829 1673618148264200740561811)
        ·
          refine ⟨2510427222396301110842717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673618148264200740561811 2510427222396301110842717)
          ·
            refine ⟨941410208398612916566019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2510427222396301110842717 941410208398612916566019)
            ·
              refine ⟨1412115312597919374849029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941410208398612916566019 1412115312597919374849029)
              ·
                refine ⟨264771621112109882784193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1412115312597919374849029 264771621112109882784193)
                ·
                  refine ⟨198578715834082412088145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264771621112109882784193 198578715834082412088145)
                  ·
                    refine ⟨148934036875561809066109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198578715834082412088145 148934036875561809066109)
                    ·
                      refine ⟨55850263828335678399791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148934036875561809066109 55850263828335678399791)
                      ·
                        rfl

theorem cell23_108768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_108768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108768 prefixEnd_108768 := by exact prefixLift 108768
  have htrace : WordTrace (prefixWord ++ tailWord_108768) baseStart_108768 baseEnd_108768 := by
    simpa [prefixWord, tailWord_108768, baseEnd_108768] using wordTrace_append hprefix tailTrace_108768
  have hstable : (prefixWord ++ tailWord_108768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108768).length < 2 ^ (prefixWord ++ tailWord_108768).sum := by decide
  have hdescent : baseEnd_108768 < baseStart_108768 := by decide
  rcases family_descends (prefixWord ++ tailWord_108768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108802 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_108802 : Nat := 118140960795 + 108802 * 2 ^ 59
def prefixEnd_108802 : Nat := 4983230072969 + 3 ^ 40 * 108802 * 2
def baseEnd_108802 : Nat := 55867722170588545374635

theorem tailTrace_108802 : CollatzResearch.WordTrace tailWord_108802 prefixEnd_108802 55867722170588545374635 := by
  unfold tailWord_108802
  simp only [CollatzResearch.WordTrace]
  refine ⟨992083737959102686832165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2645556634557607164885773 992083737959102686832165)
  ·
    refine ⟨186015700867331753781031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 992083737959102686832165 186015700867331753781031)
    ·
      refine ⟨279023551300997630671547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186015700867331753781031 279023551300997630671547)
      ·
        refine ⟨418535326951496446007321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279023551300997630671547 418535326951496446007321)
        ·
          refine ⟨313901495213622334505491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418535326951496446007321 313901495213622334505491)
          ·
            refine ⟨470852242820433501758237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313901495213622334505491 470852242820433501758237)
            ·
              refine ⟨176569591057662563159339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470852242820433501758237 176569591057662563159339)
              ·
                refine ⟨264854386586493844739009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176569591057662563159339 264854386586493844739009)
                ·
                  refine ⟨198640789939870383554257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264854386586493844739009 198640789939870383554257)
                  ·
                    refine ⟨148980592454902787665693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198640789939870383554257 148980592454902787665693)
                    ·
                      refine ⟨55867722170588545374635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 148980592454902787665693 55867722170588545374635)
                      ·
                        rfl

theorem cell23_108802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_108802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108802 prefixEnd_108802 := by exact prefixLift 108802
  have htrace : WordTrace (prefixWord ++ tailWord_108802) baseStart_108802 baseEnd_108802 := by
    simpa [prefixWord, tailWord_108802, baseEnd_108802] using wordTrace_append hprefix tailTrace_108802
  have hstable : (prefixWord ++ tailWord_108802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108802).length < 2 ^ (prefixWord ++ tailWord_108802).sum := by decide
  have hdescent : baseEnd_108802 < baseStart_108802 := by decide
  rcases family_descends (prefixWord ++ tailWord_108802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108832 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3]
def baseStart_108832 : Nat := 118140960795 + 108832 * 2 ^ 59
def prefixEnd_108832 : Nat := 4983230072969 + 3 ^ 40 * 108832 * 2
def baseEnd_108832 : Nat := 55883126590223427999497

theorem tailTrace_108832 : CollatzResearch.WordTrace tailWord_108832 prefixEnd_108832 55883126590223427999497 := by
  unfold tailWord_108832
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984714570863862935460375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2646286094485150580613833 1984714570863862935460375)
  ·
    refine ⟨2977071856295794403190563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1984714570863862935460375 2977071856295794403190563)
    ·
      refine ⟨4465607784443691604785845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977071856295794403190563 4465607784443691604785845)
      ·
        refine ⟨418650729791596087948673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4465607784443691604785845 418650729791596087948673)
        ·
          refine ⟨313988047343697065961505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418650729791596087948673 313988047343697065961505)
          ·
            refine ⟨235491035507772799471129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313988047343697065961505 235491035507772799471129)
            ·
              refine ⟨176618276630829599603347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235491035507772799471129 176618276630829599603347)
              ·
                refine ⟨264927414946244399405021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176618276630829599603347 264927414946244399405021)
                ·
                  refine ⟨99347780604841649776883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264927414946244399405021 99347780604841649776883)
                  ·
                    refine ⟨149021670907262474665325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99347780604841649776883 149021670907262474665325)
                    ·
                      refine ⟨55883126590223427999497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 149021670907262474665325 55883126590223427999497)
                      ·
                        rfl

theorem cell23_108832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_108832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108832 prefixEnd_108832 := by exact prefixLift 108832
  have htrace : WordTrace (prefixWord ++ tailWord_108832) baseStart_108832 baseEnd_108832 := by
    simpa [prefixWord, tailWord_108832, baseEnd_108832] using wordTrace_append hprefix tailTrace_108832
  have hstable : (prefixWord ++ tailWord_108832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108832).length < 2 ^ (prefixWord ++ tailWord_108832).sum := by decide
  have hdescent : baseEnd_108832 < baseStart_108832 := by decide
  rcases family_descends (prefixWord ++ tailWord_108832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108852 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_108852 : Nat := 118140960795 + 108852 * 2 ^ 59
def prefixEnd_108852 : Nat := 4983230072969 + 3 ^ 40 * 108852 * 2
def baseEnd_108852 : Nat := 18631132067771116583135

theorem tailTrace_108852 : CollatzResearch.WordTrace tailWord_108852 prefixEnd_108852 18631132067771116583135 := by
  unfold tailWord_108852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985079300827634643324405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2646772401103512857765873 1985079300827634643324405)
  ·
    refine ⟨186101184452590747811663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1985079300827634643324405 186101184452590747811663)
    ·
      refine ⟨279151776678886121717495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186101184452590747811663 279151776678886121717495)
      ·
        refine ⟨418727665018329182576243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279151776678886121717495 418727665018329182576243)
        ·
          refine ⟨628091497527493773864365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418727665018329182576243 628091497527493773864365)
          ·
            refine ⟨235534311572810165199137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628091497527493773864365 235534311572810165199137)
            ·
              refine ⟨176650733679607623899353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235534311572810165199137 176650733679607623899353)
              ·
                refine ⟨132488050259705717924515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176650733679607623899353 132488050259705717924515)
                ·
                  refine ⟨198732075389558576886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132488050259705717924515 198732075389558576886773)
                  ·
                    refine ⟨18631132067771116583135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198732075389558576886773 18631132067771116583135)
                    ·
                      rfl

theorem cell23_108852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_108852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108852 prefixEnd_108852 := by exact prefixLift 108852
  have htrace : WordTrace (prefixWord ++ tailWord_108852) baseStart_108852 baseEnd_108852 := by
    simpa [prefixWord, tailWord_108852, baseEnd_108852] using wordTrace_append hprefix tailTrace_108852
  have hstable : (prefixWord ++ tailWord_108852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108852).length < 2 ^ (prefixWord ++ tailWord_108852).sum := by decide
  have hdescent : baseEnd_108852 < baseStart_108852 := by decide
  rcases family_descends (prefixWord ++ tailWord_108852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108888 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_108888 : Nat := 118140960795 + 108888 * 2 ^ 59
def prefixEnd_108888 : Nat := 4983230072969 + 3 ^ 40 * 108888 * 2
def baseEnd_108888 : Nat := 55911881506875208899239

theorem tailTrace_108888 : CollatzResearch.WordTrace tailWord_108888 prefixEnd_108888 55911881506875208899239 := by
  unfold tailWord_108888
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985735814762423717479659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2647647753016564956639545 1985735814762423717479659)
  ·
    refine ⟨2978603722143635576219489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1985735814762423717479659 2978603722143635576219489)
    ·
      refine ⟨2233952791607726682164617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2978603722143635576219489 2233952791607726682164617)
      ·
        refine ⟨1675464593705795011623463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233952791607726682164617 1675464593705795011623463)
        ·
          refine ⟨2513196890558692517435195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675464593705795011623463 2513196890558692517435195)
          ·
            refine ⟨3769795335838038776152793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513196890558692517435195 3769795335838038776152793)
            ·
              refine ⟨2827346501878529082114595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769795335838038776152793 2827346501878529082114595)
              ·
                refine ⟨4241019752817793623171893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827346501878529082114595 4241019752817793623171893)
                ·
                  refine ⟨397595601826668152172365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4241019752817793623171893 397595601826668152172365)
                  ·
                    refine ⟨149098350685000557064637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397595601826668152172365 149098350685000557064637)
                    ·
                      refine ⟨55911881506875208899239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 149098350685000557064637 55911881506875208899239)
                      ·
                        rfl

theorem cell23_108888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_108888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108888 prefixEnd_108888 := by exact prefixLift 108888
  have htrace : WordTrace (prefixWord ++ tailWord_108888) baseStart_108888 baseEnd_108888 := by
    simpa [prefixWord, tailWord_108888, baseEnd_108888] using wordTrace_append hprefix tailTrace_108888
  have hstable : (prefixWord ++ tailWord_108888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108888).length < 2 ^ (prefixWord ++ tailWord_108888).sum := by decide
  have hdescent : baseEnd_108888 < baseStart_108888 := by decide
  rcases family_descends (prefixWord ++ tailWord_108888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 3, 3, 2]
def baseStart_108915 : Nat := 118140960795 + 108915 * 2 ^ 59
def prefixEnd_108915 : Nat := 4983230072969 + 3 ^ 40 * 108915 * 2
def baseEnd_108915 : Nat := 55925745484546603261615

theorem tailTrace_108915 : CollatzResearch.WordTrace tailWord_108915 prefixEnd_108915 55925745484546603261615 := by
  unfold tailWord_108915
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972456400427031046192199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2648304266951354030794799 3972456400427031046192199)
  ·
    refine ⟨5958684600640546569288299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3972456400427031046192199 5958684600640546569288299)
    ·
      refine ⟨8938026900960819853932449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958684600640546569288299 8938026900960819853932449)
      ·
        refine ⟨6703520175720614890449337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8938026900960819853932449 6703520175720614890449337)
        ·
          refine ⟨5027640131790461167837003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6703520175720614890449337 5027640131790461167837003)
          ·
            refine ⟨7541460197685691751755505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027640131790461167837003 7541460197685691751755505)
            ·
              refine ⟨5656095148264268813816629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7541460197685691751755505 5656095148264268813816629)
              ·
                refine ⟨530258920149775201295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5656095148264268813816629 530258920149775201295309)
                ·
                  refine ⟨198847095056165700485741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530258920149775201295309 198847095056165700485741)
                  ·
                    refine ⟨74567660646062137682153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198847095056165700485741 74567660646062137682153)
                    ·
                      refine ⟨55925745484546603261615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74567660646062137682153 55925745484546603261615)
                      ·
                        rfl

theorem cell23_108915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3, 2].length) (baseStart_108915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108915 prefixEnd_108915 := by exact prefixLift 108915
  have htrace : WordTrace (prefixWord ++ tailWord_108915) baseStart_108915 baseEnd_108915 := by
    simpa [prefixWord, tailWord_108915, baseEnd_108915] using wordTrace_append hprefix tailTrace_108915
  have hstable : (prefixWord ++ tailWord_108915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108915).length < 2 ^ (prefixWord ++ tailWord_108915).sum := by decide
  have hdescent : baseEnd_108915 < baseStart_108915 := by decide
  rcases family_descends (prefixWord ++ tailWord_108915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108996 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_108996 : Nat := 118140960795 + 108996 * 2 ^ 59
def prefixEnd_108996 : Nat := 4983230072969 + 3 ^ 40 * 108996 * 2
def baseEnd_108996 : Nat := 55967337417560786348743

theorem tailTrace_108996 : CollatzResearch.WordTrace tailWord_108996 prefixEnd_108996 55967337417560786348743 := by
  unfold tailWord_108996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987705356566790939945421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2650273808755721253260561 1987705356566790939945421)
  ·
    refine ⟨745389508712546602479533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1987705356566790939945421 745389508712546602479533)
    ·
      refine ⟨279521065767204975929825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 745389508712546602479533 279521065767204975929825)
      ·
        refine ⟨209640799325403731947369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279521065767204975929825 209640799325403731947369)
        ·
          refine ⟨157230599494052798960527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209640799325403731947369 157230599494052798960527)
          ·
            refine ⟨235845899241079198440791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157230599494052798960527 235845899241079198440791)
            ·
              refine ⟨353768848861618797661187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235845899241079198440791 353768848861618797661187)
              ·
                refine ⟨530653273292428196491781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353768848861618797661187 530653273292428196491781)
                ·
                  refine ⟨99497488742330286842209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530653273292428196491781 99497488742330286842209)
                  ·
                    refine ⟨74623116556747715131657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99497488742330286842209 74623116556747715131657)
                    ·
                      refine ⟨55967337417560786348743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74623116556747715131657 55967337417560786348743)
                      ·
                        rfl

theorem cell23_108996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_108996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_108996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_108996 prefixEnd_108996 := by exact prefixLift 108996
  have htrace : WordTrace (prefixWord ++ tailWord_108996) baseStart_108996 baseEnd_108996 := by
    simpa [prefixWord, tailWord_108996, baseEnd_108996] using wordTrace_append hprefix tailTrace_108996
  have hstable : (prefixWord ++ tailWord_108996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108996).length < 2 ^ (prefixWord ++ tailWord_108996).sum := by decide
  have hdescent : baseEnd_108996 < baseStart_108996 := by decide
  rcases family_descends (prefixWord ++ tailWord_108996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109012 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_109012 : Nat := 118140960795 + 109012 * 2 ^ 59
def prefixEnd_109012 : Nat := 4983230072969 + 3 ^ 40 * 109012 * 2
def baseEnd_109012 : Nat := 55975553108032723748669

theorem tailTrace_109012 : CollatzResearch.WordTrace tailWord_109012 prefixEnd_109012 55975553108032723748669 := by
  unfold tailWord_109012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987997140537808306236645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2650662854050411074982193 1987997140537808306236645)
  ·
    refine ⟨372749463850839057419371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1987997140537808306236645 372749463850839057419371)
    ·
      refine ⟨559124195776258586129057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372749463850839057419371 559124195776258586129057)
      ·
        refine ⟨419343146832193939596793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559124195776258586129057 419343146832193939596793)
        ·
          refine ⟨314507360124145454697595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419343146832193939596793 314507360124145454697595)
          ·
            refine ⟨471761040186218182046393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314507360124145454697595 471761040186218182046393)
            ·
              refine ⟨353820780139663636534795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471761040186218182046393 353820780139663636534795)
              ·
                refine ⟨530731170209495454802193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353820780139663636534795 530731170209495454802193)
                ·
                  refine ⟨398048377657121591101645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530731170209495454802193 398048377657121591101645)
                  ·
                    refine ⟨149268141621420596663117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398048377657121591101645 149268141621420596663117)
                    ·
                      refine ⟨55975553108032723748669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 149268141621420596663117 55975553108032723748669)
                      ·
                        rfl

theorem cell23_109012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_109012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109012 prefixEnd_109012 := by exact prefixLift 109012
  have htrace : WordTrace (prefixWord ++ tailWord_109012) baseStart_109012 baseEnd_109012 := by
    simpa [prefixWord, tailWord_109012, baseEnd_109012] using wordTrace_append hprefix tailTrace_109012
  have hstable : (prefixWord ++ tailWord_109012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109012).length < 2 ^ (prefixWord ++ tailWord_109012).sum := by decide
  have hdescent : baseEnd_109012 < baseStart_109012 := by decide
  rcases family_descends (prefixWord ++ tailWord_109012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109035 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4]
def baseStart_109035 : Nat := 118140960795 + 109035 * 2 ^ 59
def prefixEnd_109035 : Nat := 4983230072969 + 3 ^ 40 * 109035 * 2
def baseEnd_109035 : Nat := 55987363163086133761063

theorem tailTrace_109035 : CollatzResearch.WordTrace tailWord_109035 prefixEnd_109035 55987363163086133761063 := by
  unfold tailWord_109035
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976833159992291540560559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651222106661527693707039 3976833159992291540560559)
  ·
    refine ⟨5965249739988437310840839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976833159992291540560559 5965249739988437310840839)
    ·
      refine ⟨8947874609982655966261259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5965249739988437310840839 8947874609982655966261259)
      ·
        refine ⟨13421811914973983949391889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947874609982655966261259 13421811914973983949391889)
        ·
          refine ⟨10066358936230487962043917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13421811914973983949391889 10066358936230487962043917)
          ·
            refine ⟨3774884601086432985766469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10066358936230487962043917 3774884601086432985766469)
            ·
              refine ⟨707790862703706184831213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3774884601086432985766469 707790862703706184831213)
              ·
                refine ⟨265421573513889819311705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707790862703706184831213 265421573513889819311705)
                ·
                  refine ⟨199066180135417364483779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265421573513889819311705 199066180135417364483779)
                  ·
                    refine ⟨298599270203126046725669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199066180135417364483779 298599270203126046725669)
                    ·
                      refine ⟨55987363163086133761063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 298599270203126046725669 55987363163086133761063)
                      ·
                        rfl

theorem cell23_109035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4].length) (baseStart_109035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109035 prefixEnd_109035 := by exact prefixLift 109035
  have htrace : WordTrace (prefixWord ++ tailWord_109035) baseStart_109035 baseEnd_109035 := by
    simpa [prefixWord, tailWord_109035, baseEnd_109035] using wordTrace_append hprefix tailTrace_109035
  have hstable : (prefixWord ++ tailWord_109035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109035).length < 2 ^ (prefixWord ++ tailWord_109035).sum := by decide
  have hdescent : baseEnd_109035 < baseStart_109035 := by decide
  rcases family_descends (prefixWord ++ tailWord_109035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109075 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 6]
def baseStart_109075 : Nat := 118140960795 + 109075 * 2 ^ 59
def prefixEnd_109075 : Nat := 4983230072969 + 3 ^ 40 * 109075 * 2
def baseEnd_109075 : Nat := 6223100265473997473431

theorem tailTrace_109075 : CollatzResearch.WordTrace tailWord_109075 prefixEnd_109075 6223100265473997473431 := by
  unfold tailWord_109075
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978292079847378372016679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2652194719898252248011119 3978292079847378372016679)
  ·
    refine ⟨5967438119771067558025019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978292079847378372016679 5967438119771067558025019)
    ·
      refine ⟨8951157179656601337037529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5967438119771067558025019 8951157179656601337037529)
      ·
        refine ⟨6713367884742451002778147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8951157179656601337037529 6713367884742451002778147)
        ·
          refine ⟨10070051827113676504167221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713367884742451002778147 10070051827113676504167221)
          ·
            refine ⟨944067358791907172265677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10070051827113676504167221 944067358791907172265677)
            ·
              refine ⟨354025259546965189599629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 944067358791907172265677 354025259546965189599629)
              ·
                refine ⟨132759472330111946099861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354025259546965189599629 132759472330111946099861)
                ·
                  refine ⟨6223100265473997473431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132759472330111946099861 6223100265473997473431)
                  ·
                    rfl

theorem cell23_109075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 6].length) (baseStart_109075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109075 prefixEnd_109075 := by exact prefixLift 109075
  have htrace : WordTrace (prefixWord ++ tailWord_109075) baseStart_109075 baseEnd_109075 := by
    simpa [prefixWord, tailWord_109075, baseEnd_109075] using wordTrace_append hprefix tailTrace_109075
  have hstable : (prefixWord ++ tailWord_109075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109075).length < 2 ^ (prefixWord ++ tailWord_109075).sum := by decide
  have hdescent : baseEnd_109075 < baseStart_109075 := by decide
  rcases family_descends (prefixWord ++ tailWord_109075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109135 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 1, 6]
def baseStart_109135 : Nat := 118140960795 + 109135 * 2 ^ 59
def prefixEnd_109135 : Nat := 4983230072969 + 3 ^ 40 * 109135 * 2
def baseEnd_109135 : Nat := 18679570409511914170201

theorem tailTrace_109135 : CollatzResearch.WordTrace tailWord_109135 prefixEnd_109135 18679570409511914170201 := by
  unfold tailWord_109135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980480459630008619200859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2653653639753339079467239 3980480459630008619200859)
  ·
    refine ⟨5970720689445012928801289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3980480459630008619200859 5970720689445012928801289)
    ·
      refine ⟨4478040517083759696600967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5970720689445012928801289 4478040517083759696600967)
      ·
        refine ⟨6717060775625639544901451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478040517083759696600967 6717060775625639544901451)
        ·
          refine ⟨10075591163438459317352177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717060775625639544901451 10075591163438459317352177)
          ·
            refine ⟨7556693372578844488014133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10075591163438459317352177 7556693372578844488014133)
            ·
              refine ⟨708440003679266670751325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7556693372578844488014133 708440003679266670751325)
              ·
                refine ⟨265665001379725001531747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708440003679266670751325 265665001379725001531747)
                ·
                  refine ⟨398497502069587502297621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265665001379725001531747 398497502069587502297621)
                  ·
                    refine ⟨18679570409511914170201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 398497502069587502297621 18679570409511914170201)
                    ·
                      rfl

theorem cell23_109135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_109135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109135 prefixEnd_109135 := by exact prefixLift 109135
  have htrace : WordTrace (prefixWord ++ tailWord_109135) baseStart_109135 baseEnd_109135 := by
    simpa [prefixWord, tailWord_109135, baseEnd_109135] using wordTrace_append hprefix tailTrace_109135
  have hstable : (prefixWord ++ tailWord_109135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109135).length < 2 ^ (prefixWord ++ tailWord_109135).sum := by decide
  have hdescent : baseEnd_109135 < baseStart_109135 := by decide
  rcases family_descends (prefixWord ++ tailWord_109135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109159 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_109159 : Nat := 118140960795 + 109159 * 2 ^ 59
def prefixEnd_109159 : Nat := 4983230072969 + 3 ^ 40 * 109159 * 2
def baseEnd_109159 : Nat := 56051034764243648610493

theorem tailTrace_109159 : CollatzResearch.WordTrace tailWord_109159 prefixEnd_109159 56051034764243648610493 := by
  unfold tailWord_109159
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981355811543060718074531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2654237207695373812049687 3981355811543060718074531)
  ·
    refine ⟨5972033717314591077111797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981355811543060718074531 5972033717314591077111797)
    ·
      refine ⟨559878160998242913479231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5972033717314591077111797 559878160998242913479231)
      ·
        refine ⟨839817241497364370218847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559878160998242913479231 839817241497364370218847)
        ·
          refine ⟨1259725862246046555328271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839817241497364370218847 1259725862246046555328271)
          ·
            refine ⟨1889588793369069832992407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259725862246046555328271 1889588793369069832992407)
            ·
              refine ⟨2834383190053604749488611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889588793369069832992407 2834383190053604749488611)
              ·
                refine ⟨4251574785080407124232917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834383190053604749488611 4251574785080407124232917)
                ·
                  refine ⟨99646284025322041974209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4251574785080407124232917 99646284025322041974209)
                  ·
                    refine ⟨74734713018991531480657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99646284025322041974209 74734713018991531480657)
                    ·
                      refine ⟨56051034764243648610493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74734713018991531480657 56051034764243648610493)
                      ·
                        rfl

theorem cell23_109159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_109159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109159 prefixEnd_109159 := by exact prefixLift 109159
  have htrace : WordTrace (prefixWord ++ tailWord_109159) baseStart_109159 baseEnd_109159 := by
    simpa [prefixWord, tailWord_109159, baseEnd_109159] using wordTrace_append hprefix tailTrace_109159
  have hstable : (prefixWord ++ tailWord_109159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109159).length < 2 ^ (prefixWord ++ tailWord_109159).sum := by decide
  have hdescent : baseEnd_109159 < baseStart_109159 := by decide
  rcases family_descends (prefixWord ++ tailWord_109159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109162 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_109162 : Nat := 118140960795 + 109162 * 2 ^ 59
def prefixEnd_109162 : Nat := 4983230072969 + 3 ^ 40 * 109162 * 2
def baseEnd_109162 : Nat := 56052575206207136872979

theorem tailTrace_109162 : CollatzResearch.WordTrace tailWord_109162 prefixEnd_109162 56052575206207136872979 := by
  unfold tailWord_109162
  simp only [CollatzResearch.WordTrace]
  refine ⟨995366307633048057608435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2654310153688128153622493 995366307633048057608435)
  ·
    refine ⟨1493049461449572086412653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995366307633048057608435 1493049461449572086412653)
    ·
      refine ⟨559893548043589532404745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1493049461449572086412653 559893548043589532404745)
      ·
        refine ⟨419920161032692149303559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559893548043589532404745 419920161032692149303559)
        ·
          refine ⟨629880241549038223955339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419920161032692149303559 629880241549038223955339)
          ·
            refine ⟨944820362323557335933009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629880241549038223955339 944820362323557335933009)
            ·
              refine ⟨708615271742668001949757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944820362323557335933009 708615271742668001949757)
              ·
                refine ⟨265730726903500500731159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708615271742668001949757 265730726903500500731159)
                ·
                  refine ⟨398596090355250751096739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265730726903500500731159 398596090355250751096739)
                  ·
                    refine ⟨597894135532876126645109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398596090355250751096739 597894135532876126645109)
                    ·
                      refine ⟨56052575206207136872979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 597894135532876126645109 56052575206207136872979)
                      ·
                        rfl

theorem cell23_109162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_109162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109162 prefixEnd_109162 := by exact prefixLift 109162
  have htrace : WordTrace (prefixWord ++ tailWord_109162) baseStart_109162 baseEnd_109162 := by
    simpa [prefixWord, tailWord_109162, baseEnd_109162] using wordTrace_append hprefix tailTrace_109162
  have hstable : (prefixWord ++ tailWord_109162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109162).length < 2 ^ (prefixWord ++ tailWord_109162).sum := by decide
  have hdescent : baseEnd_109162 < baseStart_109162 := by decide
  rcases family_descends (prefixWord ++ tailWord_109162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109189 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_109189 : Nat := 118140960795 + 109189 * 2 ^ 59
def prefixEnd_109189 : Nat := 4983230072969 + 3 ^ 40 * 109189 * 2
def baseEnd_109189 : Nat := 56066439183878531235355

theorem tailTrace_109189 : CollatzResearch.WordTrace tailWord_109189 prefixEnd_109189 56066439183878531235355 := by
  unfold tailWord_109189
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982450001434375841666621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2654966667622917227777747 3982450001434375841666621)
  ·
    refine ⟨1493418750537890940624983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3982450001434375841666621 1493418750537890940624983)
    ·
      refine ⟨2240128125806836410937475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493418750537890940624983 2240128125806836410937475)
      ·
        refine ⟨3360192188710254616406213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240128125806836410937475 3360192188710254616406213)
        ·
          refine ⟨630036035383172740576165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3360192188710254616406213 630036035383172740576165)
          ·
            refine ⟨118131756634344888858031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 630036035383172740576165 118131756634344888858031)
            ·
              refine ⟨177197634951517333287047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118131756634344888858031 177197634951517333287047)
              ·
                refine ⟨265796452427275999930571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177197634951517333287047 265796452427275999930571)
                ·
                  refine ⟨398694678640913999895857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265796452427275999930571 398694678640913999895857)
                  ·
                    refine ⟨299021008980685499921893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398694678640913999895857 299021008980685499921893)
                    ·
                      refine ⟨56066439183878531235355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 299021008980685499921893 56066439183878531235355)
                      ·
                        rfl

theorem cell23_109189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_109189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109189 prefixEnd_109189 := by exact prefixLift 109189
  have htrace : WordTrace (prefixWord ++ tailWord_109189) baseStart_109189 baseEnd_109189 := by
    simpa [prefixWord, tailWord_109189, baseEnd_109189] using wordTrace_append hprefix tailTrace_109189
  have hstable : (prefixWord ++ tailWord_109189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109189).length < 2 ^ (prefixWord ++ tailWord_109189).sum := by decide
  have hdescent : baseEnd_109189 < baseStart_109189 := by decide
  rcases family_descends (prefixWord ++ tailWord_109189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109283 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 2, 2, 2]
def baseStart_109283 : Nat := 118140960795 + 109283 * 2 ^ 59
def prefixEnd_109283 : Nat := 4983230072969 + 3 ^ 40 * 109283 * 2
def baseEnd_109283 : Nat := 56114706365401163459923

theorem tailTrace_109283 : CollatzResearch.WordTrace tailWord_109283 prefixEnd_109283 56114706365401163459923 := by
  unfold tailWord_109283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985878463093829895588503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2657252308729219930392335 3985878463093829895588503)
  ·
    refine ⟨5978817694640744843382755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985878463093829895588503 5978817694640744843382755)
    ·
      refine ⟨8968226541961117265074133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978817694640744843382755 8968226541961117265074133)
      ·
        refine ⟨210192809577213685900175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8968226541961117265074133 210192809577213685900175)
        ·
          refine ⟨315289214365820528850263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210192809577213685900175 315289214365820528850263)
          ·
            refine ⟨472933821548730793275395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315289214365820528850263 472933821548730793275395)
            ·
              refine ⟨709400732323096189913093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472933821548730793275395 709400732323096189913093)
              ·
                refine ⟨133012637310580535608705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709400732323096189913093 133012637310580535608705)
                ·
                  refine ⟨99759477982935401706529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133012637310580535608705 99759477982935401706529)
                  ·
                    refine ⟨74819608487201551279897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99759477982935401706529 74819608487201551279897)
                    ·
                      refine ⟨56114706365401163459923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74819608487201551279897 56114706365401163459923)
                      ·
                        rfl

theorem cell23_109283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_109283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109283 prefixEnd_109283 := by exact prefixLift 109283
  have htrace : WordTrace (prefixWord ++ tailWord_109283) baseStart_109283 baseEnd_109283 := by
    simpa [prefixWord, tailWord_109283, baseEnd_109283] using wordTrace_append hprefix tailTrace_109283
  have hstable : (prefixWord ++ tailWord_109283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109283).length < 2 ^ (prefixWord ++ tailWord_109283).sum := by decide
  have hdescent : baseEnd_109283 < baseStart_109283 := by decide
  rcases family_descends (prefixWord ++ tailWord_109283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109309 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_109309 : Nat := 118140960795 + 109309 * 2 ^ 59
def prefixEnd_109309 : Nat := 4983230072969 + 3 ^ 40 * 109309 * 2
def baseEnd_109309 : Nat := 56128056862418061734803

theorem tailTrace_109309 : CollatzResearch.WordTrace tailWord_109309 prefixEnd_109309 56128056862418061734803 := by
  unfold tailWord_109309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986826760999636336034981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2657884507333090890689987 3986826760999636336034981)
  ·
    refine ⟨747530017687431813006559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3986826760999636336034981 747530017687431813006559)
    ·
      refine ⟨1121295026531147719509839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747530017687431813006559 1121295026531147719509839)
      ·
        refine ⟨1681942539796721579264759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121295026531147719509839 1681942539796721579264759)
        ·
          refine ⟨2522913809695082368897139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681942539796721579264759 2522913809695082368897139)
          ·
            refine ⟨3784370714542623553345709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522913809695082368897139 3784370714542623553345709)
            ·
              refine ⟨1419139017953483832504641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3784370714542623553345709 1419139017953483832504641)
              ·
                refine ⟨1064354263465112874378481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419139017953483832504641 1064354263465112874378481)
                ·
                  refine ⟨798265697598834655783861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064354263465112874378481 798265697598834655783861)
                  ·
                    refine ⟨74837409149890748979737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 798265697598834655783861 74837409149890748979737)
                    ·
                      refine ⟨56128056862418061734803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74837409149890748979737 56128056862418061734803)
                      ·
                        rfl

theorem cell23_109309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_109309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109309 prefixEnd_109309 := by exact prefixLift 109309
  have htrace : WordTrace (prefixWord ++ tailWord_109309) baseStart_109309 baseEnd_109309 := by
    simpa [prefixWord, tailWord_109309, baseEnd_109309] using wordTrace_append hprefix tailTrace_109309
  have hstable : (prefixWord ++ tailWord_109309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109309).length < 2 ^ (prefixWord ++ tailWord_109309).sum := by decide
  have hdescent : baseEnd_109309 < baseStart_109309 := by decide
  rcases family_descends (prefixWord ++ tailWord_109309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109319 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 7]
def baseStart_109319 : Nat := 118140960795 + 109319 * 2 ^ 59
def prefixEnd_109319 : Nat := 4983230072969 + 3 ^ 40 * 109319 * 2
def baseEnd_109319 : Nat := 18711063889654340869919

theorem tailTrace_109319 : CollatzResearch.WordTrace tailWord_109319 prefixEnd_109319 18711063889654340869919 := by
  unfold tailWord_109319
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987191490963408043899011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2658127660642272029266007 3987191490963408043899011)
  ·
    refine ⟨5980787236445112065848517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987191490963408043899011 5980787236445112065848517)
    ·
      refine ⟨1121397606833458512346597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5980787236445112065848517 1121397606833458512346597)
      ·
        refine ⟨210262051281273471064987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1121397606833458512346597 210262051281273471064987)
        ·
          refine ⟨315393076921910206597481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210262051281273471064987 315393076921910206597481)
          ·
            refine ⟨236544807691432654948111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315393076921910206597481 236544807691432654948111)
            ·
              refine ⟨354817211537148982422167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236544807691432654948111 354817211537148982422167)
              ·
                refine ⟨532225817305723473633251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354817211537148982422167 532225817305723473633251)
                ·
                  refine ⟨798338725958585210449877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532225817305723473633251 798338725958585210449877)
                  ·
                    refine ⟨18711063889654340869919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 798338725958585210449877 18711063889654340869919)
                    ·
                      rfl

theorem cell23_109319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_109319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109319 prefixEnd_109319 := by exact prefixLift 109319
  have htrace : WordTrace (prefixWord ++ tailWord_109319) baseStart_109319 baseEnd_109319 := by
    simpa [prefixWord, tailWord_109319, baseEnd_109319] using wordTrace_append hprefix tailTrace_109319
  have hstable : (prefixWord ++ tailWord_109319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109319).length < 2 ^ (prefixWord ++ tailWord_109319).sum := by decide
  have hdescent : baseEnd_109319 < baseStart_109319 := by decide
  rcases family_descends (prefixWord ++ tailWord_109319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109426 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_109426 : Nat := 118140960795 + 109426 * 2 ^ 59
def prefixEnd_109426 : Nat := 4983230072969 + 3 ^ 40 * 109426 * 2
def baseEnd_109426 : Nat := 18729378032998034657255

theorem tailTrace_109426 : CollatzResearch.WordTrace tailWord_109426 prefixEnd_109426 18729378032998034657255 := by
  unfold tailWord_109426
  simp only [CollatzResearch.WordTrace]
  refine ⟨997773525393941329511033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2660729401050510212029421 997773525393941329511033)
  ·
    refine ⟨748330144045455997133275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 997773525393941329511033 748330144045455997133275)
    ·
      refine ⟨1122495216068183995699913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 748330144045455997133275 1122495216068183995699913)
      ·
        refine ⟨841871412051137996774935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122495216068183995699913 841871412051137996774935)
        ·
          refine ⟨1262807118076706995162403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841871412051137996774935 1262807118076706995162403)
          ·
            refine ⟨1894210677115060492743605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262807118076706995162403 1894210677115060492743605)
            ·
              refine ⟨177582250979536921194713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1894210677115060492743605 177582250979536921194713)
              ·
                refine ⟨133186688234652690896035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177582250979536921194713 133186688234652690896035)
                ·
                  refine ⟨199780032351979036344053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133186688234652690896035 199780032351979036344053)
                  ·
                    refine ⟨18729378032998034657255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199780032351979036344053 18729378032998034657255)
                    ·
                      rfl

theorem cell23_109426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_109426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109426 prefixEnd_109426 := by exact prefixLift 109426
  have htrace : WordTrace (prefixWord ++ tailWord_109426) baseStart_109426 baseEnd_109426 := by
    simpa [prefixWord, tailWord_109426, baseEnd_109426] using wordTrace_append hprefix tailTrace_109426
  have hstable : (prefixWord ++ tailWord_109426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109426).length < 2 ^ (prefixWord ++ tailWord_109426).sum := by decide
  have hdescent : baseEnd_109426 < baseStart_109426 := by decide
  rcases family_descends (prefixWord ++ tailWord_109426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109433 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 2, 3, 2]
def baseStart_109433 : Nat := 118140960795 + 109433 * 2 ^ 59
def prefixEnd_109433 : Nat := 4983230072969 + 3 ^ 40 * 109433 * 2
def baseEnd_109433 : Nat := 56191728463575576584233

theorem tailTrace_109433 : CollatzResearch.WordTrace tailWord_109433 prefixEnd_109433 56191728463575576584233 := by
  unfold tailWord_109433
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991349412550405513548953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2660899608366937009032635 3991349412550405513548953)
  ·
    refine ⟨2993512059412804135161715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3991349412550405513548953 2993512059412804135161715)
    ·
      refine ⟨4490268089119206202742573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993512059412804135161715 4490268089119206202742573)
      ·
        refine ⟨1683850533419702326028465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4490268089119206202742573 1683850533419702326028465)
        ·
          refine ⟨1262887900064776744521349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683850533419702326028465 1262887900064776744521349)
          ·
            refine ⟨236791481262145639597753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1262887900064776744521349 236791481262145639597753)
            ·
              refine ⟨177593610946609229698315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236791481262145639597753 177593610946609229698315)
              ·
                refine ⟨266390416419913844547473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177593610946609229698315 266390416419913844547473)
                ·
                  refine ⟨199792812314935383410605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266390416419913844547473 199792812314935383410605)
                  ·
                    refine ⟨74922304618100768778977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199792812314935383410605 74922304618100768778977)
                    ·
                      refine ⟨56191728463575576584233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74922304618100768778977 56191728463575576584233)
                      ·
                        rfl

theorem cell23_109433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_109433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109433 prefixEnd_109433 := by exact prefixLift 109433
  have htrace : WordTrace (prefixWord ++ tailWord_109433) baseStart_109433 baseEnd_109433 := by
    simpa [prefixWord, tailWord_109433, baseEnd_109433] using wordTrace_append hprefix tailTrace_109433
  have hstable : (prefixWord ++ tailWord_109433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109433).length < 2 ^ (prefixWord ++ tailWord_109433).sum := by decide
  have hdescent : baseEnd_109433 < baseStart_109433 := by decide
  rcases family_descends (prefixWord ++ tailWord_109433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109439 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 6, 4]
def baseStart_109439 : Nat := 118140960795 + 109439 * 2 ^ 59
def prefixEnd_109439 : Nat := 4983230072969 + 3 ^ 40 * 109439 * 2
def baseEnd_109439 : Nat := 18731603115834184369735

theorem tailTrace_109439 : CollatzResearch.WordTrace tailWord_109439 prefixEnd_109439 18731603115834184369735 := by
  unfold tailWord_109439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991568250528668538267371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2661045500352445692178247 3991568250528668538267371)
  ·
    refine ⟨5987352375793002807401057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991568250528668538267371 5987352375793002807401057)
    ·
      refine ⟨4490514281844752105550793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5987352375793002807401057 4490514281844752105550793)
      ·
        refine ⟨3367885711383564079163095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4490514281844752105550793 3367885711383564079163095)
        ·
          refine ⟨5051828567075346118744643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367885711383564079163095 5051828567075346118744643)
          ·
            refine ⟨7577742850613019178116965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051828567075346118744643 7577742850613019178116965)
            ·
              refine ⟨1420826784489941095896931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7577742850613019178116965 1420826784489941095896931)
              ·
                refine ⟨2131240176734911643845397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420826784489941095896931 2131240176734911643845397)
                ·
                  refine ⟨99901883284448983305253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2131240176734911643845397 99901883284448983305253)
                  ·
                    refine ⟨18731603115834184369735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99901883284448983305253 18731603115834184369735)
                    ·
                      rfl

theorem cell23_109439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_109439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109439 prefixEnd_109439 := by exact prefixLift 109439
  have htrace : WordTrace (prefixWord ++ tailWord_109439) baseStart_109439 baseEnd_109439 := by
    simpa [prefixWord, tailWord_109439, baseEnd_109439] using wordTrace_append hprefix tailTrace_109439
  have hstable : (prefixWord ++ tailWord_109439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109439).length < 2 ^ (prefixWord ++ tailWord_109439).sum := by decide
  have hdescent : baseEnd_109439 < baseStart_109439 := by decide
  rcases family_descends (prefixWord ++ tailWord_109439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109463 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_109463 : Nat := 118140960795 + 109463 * 2 ^ 59
def prefixEnd_109463 : Nat := 4983230072969 + 3 ^ 40 * 109463 * 2
def baseEnd_109463 : Nat := 56207132883210459209095

theorem tailTrace_109463 : CollatzResearch.WordTrace tailWord_109463 prefixEnd_109463 56207132883210459209095 := by
  unfold tailWord_109463
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992443602441720637141043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2661629068294480424760695 3992443602441720637141043)
  ·
    refine ⟨5988665403662580955711565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992443602441720637141043 5988665403662580955711565)
    ·
      refine ⟨2245749526373467858391837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5988665403662580955711565 2245749526373467858391837)
      ·
        refine ⟨842156072390050446896939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2245749526373467858391837 842156072390050446896939)
        ·
          refine ⟨1263234108585075670345409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842156072390050446896939 1263234108585075670345409)
          ·
            refine ⟨947425581438806752759057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263234108585075670345409 947425581438806752759057)
            ·
              refine ⟨710569186079105064569293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947425581438806752759057 710569186079105064569293)
              ·
                refine ⟨266463444779664399213485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710569186079105064569293 266463444779664399213485)
                ·
                  refine ⟨99923791792374149705057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266463444779664399213485 99923791792374149705057)
                  ·
                    refine ⟨74942843844280612278793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99923791792374149705057 74942843844280612278793)
                    ·
                      refine ⟨56207132883210459209095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74942843844280612278793 56207132883210459209095)
                      ·
                        rfl

theorem cell23_109463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_109463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109463 prefixEnd_109463 := by exact prefixLift 109463
  have htrace : WordTrace (prefixWord ++ tailWord_109463) baseStart_109463 baseEnd_109463 := by
    simpa [prefixWord, tailWord_109463, baseEnd_109463] using wordTrace_append hprefix tailTrace_109463
  have hstable : (prefixWord ++ tailWord_109463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109463).length < 2 ^ (prefixWord ++ tailWord_109463).sum := by decide
  have hdescent : baseEnd_109463 < baseStart_109463 := by decide
  rcases family_descends (prefixWord ++ tailWord_109463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109473 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_109473 : Nat := 118140960795 + 109473 * 2 ^ 59
def prefixEnd_109473 : Nat := 4983230072969 + 3 ^ 40 * 109473 * 2
def baseEnd_109473 : Nat := 18737422563251806694683

theorem tailTrace_109473 : CollatzResearch.WordTrace tailWord_109473 prefixEnd_109473 18737422563251806694683 := by
  unfold tailWord_109473
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992808332405492345005073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2661872221603661563336715 3992808332405492345005073)
  ·
    refine ⟨2994606249304119258753805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992808332405492345005073 2994606249304119258753805)
    ·
      refine ⟨1122977343489044722032677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2994606249304119258753805 1122977343489044722032677)
      ·
        refine ⟨210558251904195885381127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1122977343489044722032677 210558251904195885381127)
        ·
          refine ⟨315837377856293828071691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210558251904195885381127 315837377856293828071691)
          ·
            refine ⟨473756066784440742107537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315837377856293828071691 473756066784440742107537)
            ·
              refine ⟨355317050088330556580653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473756066784440742107537 355317050088330556580653)
              ·
                refine ⟨133243893783123958717745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355317050088330556580653 133243893783123958717745)
                ·
                  refine ⟨99932920337342969038309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133243893783123958717745 99932920337342969038309)
                  ·
                    refine ⟨18737422563251806694683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99932920337342969038309 18737422563251806694683)
                    ·
                      rfl

theorem cell23_109473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_109473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109473 prefixEnd_109473 := by exact prefixLift 109473
  have htrace : WordTrace (prefixWord ++ tailWord_109473) baseStart_109473 baseEnd_109473 := by
    simpa [prefixWord, tailWord_109473, baseEnd_109473] using wordTrace_append hprefix tailTrace_109473
  have hstable : (prefixWord ++ tailWord_109473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109473).length < 2 ^ (prefixWord ++ tailWord_109473).sum := by decide
  have hdescent : baseEnd_109473 < baseStart_109473 := by decide
  rcases family_descends (prefixWord ++ tailWord_109473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109476 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_109476 : Nat := 118140960795 + 109476 * 2 ^ 59
def prefixEnd_109476 : Nat := 4983230072969 + 3 ^ 40 * 109476 * 2
def baseEnd_109476 : Nat := 56213808131718908346535

theorem tailTrace_109476 : CollatzResearch.WordTrace tailWord_109476 prefixEnd_109476 56213808131718908346535 := by
  unfold tailWord_109476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996458875697311928682141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2661945167596415904909521 1996458875697311928682141)
  ·
    refine ⟨748672078386491973255803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1996458875697311928682141 748672078386491973255803)
    ·
      refine ⟨1123008117579737959883705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 748672078386491973255803 1123008117579737959883705)
      ·
        refine ⟨842256088184803469912779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1123008117579737959883705 842256088184803469912779)
        ·
          refine ⟨1263384132277205204869169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842256088184803469912779 1263384132277205204869169)
          ·
            refine ⟨947538099207903903651877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263384132277205204869169 947538099207903903651877)
            ·
              refine ⟨177663393601481981934727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 947538099207903903651877 177663393601481981934727)
              ·
                refine ⟨266495090402222972902091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177663393601481981934727 266495090402222972902091)
                ·
                  refine ⟨399742635603334459353137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266495090402222972902091 399742635603334459353137)
                  ·
                    refine ⟨299806976702500844514853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399742635603334459353137 299806976702500844514853)
                    ·
                      refine ⟨56213808131718908346535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 299806976702500844514853 56213808131718908346535)
                      ·
                        rfl

theorem cell23_109476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_109476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109476 prefixEnd_109476 := by exact prefixLift 109476
  have htrace : WordTrace (prefixWord ++ tailWord_109476) baseStart_109476 baseEnd_109476 := by
    simpa [prefixWord, tailWord_109476, baseEnd_109476] using wordTrace_append hprefix tailTrace_109476
  have hstable : (prefixWord ++ tailWord_109476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109476).length < 2 ^ (prefixWord ++ tailWord_109476).sum := by decide
  have hdescent : baseEnd_109476 < baseStart_109476 := by decide
  rcases family_descends (prefixWord ++ tailWord_109476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109496 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_109496 : Nat := 118140960795 + 109496 * 2 ^ 59
def prefixEnd_109496 : Nat := 4983230072969 + 3 ^ 40 * 109496 * 2
def baseEnd_109496 : Nat := 56224077744808830096443

theorem tailTrace_109496 : CollatzResearch.WordTrace tailWord_109496 prefixEnd_109496 56224077744808830096443 := by
  unfold tailWord_109496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996823605661083636546171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2662431474214778182061561 1996823605661083636546171)
  ·
    refine ⟨2995235408491625454819257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996823605661083636546171 2995235408491625454819257)
    ·
      refine ⟨2246426556368719091114443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2995235408491625454819257 2246426556368719091114443)
      ·
        refine ⟨3369639834553078636671665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246426556368719091114443 3369639834553078636671665)
        ·
          refine ⟨2527229875914808977503749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369639834553078636671665 2527229875914808977503749)
          ·
            refine ⟨473855601734026683281953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2527229875914808977503749 473855601734026683281953)
            ·
              refine ⟨355391701300520012461465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473855601734026683281953 355391701300520012461465)
              ·
                refine ⟨266543775975390009346099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355391701300520012461465 266543775975390009346099)
                ·
                  refine ⟨399815663963085014019149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266543775975390009346099 399815663963085014019149)
                  ·
                    refine ⟨149930873986156880257181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399815663963085014019149 149930873986156880257181)
                    ·
                      refine ⟨56224077744808830096443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 149930873986156880257181 56224077744808830096443)
                      ·
                        rfl

theorem cell23_109496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_109496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109496 prefixEnd_109496 := by exact prefixLift 109496
  have htrace : WordTrace (prefixWord ++ tailWord_109496) baseStart_109496 baseEnd_109496 := by
    simpa [prefixWord, tailWord_109496, baseEnd_109496] using wordTrace_append hprefix tailTrace_109496
  have hstable : (prefixWord ++ tailWord_109496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109496).length < 2 ^ (prefixWord ++ tailWord_109496).sum := by decide
  have hdescent : baseEnd_109496 < baseStart_109496 := by decide
  rcases family_descends (prefixWord ++ tailWord_109496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109497 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 1, 2, 2]
def baseStart_109497 : Nat := 118140960795 + 109497 * 2 ^ 59
def prefixEnd_109497 : Nat := 4983230072969 + 3 ^ 40 * 109497 * 2
def baseEnd_109497 : Nat := 56224591225463326183939

theorem tailTrace_109497 : CollatzResearch.WordTrace tailWord_109497 prefixEnd_109497 56224591225463326183939 := by
  unfold tailWord_109497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993683684318544443878745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2662455789545696295919163 3993683684318544443878745)
  ·
    refine ⟨2995262763238908332909059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3993683684318544443878745 2995262763238908332909059)
    ·
      refine ⟨4492894144858362499363589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995262763238908332909059 4492894144858362499363589)
      ·
        refine ⟨842417652160942968630673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4492894144858362499363589 842417652160942968630673)
        ·
          refine ⟨631813239120707226473005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842417652160942968630673 631813239120707226473005)
          ·
            refine ⟨236929964670265209927377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 631813239120707226473005 236929964670265209927377)
            ·
              refine ⟨177697473502698907445533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236929964670265209927377 177697473502698907445533)
              ·
                refine ⟨66636552563512090292075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177697473502698907445533 66636552563512090292075)
                ·
                  refine ⟨99954828845268135438113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66636552563512090292075 99954828845268135438113)
                  ·
                    refine ⟨74966121633951101578585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99954828845268135438113 74966121633951101578585)
                    ·
                      refine ⟨56224591225463326183939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 74966121633951101578585 56224591225463326183939)
                      ·
                        rfl

theorem cell23_109497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_109497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109497 prefixEnd_109497 := by exact prefixLift 109497
  have htrace : WordTrace (prefixWord ++ tailWord_109497) baseStart_109497 baseEnd_109497 := by
    simpa [prefixWord, tailWord_109497, baseEnd_109497] using wordTrace_append hprefix tailTrace_109497
  have hstable : (prefixWord ++ tailWord_109497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109497).length < 2 ^ (prefixWord ++ tailWord_109497).sum := by decide
  have hdescent : baseEnd_109497 < baseStart_109497 := by decide
  rcases family_descends (prefixWord ++ tailWord_109497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109517 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_109517 : Nat := 118140960795 + 109517 * 2 ^ 59
def prefixEnd_109517 : Nat := 4983230072969 + 3 ^ 40 * 109517 * 2
def baseEnd_109517 : Nat := 56234860838553247933847

theorem tailTrace_109517 : CollatzResearch.WordTrace tailWord_109517 prefixEnd_109517 56234860838553247933847 := by
  unfold tailWord_109517
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994413144246087859606805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2662942096164058573071203 3994413144246087859606805)
  ·
    refine ⟨187238116136535368419069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3994413144246087859606805 187238116136535368419069)
    ·
      refine ⟨70214293551200763157151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187238116136535368419069 70214293551200763157151)
      ·
        refine ⟨105321440326801144735727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70214293551200763157151 105321440326801144735727)
        ·
          refine ⟨157982160490201717103591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105321440326801144735727 157982160490201717103591)
          ·
            refine ⟨236973240735302575655387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157982160490201717103591 236973240735302575655387)
            ·
              refine ⟨355459861102953863483081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236973240735302575655387 355459861102953863483081)
              ·
                refine ⟨266594895827215397612311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355459861102953863483081 266594895827215397612311)
                ·
                  refine ⟨399892343740823096418467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266594895827215397612311 399892343740823096418467)
                  ·
                    refine ⟨599838515611234644627701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399892343740823096418467 599838515611234644627701)
                    ·
                      refine ⟨56234860838553247933847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 599838515611234644627701 56234860838553247933847)
                      ·
                        rfl

theorem cell23_109517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_109517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109517 prefixEnd_109517 := by exact prefixLift 109517
  have htrace : WordTrace (prefixWord ++ tailWord_109517) baseStart_109517 baseEnd_109517 := by
    simpa [prefixWord, tailWord_109517, baseEnd_109517] using wordTrace_append hprefix tailTrace_109517
  have hstable : (prefixWord ++ tailWord_109517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109517).length < 2 ^ (prefixWord ++ tailWord_109517).sum := by decide
  have hdescent : baseEnd_109517 < baseStart_109517 := by decide
  rcases family_descends (prefixWord ++ tailWord_109517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109576 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 7]
def baseStart_109576 : Nat := 118140960795 + 109576 * 2 ^ 59
def prefixEnd_109576 : Nat := 4983230072969 + 3 ^ 40 * 109576 * 2
def baseEnd_109576 : Nat := 6251684021907613010675

theorem tailTrace_109576 : CollatzResearch.WordTrace tailWord_109576 prefixEnd_109576 6251684021907613010675 := by
  unfold tailWord_109576
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998282525516170468002291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2664376700688227290669721 1998282525516170468002291)
  ·
    refine ⟨2997423788274255702003437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1998282525516170468002291 2997423788274255702003437)
    ·
      refine ⟨1124033920602845888251289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2997423788274255702003437 1124033920602845888251289)
      ·
        refine ⟨843025440452134416188467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124033920602845888251289 843025440452134416188467)
        ·
          refine ⟨1264538160678201624282701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843025440452134416188467 1264538160678201624282701)
          ·
            refine ⟨474201810254325609106013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1264538160678201624282701 474201810254325609106013)
            ·
              refine ⟨177825678845372103414755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 474201810254325609106013 177825678845372103414755)
              ·
                refine ⟨266738518268058155122133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177825678845372103414755 266738518268058155122133)
                ·
                  refine ⟨6251684021907613010675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266738518268058155122133 6251684021907613010675)
                  ·
                    rfl

theorem cell23_109576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_109576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109576 prefixEnd_109576 := by exact prefixLift 109576
  have htrace : WordTrace (prefixWord ++ tailWord_109576) baseStart_109576 baseEnd_109576 := by
    simpa [prefixWord, tailWord_109576, baseEnd_109576] using wordTrace_append hprefix tailTrace_109576
  have hstable : (prefixWord ++ tailWord_109576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109576).length < 2 ^ (prefixWord ++ tailWord_109576).sum := by decide
  have hdescent : baseEnd_109576 < baseStart_109576 := by decide
  rcases family_descends (prefixWord ++ tailWord_109576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109630 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_109630 : Nat := 118140960795 + 109630 * 2 ^ 59
def prefixEnd_109630 : Nat := 4983230072969 + 3 ^ 40 * 109630 * 2
def baseEnd_109630 : Nat := 56292884152511305820827

theorem tailTrace_109630 : CollatzResearch.WordTrace tailWord_109630 prefixEnd_109630 56292884152511305820827 := by
  unfold tailWord_109630
  simp only [CollatzResearch.WordTrace]
  refine ⟨499816824104588519808793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2665689728557805438980229 499816824104588519808793)
  ·
    refine ⟨374862618078441389856595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499816824104588519808793 374862618078441389856595)
    ·
      refine ⟨562293927117662084784893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374862618078441389856595 562293927117662084784893)
      ·
        refine ⟨210860222669123281794335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562293927117662084784893 210860222669123281794335)
        ·
          refine ⟨316290334003684922691503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210860222669123281794335 316290334003684922691503)
          ·
            refine ⟨474435501005527384037255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316290334003684922691503 474435501005527384037255)
            ·
              refine ⟨711653251508291076055883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474435501005527384037255 711653251508291076055883)
              ·
                refine ⟨1067479877262436614083825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711653251508291076055883 1067479877262436614083825)
                ·
                  refine ⟨800609907946827460562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067479877262436614083825 800609907946827460562869)
                  ·
                    refine ⟨75057178870015074427769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 800609907946827460562869 75057178870015074427769)
                    ·
                      refine ⟨56292884152511305820827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75057178870015074427769 56292884152511305820827)
                      ·
                        rfl

theorem cell23_109630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_109630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109630 prefixEnd_109630 := by exact prefixLift 109630
  have htrace : WordTrace (prefixWord ++ tailWord_109630) baseStart_109630 baseEnd_109630 := by
    simpa [prefixWord, tailWord_109630, baseEnd_109630] using wordTrace_append hprefix tailTrace_109630
  have hstable : (prefixWord ++ tailWord_109630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109630).length < 2 ^ (prefixWord ++ tailWord_109630).sum := by decide
  have hdescent : baseEnd_109630 < baseStart_109630 := by decide
  rcases family_descends (prefixWord ++ tailWord_109630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109653 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_109653 : Nat := 118140960795 + 109653 * 2 ^ 59
def prefixEnd_109653 : Nat := 4983230072969 + 3 ^ 40 * 109653 * 2
def baseEnd_109653 : Nat := 18768231402521571944407

theorem tailTrace_109653 : CollatzResearch.WordTrace tailWord_109653 prefixEnd_109653 18768231402521571944407 := by
  unfold tailWord_109653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999373471753383086557613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2666248981168922057705075 3999373471753383086557613)
  ·
    refine ⟨1499765051907518657459105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3999373471753383086557613 1499765051907518657459105)
    ·
      refine ⟨1124823788930638993094329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1499765051907518657459105 1124823788930638993094329)
      ·
        refine ⟨843617841697979244820747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124823788930638993094329 843617841697979244820747)
        ·
          refine ⟨1265426762546968867231121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843617841697979244820747 1265426762546968867231121)
          ·
            refine ⟨949070071910226650423341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265426762546968867231121 949070071910226650423341)
            ·
              refine ⟨355901276966334993908753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949070071910226650423341 355901276966334993908753)
              ·
                refine ⟨266925957724751245431565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355901276966334993908753 266925957724751245431565)
                ·
                  refine ⟨100097234146781717036837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266925957724751245431565 100097234146781717036837)
                  ·
                    refine ⟨18768231402521571944407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100097234146781717036837 18768231402521571944407)
                    ·
                      rfl

theorem cell23_109653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_109653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109653 prefixEnd_109653 := by exact prefixLift 109653
  have htrace : WordTrace (prefixWord ++ tailWord_109653) baseStart_109653 baseEnd_109653 := by
    simpa [prefixWord, tailWord_109653, baseEnd_109653] using wordTrace_append hprefix tailTrace_109653
  have hstable : (prefixWord ++ tailWord_109653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109653).length < 2 ^ (prefixWord ++ tailWord_109653).sum := by decide
  have hdescent : baseEnd_109653 < baseStart_109653 := by decide
  rcases family_descends (prefixWord ++ tailWord_109653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109696 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_109696 : Nat := 118140960795 + 109696 * 2 ^ 59
def prefixEnd_109696 : Nat := 4983230072969 + 3 ^ 40 * 109696 * 2
def baseEnd_109696 : Nat := 18775591291902682531841

theorem tailTrace_109696 : CollatzResearch.WordTrace tailWord_109696 prefixEnd_109696 18775591291902682531841 := by
  unfold tailWord_109696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000470905298800715186471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2667294540398400953581961 2000470905298800715186471)
  ·
    refine ⟨3000706357948201072779707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000470905298800715186471 3000706357948201072779707)
    ·
      refine ⟨4501059536922301609169561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000706357948201072779707 4501059536922301609169561)
      ·
        refine ⟨3375794652691726206877171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4501059536922301609169561 3375794652691726206877171)
        ·
          refine ⟨5063691979037589310315757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375794652691726206877171 5063691979037589310315757)
          ·
            refine ⟨1898884492139095991368409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5063691979037589310315757 1898884492139095991368409)
            ·
              refine ⟨1424163369104321993526307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898884492139095991368409 1424163369104321993526307)
              ·
                refine ⟨2136245053656482990289461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424163369104321993526307 2136245053656482990289461)
                ·
                  refine ⟨200272973780295280339637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2136245053656482990289461 200272973780295280339637)
                  ·
                    refine ⟨18775591291902682531841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200272973780295280339637 18775591291902682531841)
                    ·
                      rfl

theorem cell23_109696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_109696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109696 prefixEnd_109696 := by exact prefixLift 109696
  have htrace : WordTrace (prefixWord ++ tailWord_109696) baseStart_109696 baseEnd_109696 := by
    simpa [prefixWord, tailWord_109696, baseEnd_109696] using wordTrace_append hprefix tailTrace_109696
  have hstable : (prefixWord ++ tailWord_109696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109696).length < 2 ^ (prefixWord ++ tailWord_109696).sum := by decide
  have hdescent : baseEnd_109696 < baseStart_109696 := by decide
  rcases family_descends (prefixWord ++ tailWord_109696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109700 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 6]
def baseStart_109700 : Nat := 118140960795 + 109700 * 2 ^ 59
def prefixEnd_109700 : Nat := 4983230072969 + 3 ^ 40 * 109700 * 2
def baseEnd_109700 : Nat := 6258758644258447993945

theorem tailTrace_109700 : CollatzResearch.WordTrace tailWord_109700 prefixEnd_109700 6258758644258447993945 := by
  unfold tailWord_109700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000543851291555056759277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2667391801722073409012369 2000543851291555056759277)
  ·
    refine ⟨750203944234333146284729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2000543851291555056759277 750203944234333146284729)
    ·
      refine ⟨562652958175749859713547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 750203944234333146284729 562652958175749859713547)
      ·
        refine ⟨843979437263624789570321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562652958175749859713547 843979437263624789570321)
        ·
          refine ⟨632984577947718592177741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843979437263624789570321 632984577947718592177741)
          ·
            refine ⟨237369216730394472066653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632984577947718592177741 237369216730394472066653)
            ·
              refine ⟨89013456273897927024995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237369216730394472066653 89013456273897927024995)
              ·
                refine ⟨133520184410846890537493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89013456273897927024995 133520184410846890537493)
                ·
                  refine ⟨6258758644258447993945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133520184410846890537493 6258758644258447993945)
                  ·
                    rfl

theorem cell23_109700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_109700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109700 prefixEnd_109700 := by exact prefixLift 109700
  have htrace : WordTrace (prefixWord ++ tailWord_109700) baseStart_109700 baseEnd_109700 := by
    simpa [prefixWord, tailWord_109700, baseEnd_109700] using wordTrace_append hprefix tailTrace_109700
  have hstable : (prefixWord ++ tailWord_109700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109700).length < 2 ^ (prefixWord ++ tailWord_109700).sum := by decide
  have hdescent : baseEnd_109700 < baseStart_109700 := by decide
  rcases family_descends (prefixWord ++ tailWord_109700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109720 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_109720 : Nat := 118140960795 + 109720 * 2 ^ 59
def prefixEnd_109720 : Nat := 4983230072969 + 3 ^ 40 * 109720 * 2
def baseEnd_109720 : Nat := 56339097411415953695413

theorem tailTrace_109720 : CollatzResearch.WordTrace tailWord_109720 prefixEnd_109720 56339097411415953695413 := by
  unfold tailWord_109720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000908581255326764623307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2667878108340435686164409 2000908581255326764623307)
  ·
    refine ⟨3001362871882990146934961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000908581255326764623307 3001362871882990146934961)
    ·
      refine ⟨2251022153912242610201221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3001362871882990146934961 2251022153912242610201221)
      ·
        refine ⟨422066653858545489412729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2251022153912242610201221 422066653858545489412729)
        ·
          refine ⟨316549990393909117059547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422066653858545489412729 316549990393909117059547)
          ·
            refine ⟨474824985590863675589321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316549990393909117059547 474824985590863675589321)
            ·
              refine ⟨356118739193147756691991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474824985590863675589321 356118739193147756691991)
              ·
                refine ⟨534178108789721635037987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356118739193147756691991 534178108789721635037987)
                ·
                  refine ⟨801267163184582452556981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534178108789721635037987 801267163184582452556981)
                  ·
                    refine ⟨75118796548554604927217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801267163184582452556981 75118796548554604927217)
                    ·
                      refine ⟨56339097411415953695413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75118796548554604927217 56339097411415953695413)
                      ·
                        rfl

theorem cell23_109720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_109720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109720 prefixEnd_109720 := by exact prefixLift 109720
  have htrace : WordTrace (prefixWord ++ tailWord_109720) baseStart_109720 baseEnd_109720 := by
    simpa [prefixWord, tailWord_109720, baseEnd_109720] using wordTrace_append hprefix tailTrace_109720
  have hstable : (prefixWord ++ tailWord_109720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109720).length < 2 ^ (prefixWord ++ tailWord_109720).sum := by decide
  have hdescent : baseEnd_109720 < baseStart_109720 := by decide
  rcases family_descends (prefixWord ++ tailWord_109720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109743 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 4, 4]
def baseStart_109743 : Nat := 118140960795 + 109743 * 2 ^ 59
def prefixEnd_109743 : Nat := 4983230072969 + 3 ^ 40 * 109743 * 2
def baseEnd_109743 : Nat := 18783635822156454569269

theorem tailTrace_109743 : CollatzResearch.WordTrace tailWord_109743 prefixEnd_109743 18783635822156454569269 := by
  unfold tailWord_109743
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002656041427328457333883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668437360951552304889255 4002656041427328457333883)
  ·
    refine ⟨6003984062140992686000825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4002656041427328457333883 6003984062140992686000825)
    ·
      refine ⟨4502988046605744514500619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6003984062140992686000825 4502988046605744514500619)
      ·
        refine ⟨6754482069908616771750929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502988046605744514500619 6754482069908616771750929)
        ·
          refine ⟨5065861552431462578813197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6754482069908616771750929 5065861552431462578813197)
          ·
            refine ⟨1899698082161798467054949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5065861552431462578813197 1899698082161798467054949)
            ·
              refine ⟨356193390405337212572803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1899698082161798467054949 356193390405337212572803)
              ·
                refine ⟨534290085608005818859205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356193390405337212572803 534290085608005818859205)
                ·
                  refine ⟨100179391051501091036101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534290085608005818859205 100179391051501091036101)
                  ·
                    refine ⟨18783635822156454569269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100179391051501091036101 18783635822156454569269)
                    ·
                      rfl

theorem cell23_109743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_109743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109743 prefixEnd_109743 := by exact prefixLift 109743
  have htrace : WordTrace (prefixWord ++ tailWord_109743) baseStart_109743 baseEnd_109743 := by
    simpa [prefixWord, tailWord_109743, baseEnd_109743] using wordTrace_append hprefix tailTrace_109743
  have hstable : (prefixWord ++ tailWord_109743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109743).length < 2 ^ (prefixWord ++ tailWord_109743).sum := by decide
  have hdescent : baseEnd_109743 < baseStart_109743 := by decide
  rcases family_descends (prefixWord ++ tailWord_109743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109753 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_109753 : Nat := 118140960795 + 109753 * 2 ^ 59
def prefixEnd_109753 : Nat := 4983230072969 + 3 ^ 40 * 109753 * 2
def baseEnd_109753 : Nat := 56356042273014324582761

theorem tailTrace_109753 : CollatzResearch.WordTrace tailWord_109753 prefixEnd_109753 56356042273014324582761 := by
  unfold tailWord_109753
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003020771391100165197913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668680514260733443465275 4003020771391100165197913)
  ·
    refine ⟨3002265578543325123898435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4003020771391100165197913 3002265578543325123898435)
    ·
      refine ⟨4503398367814987685847653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002265578543325123898435 4503398367814987685847653)
      ·
        refine ⟨844387193965310191096435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4503398367814987685847653 844387193965310191096435)
        ·
          refine ⟨1266580790947965286644653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844387193965310191096435 1266580790947965286644653)
          ·
            refine ⟨474967796605486982491745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1266580790947965286644653 474967796605486982491745)
            ·
              refine ⟨356225847454115236868809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474967796605486982491745 356225847454115236868809)
              ·
                refine ⟨267169385590586427651607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356225847454115236868809 267169385590586427651607)
                ·
                  refine ⟨400754078385879641477411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267169385590586427651607 400754078385879641477411)
                  ·
                    refine ⟨601131117578819462216117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400754078385879641477411 601131117578819462216117)
                    ·
                      refine ⟨56356042273014324582761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 601131117578819462216117 56356042273014324582761)
                      ·
                        rfl

theorem cell23_109753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_109753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109753 prefixEnd_109753 := by exact prefixLift 109753
  have htrace : WordTrace (prefixWord ++ tailWord_109753) baseStart_109753 baseEnd_109753 := by
    simpa [prefixWord, tailWord_109753, baseEnd_109753] using wordTrace_append hprefix tailTrace_109753
  have hstable : (prefixWord ++ tailWord_109753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109753).length < 2 ^ (prefixWord ++ tailWord_109753).sum := by decide
  have hdescent : baseEnd_109753 < baseStart_109753 := by decide
  rcases family_descends (prefixWord ++ tailWord_109753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109764 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_109764 : Nat := 118140960795 + 109764 * 2 ^ 59
def prefixEnd_109764 : Nat := 4983230072969 + 3 ^ 40 * 109764 * 2
def baseEnd_109764 : Nat := 18787230186737927181737

theorem tailTrace_109764 : CollatzResearch.WordTrace tailWord_109764 prefixEnd_109764 18787230186737927181737 := by
  unfold tailWord_109764
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001710987175624521924173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2668947982900832695898897 2001710987175624521924173)
  ·
    refine ⟨750641620190859195721565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2001710987175624521924173 750641620190859195721565)
    ·
      refine ⟨281490607571572198395587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 750641620190859195721565 281490607571572198395587)
      ·
        refine ⟨422235911357358297593381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281490607571572198395587 422235911357358297593381)
        ·
          refine ⟨79169233379504680798759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422235911357358297593381 79169233379504680798759)
          ·
            refine ⟨118753850069257021198139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79169233379504680798759 118753850069257021198139)
            ·
              refine ⟨178130775103885531797209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118753850069257021198139 178130775103885531797209)
              ·
                refine ⟨133598081327914148847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178130775103885531797209 133598081327914148847907)
                ·
                  refine ⟨200397121991871223271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133598081327914148847907 200397121991871223271861)
                  ·
                    refine ⟨18787230186737927181737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200397121991871223271861 18787230186737927181737)
                    ·
                      rfl

theorem cell23_109764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_109764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109764 prefixEnd_109764 := by exact prefixLift 109764
  have htrace : WordTrace (prefixWord ++ tailWord_109764) baseStart_109764 baseEnd_109764 := by
    simpa [prefixWord, tailWord_109764, baseEnd_109764] using wordTrace_append hprefix tailTrace_109764
  have hstable : (prefixWord ++ tailWord_109764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109764).length < 2 ^ (prefixWord ++ tailWord_109764).sum := by decide
  have hdescent : baseEnd_109764 < baseStart_109764 := by decide
  rcases family_descends (prefixWord ++ tailWord_109764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109770 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_109770 : Nat := 118140960795 + 109770 * 2 ^ 59
def prefixEnd_109770 : Nat := 4983230072969 + 3 ^ 40 * 109770 * 2
def baseEnd_109770 : Nat := 56364771444140758070183

theorem tailTrace_109770 : CollatzResearch.WordTrace tailWord_109770 prefixEnd_109770 56364771444140758070183 := by
  unfold tailWord_109770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000910203082378017141691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2669093874886341379044509 1000910203082378017141691)
  ·
    refine ⟨1501365304623567025712537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000910203082378017141691 1501365304623567025712537)
    ·
      refine ⟨1126023978467675269284403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1501365304623567025712537 1126023978467675269284403)
      ·
        refine ⟨1689035967701512903926605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126023978467675269284403 1689035967701512903926605)
        ·
          refine ⟨633388487888067338972477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1689035967701512903926605 633388487888067338972477)
          ·
            refine ⟨237520682958025252114679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633388487888067338972477 237520682958025252114679)
            ·
              refine ⟨356281024437037878172019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237520682958025252114679 356281024437037878172019)
              ·
                refine ⟨534421536655556817258029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356281024437037878172019 534421536655556817258029)
                ·
                  refine ⟨200408076245833806471761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534421536655556817258029 200408076245833806471761)
                  ·
                    refine ⟨150306057184375354853821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200408076245833806471761 150306057184375354853821)
                    ·
                      refine ⟨56364771444140758070183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 150306057184375354853821 56364771444140758070183)
                      ·
                        rfl

theorem cell23_109770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_109770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109770 prefixEnd_109770 := by exact prefixLift 109770
  have htrace : WordTrace (prefixWord ++ tailWord_109770) baseStart_109770 baseEnd_109770 := by
    simpa [prefixWord, tailWord_109770, baseEnd_109770] using wordTrace_append hprefix tailTrace_109770
  have hstable : (prefixWord ++ tailWord_109770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109770).length < 2 ^ (prefixWord ++ tailWord_109770).sum := by decide
  have hdescent : baseEnd_109770 < baseStart_109770 := by decide
  rcases family_descends (prefixWord ++ tailWord_109770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109783 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_109783 : Nat := 118140960795 + 109783 * 2 ^ 59
def prefixEnd_109783 : Nat := 4983230072969 + 3 ^ 40 * 109783 * 2
def baseEnd_109783 : Nat := 56371446692649207207623

theorem tailTrace_109783 : CollatzResearch.WordTrace tailWord_109783 prefixEnd_109783 56371446692649207207623 := by
  unfold tailWord_109783
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004114961282415288790003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2669409974188276859193335 4004114961282415288790003)
  ·
    refine ⟨6006172441923622933185005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4004114961282415288790003 6006172441923622933185005)
    ·
      refine ⟨2252314665721358599944377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6006172441923622933185005 2252314665721358599944377)
      ·
        refine ⟨1689235999291018949958283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2252314665721358599944377 1689235999291018949958283)
        ·
          refine ⟨2533853998936528424937425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689235999291018949958283 2533853998936528424937425)
          ·
            refine ⟨1900390499202396318703069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533853998936528424937425 1900390499202396318703069)
            ·
              refine ⟨712646437200898619513651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900390499202396318703069 712646437200898619513651)
              ·
                refine ⟨1068969655801347929270477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712646437200898619513651 1068969655801347929270477)
                ·
                  refine ⟨400863620925505473476429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068969655801347929270477 400863620925505473476429)
                  ·
                    refine ⟨150323857847064552553661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400863620925505473476429 150323857847064552553661)
                    ·
                      refine ⟨56371446692649207207623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 150323857847064552553661 56371446692649207207623)
                      ·
                        rfl

theorem cell23_109783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_109783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109783 prefixEnd_109783 := by exact prefixLift 109783
  have htrace : WordTrace (prefixWord ++ tailWord_109783) baseStart_109783 baseEnd_109783 := by
    simpa [prefixWord, tailWord_109783, baseEnd_109783] using wordTrace_append hprefix tailTrace_109783
  have hstable : (prefixWord ++ tailWord_109783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109783).length < 2 ^ (prefixWord ++ tailWord_109783).sum := by decide
  have hdescent : baseEnd_109783 < baseStart_109783 := by decide
  rcases family_descends (prefixWord ++ tailWord_109783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109874 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_109874 : Nat := 118140960795 + 109874 * 2 ^ 59
def prefixEnd_109874 : Nat := 4983230072969 + 3 ^ 40 * 109874 * 2
def baseEnd_109874 : Nat := 56418173432208351169705

theorem tailTrace_109874 : CollatzResearch.WordTrace tailWord_109874 prefixEnd_109874 56418173432208351169705 := by
  unfold tailWord_109874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001858500988184457588169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2671622669301825220235117 1001858500988184457588169)
  ·
    refine ⟨751393875741138343191127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1001858500988184457588169 751393875741138343191127)
    ·
      refine ⟨1127090813611707514786691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751393875741138343191127 1127090813611707514786691)
      ·
        refine ⟨1690636220417561272180037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127090813611707514786691 1690636220417561272180037)
        ·
          refine ⟨316994291328292738533757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1690636220417561272180037 316994291328292738533757)
          ·
            refine ⟨118872859248109776950159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316994291328292738533757 118872859248109776950159)
            ·
              refine ⟨178309288872164665425239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118872859248109776950159 178309288872164665425239)
              ·
                refine ⟨267463933308246998137859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178309288872164665425239 267463933308246998137859)
                ·
                  refine ⟨401195899962370497206789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267463933308246998137859 401195899962370497206789)
                  ·
                    refine ⟨75224231242944468226273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401195899962370497206789 75224231242944468226273)
                    ·
                      refine ⟨56418173432208351169705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75224231242944468226273 56418173432208351169705)
                      ·
                        rfl

theorem cell23_109874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_109874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109874 prefixEnd_109874 := by exact prefixLift 109874
  have htrace : WordTrace (prefixWord ++ tailWord_109874) baseStart_109874 baseEnd_109874 := by
    simpa [prefixWord, tailWord_109874, baseEnd_109874] using wordTrace_append hprefix tailTrace_109874
  have hstable : (prefixWord ++ tailWord_109874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109874).length < 2 ^ (prefixWord ++ tailWord_109874).sum := by decide
  have hdescent : baseEnd_109874 < baseStart_109874 := by decide
  rcases family_descends (prefixWord ++ tailWord_109874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109878 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_109878 : Nat := 118140960795 + 109878 * 2 ^ 59
def prefixEnd_109878 : Nat := 4983230072969 + 3 ^ 40 * 109878 * 2
def baseEnd_109878 : Nat := 56420227354826335519687

theorem tailTrace_109878 : CollatzResearch.WordTrace tailWord_109878 prefixEnd_109878 56420227354826335519687 := by
  unfold tailWord_109878
  simp only [CollatzResearch.WordTrace]
  refine ⟨250473743496140407093643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2671719930625497675665525 250473743496140407093643)
  ·
    refine ⟨375710615244210610640465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250473743496140407093643 375710615244210610640465)
    ·
      refine ⟨281782961433157957980349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375710615244210610640465 281782961433157957980349)
      ·
        refine ⟨105668610537434234242631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281782961433157957980349 105668610537434234242631)
        ·
          refine ⟨158502915806151351363947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105668610537434234242631 158502915806151351363947)
          ·
            refine ⟨237754373709227027045921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158502915806151351363947 237754373709227027045921)
            ·
              refine ⟨178315780281920270284441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237754373709227027045921 178315780281920270284441)
              ·
                refine ⟨133736835211440202713331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178315780281920270284441 133736835211440202713331)
                ·
                  refine ⟨200605252817160304069997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133736835211440202713331 200605252817160304069997)
                  ·
                    refine ⟨75226969806435114026249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200605252817160304069997 75226969806435114026249)
                    ·
                      refine ⟨56420227354826335519687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75226969806435114026249 56420227354826335519687)
                      ·
                        rfl

theorem cell23_109878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_109878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109878 prefixEnd_109878 := by exact prefixLift 109878
  have htrace : WordTrace (prefixWord ++ tailWord_109878) baseStart_109878 baseEnd_109878 := by
    simpa [prefixWord, tailWord_109878, baseEnd_109878] using wordTrace_append hprefix tailTrace_109878
  have hstable : (prefixWord ++ tailWord_109878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109878).length < 2 ^ (prefixWord ++ tailWord_109878).sum := by decide
  have hdescent : baseEnd_109878 < baseStart_109878 := by decide
  rcases family_descends (prefixWord ++ tailWord_109878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109893 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_109893 : Nat := 118140960795 + 109893 * 2 ^ 59
def prefixEnd_109893 : Nat := 4983230072969 + 3 ^ 40 * 109893 * 2
def baseEnd_109893 : Nat := 18809309854881258944039

theorem tailTrace_109893 : CollatzResearch.WordTrace tailWord_109893 prefixEnd_109893 18809309854881258944039 := by
  unfold tailWord_109893
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008126990883904075294333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2672084660589269383529555 4008126990883904075294333)
  ·
    refine ⟨1503047621581464028235375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4008126990883904075294333 1503047621581464028235375)
    ·
      refine ⟨2254571432372196042353063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503047621581464028235375 2254571432372196042353063)
      ·
        refine ⟨3381857148558294063529595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254571432372196042353063 3381857148558294063529595)
        ·
          refine ⟨5072785722837441095294393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381857148558294063529595 5072785722837441095294393)
          ·
            refine ⟨3804589292128080821470795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072785722837441095294393 3804589292128080821470795)
            ·
              refine ⟨5706883938192121232206193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804589292128080821470795 5706883938192121232206193)
              ·
                refine ⟨4280162953644090924154645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706883938192121232206193 4280162953644090924154645)
                ·
                  refine ⟨200632638452066762069749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4280162953644090924154645 200632638452066762069749)
                  ·
                    refine ⟨18809309854881258944039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200632638452066762069749 18809309854881258944039)
                    ·
                      rfl

theorem cell23_109893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_109893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109893 prefixEnd_109893 := by exact prefixLift 109893
  have htrace : WordTrace (prefixWord ++ tailWord_109893) baseStart_109893 baseEnd_109893 := by
    simpa [prefixWord, tailWord_109893, baseEnd_109893] using wordTrace_append hprefix tailTrace_109893
  have hstable : (prefixWord ++ tailWord_109893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109893).length < 2 ^ (prefixWord ++ tailWord_109893).sum := by decide
  have hdescent : baseEnd_109893 < baseStart_109893 := by decide
  rcases family_descends (prefixWord ++ tailWord_109893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109920 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_109920 : Nat := 118140960795 + 109920 * 2 ^ 59
def prefixEnd_109920 : Nat := 4983230072969 + 3 ^ 40 * 109920 * 2
def baseEnd_109920 : Nat := 56441793542315171194493

theorem tailTrace_109920 : CollatzResearch.WordTrace tailWord_109920 prefixEnd_109920 56441793542315171194493 := by
  unfold tailWord_109920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004555880893043843263607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2672741174524058457684809 2004555880893043843263607)
  ·
    refine ⟨3006833821339565764895411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004555880893043843263607 3006833821339565764895411)
    ·
      refine ⟨4510250732009348647343117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3006833821339565764895411 4510250732009348647343117)
      ·
        refine ⟨1691344024503505742753669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4510250732009348647343117 1691344024503505742753669)
        ·
          refine ⟨317127004594407326766313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1691344024503505742753669 317127004594407326766313)
          ·
            refine ⟨237845253445805495074735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317127004594407326766313 237845253445805495074735)
            ·
              refine ⟨356767880168708242612103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237845253445805495074735 356767880168708242612103)
              ·
                refine ⟨535151820253062363918155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356767880168708242612103 535151820253062363918155)
                ·
                  refine ⟨802727730379593545877233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535151820253062363918155 802727730379593545877233)
                  ·
                    refine ⟨602045797784695159407925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802727730379593545877233 602045797784695159407925)
                    ·
                      refine ⟨56441793542315171194493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 602045797784695159407925 56441793542315171194493)
                      ·
                        rfl

theorem cell23_109920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_109920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_109920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_109920 prefixEnd_109920 := by exact prefixLift 109920
  have htrace : WordTrace (prefixWord ++ tailWord_109920) baseStart_109920 baseEnd_109920 := by
    simpa [prefixWord, tailWord_109920, baseEnd_109920] using wordTrace_append hprefix tailTrace_109920
  have hstable : (prefixWord ++ tailWord_109920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109920).length < 2 ^ (prefixWord ++ tailWord_109920).sum := by decide
  have hdescent : baseEnd_109920 < baseStart_109920 := by decide
  rcases family_descends (prefixWord ++ tailWord_109920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110007 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_110007 : Nat := 118140960795 + 110007 * 2 ^ 59
def prefixEnd_110007 : Nat := 4983230072969 + 3 ^ 40 * 110007 * 2
def baseEnd_110007 : Nat := 56486466359256330806593

theorem tailTrace_110007 : CollatzResearch.WordTrace tailWord_110007 prefixEnd_110007 56486466359256330806593 := by
  unfold tailWord_110007
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012284912470901544944275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2674856608313934363296183 4012284912470901544944275)
  ·
    refine ⟨6018427368706352317416413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012284912470901544944275 6018427368706352317416413)
    ·
      refine ⟨2256910263264882119031155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6018427368706352317416413 2256910263264882119031155)
      ·
        refine ⟨3385365394897323178546733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256910263264882119031155 3385365394897323178546733)
        ·
          refine ⟨1269512023086496191955025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3385365394897323178546733 1269512023086496191955025)
          ·
            refine ⟨952134017314872143966269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269512023086496191955025 952134017314872143966269)
            ·
              refine ⟨357050256493077053987351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952134017314872143966269 357050256493077053987351)
              ·
                refine ⟨535575384739615580981027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357050256493077053987351 535575384739615580981027)
                ·
                  refine ⟨803363077109423371471541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535575384739615580981027 803363077109423371471541)
                  ·
                    refine ⟨75315288479008441075457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 803363077109423371471541 75315288479008441075457)
                    ·
                      refine ⟨56486466359256330806593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75315288479008441075457 56486466359256330806593)
                      ·
                        rfl

theorem cell23_110007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_110007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110007 prefixEnd_110007 := by exact prefixLift 110007
  have htrace : WordTrace (prefixWord ++ tailWord_110007) baseStart_110007 baseEnd_110007 := by
    simpa [prefixWord, tailWord_110007, baseEnd_110007] using wordTrace_append hprefix tailTrace_110007
  have hstable : (prefixWord ++ tailWord_110007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110007).length < 2 ^ (prefixWord ++ tailWord_110007).sum := by decide
  have hdescent : baseEnd_110007 < baseStart_110007 := by decide
  rcases family_descends (prefixWord ++ tailWord_110007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110030 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_110030 : Nat := 118140960795 + 110030 * 2 ^ 59
def prefixEnd_110030 : Nat := 4983230072969 + 3 ^ 40 * 110030 * 2
def baseEnd_110030 : Nat := 18832758804769913606329

theorem tailTrace_110030 : CollatzResearch.WordTrace tailWord_110030 prefixEnd_110030 18832758804769913606329 := by
  unfold tailWord_110030
  simp only [CollatzResearch.WordTrace]
  refine ⟨501640473923447059128943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2675415860925050982021029 501640473923447059128943)
  ·
    refine ⟨752460710885170588693415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501640473923447059128943 752460710885170588693415)
    ·
      refine ⟨1128691066327755883040123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752460710885170588693415 1128691066327755883040123)
      ·
        refine ⟨1693036599491633824560185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128691066327755883040123 1693036599491633824560185)
        ·
          refine ⟨1269777449618725368420139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693036599491633824560185 1269777449618725368420139)
          ·
            refine ⟨1904666174428088052630209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269777449618725368420139 1904666174428088052630209)
            ·
              refine ⟨1428499630821066039472657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904666174428088052630209 1428499630821066039472657)
              ·
                refine ⟨1071374723115799529604493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428499630821066039472657 1071374723115799529604493)
                ·
                  refine ⟨401765521168424823601685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071374723115799529604493 401765521168424823601685)
                  ·
                    refine ⟨18832758804769913606329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 401765521168424823601685 18832758804769913606329)
                    ·
                      rfl

theorem cell23_110030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_110030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110030 prefixEnd_110030 := by exact prefixLift 110030
  have htrace : WordTrace (prefixWord ++ tailWord_110030) baseStart_110030 baseEnd_110030 := by
    simpa [prefixWord, tailWord_110030, baseEnd_110030] using wordTrace_append hprefix tailTrace_110030
  have hstable : (prefixWord ++ tailWord_110030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110030).length < 2 ^ (prefixWord ++ tailWord_110030).sum := by decide
  have hdescent : baseEnd_110030 < baseStart_110030 := by decide
  rcases family_descends (prefixWord ++ tailWord_110030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110040 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_110040 : Nat := 118140960795 + 110040 * 2 ^ 59
def prefixEnd_110040 : Nat := 4983230072969 + 3 ^ 40 * 110040 * 2
def baseEnd_110040 : Nat := 56503411220854701693941

theorem tailTrace_110040 : CollatzResearch.WordTrace tailWord_110040 prefixEnd_110040 56503411220854701693941 := by
  unfold tailWord_110040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006744260675674090447787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2675659014234232120597049 2006744260675674090447787)
  ·
    refine ⟨3010116391013511135671681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006744260675674090447787 3010116391013511135671681)
    ·
      refine ⟨2257587293260133351753761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3010116391013511135671681 2257587293260133351753761)
      ·
        refine ⟨1693190469945100013815321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2257587293260133351753761 1693190469945100013815321)
        ·
          refine ⟨1269892852458825010361491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693190469945100013815321 1269892852458825010361491)
          ·
            refine ⟨1904839278688237515542237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269892852458825010361491 1904839278688237515542237)
            ·
              refine ⟨714314729508089068328339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1904839278688237515542237 714314729508089068328339)
              ·
                refine ⟨1071472094262133602492509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714314729508089068328339 1071472094262133602492509)
                ·
                  refine ⟨401802035348300100934691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071472094262133602492509 401802035348300100934691)
                  ·
                    refine ⟨602703053022450151402037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 401802035348300100934691 602703053022450151402037)
                    ·
                      refine ⟨56503411220854701693941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 602703053022450151402037 56503411220854701693941)
                      ·
                        rfl

theorem cell23_110040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_110040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110040 prefixEnd_110040 := by exact prefixLift 110040
  have htrace : WordTrace (prefixWord ++ tailWord_110040) baseStart_110040 baseEnd_110040 := by
    simpa [prefixWord, tailWord_110040, baseEnd_110040] using wordTrace_append hprefix tailTrace_110040
  have hstable : (prefixWord ++ tailWord_110040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110040).length < 2 ^ (prefixWord ++ tailWord_110040).sum := by decide
  have hdescent : baseEnd_110040 < baseStart_110040 := by decide
  rcases family_descends (prefixWord ++ tailWord_110040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110071 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 1, 2, 2]
def baseStart_110071 : Nat := 118140960795 + 110071 * 2 ^ 59
def prefixEnd_110071 : Nat := 4983230072969 + 3 ^ 40 * 110071 * 2
def baseEnd_110071 : Nat := 56519329121144080406299

theorem tailTrace_110071 : CollatzResearch.WordTrace tailWord_110071 prefixEnd_110071 56519329121144080406299 := by
  unfold tailWord_110071
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014619184239040475274067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2676412789492693650182711 4014619184239040475274067)
  ·
    refine ⟨6021928776358560712911101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4014619184239040475274067 6021928776358560712911101)
    ·
      refine ⟨2258223291134460267341663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6021928776358560712911101 2258223291134460267341663)
      ·
        refine ⟨3387334936701690401012495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258223291134460267341663 3387334936701690401012495)
        ·
          refine ⟨5081002405052535601518743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387334936701690401012495 5081002405052535601518743)
          ·
            refine ⟨7621503607578803402278115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081002405052535601518743 7621503607578803402278115)
            ·
              refine ⟨11432255411368205103417173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621503607578803402278115 11432255411368205103417173)
              ·
                refine ⟨66985871550985576777835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11432255411368205103417173 66985871550985576777835)
                ·
                  refine ⟨100478807326478365166753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66985871550985576777835 100478807326478365166753)
                  ·
                    refine ⟨75359105494858773875065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100478807326478365166753 75359105494858773875065)
                    ·
                      refine ⟨56519329121144080406299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75359105494858773875065 56519329121144080406299)
                      ·
                        rfl

theorem cell23_110071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_110071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110071 prefixEnd_110071 := by exact prefixLift 110071
  have htrace : WordTrace (prefixWord ++ tailWord_110071) baseStart_110071 baseEnd_110071 := by
    simpa [prefixWord, tailWord_110071, baseEnd_110071] using wordTrace_append hprefix tailTrace_110071
  have hstable : (prefixWord ++ tailWord_110071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110071).length < 2 ^ (prefixWord ++ tailWord_110071).sum := by decide
  have hdescent : baseEnd_110071 < baseStart_110071 := by decide
  rcases family_descends (prefixWord ++ tailWord_110071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110161 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_110161 : Nat := 118140960795 + 110161 * 2 ^ 59
def prefixEnd_110161 : Nat := 4983230072969 + 3 ^ 40 * 110161 * 2
def baseEnd_110161 : Nat := 56565542380048728280885

theorem tailTrace_110161 : CollatzResearch.WordTrace tailWord_110161 prefixEnd_110161 56565542380048728280885 := by
  unfold tailWord_110161
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017901753912985846050337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2678601169275323897366891 4017901753912985846050337)
  ·
    refine ⟨3013426315434739384537753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4017901753912985846050337 3013426315434739384537753)
    ·
      refine ⟨2260069736576054538403315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3013426315434739384537753 2260069736576054538403315)
      ·
        refine ⟨3390104604864081807604973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260069736576054538403315 3390104604864081807604973)
        ·
          refine ⟨1271289226824030677851865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3390104604864081807604973 1271289226824030677851865)
          ·
            refine ⟨953466920118023008388899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271289226824030677851865 953466920118023008388899)
            ·
              refine ⟨1430200380177034512583349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953466920118023008388899 1430200380177034512583349)
              ·
                refine ⟨134081285641596985554689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1430200380177034512583349 134081285641596985554689)
                ·
                  refine ⟨100560964231197739166017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134081285641596985554689 100560964231197739166017)
                  ·
                    refine ⟨75420723173398304374513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100560964231197739166017 75420723173398304374513)
                    ·
                      refine ⟨56565542380048728280885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75420723173398304374513 56565542380048728280885)
                      ·
                        rfl

theorem cell23_110161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_110161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110161 prefixEnd_110161 := by exact prefixLift 110161
  have htrace : WordTrace (prefixWord ++ tailWord_110161) baseStart_110161 baseEnd_110161 := by
    simpa [prefixWord, tailWord_110161, baseEnd_110161] using wordTrace_append hprefix tailTrace_110161
  have hstable : (prefixWord ++ tailWord_110161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110161).length < 2 ^ (prefixWord ++ tailWord_110161).sum := by decide
  have hdescent : baseEnd_110161 < baseStart_110161 := by decide
  rcases family_descends (prefixWord ++ tailWord_110161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110167 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 7]
def baseStart_110167 : Nat := 118140960795 + 110167 * 2 ^ 59
def prefixEnd_110167 : Nat := 4983230072969 + 3 ^ 40 * 110167 * 2
def baseEnd_110167 : Nat := 6285402584886189422873

theorem tailTrace_110167 : CollatzResearch.WordTrace tailWord_110167 prefixEnd_110167 6285402584886189422873 := by
  unfold tailWord_110167
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018120591891248870768755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2678747061260832580512503 4018120591891248870768755)
  ·
    refine ⟨6027180887836873306153133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4018120591891248870768755 6027180887836873306153133)
    ·
      refine ⟨2260192832938827489807425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6027180887836873306153133 2260192832938827489807425)
      ·
        refine ⟨1695144624704120617355569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260192832938827489807425 1695144624704120617355569)
        ·
          refine ⟨1271358468528090463016677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1695144624704120617355569 1271358468528090463016677)
          ·
            refine ⟨238379712849016961815627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1271358468528090463016677 238379712849016961815627)
            ·
              refine ⟨357569569273525442723441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238379712849016961815627 357569569273525442723441)
              ·
                refine ⟨268177176955144082042581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357569569273525442723441 268177176955144082042581)
                ·
                  refine ⟨6285402584886189422873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268177176955144082042581 6285402584886189422873)
                  ·
                    rfl

theorem cell23_110167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 7].length) (baseStart_110167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110167 prefixEnd_110167 := by exact prefixLift 110167
  have htrace : WordTrace (prefixWord ++ tailWord_110167) baseStart_110167 baseEnd_110167 := by
    simpa [prefixWord, tailWord_110167, baseEnd_110167] using wordTrace_append hprefix tailTrace_110167
  have hstable : (prefixWord ++ tailWord_110167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110167).length < 2 ^ (prefixWord ++ tailWord_110167).sum := by decide
  have hdescent : baseEnd_110167 < baseStart_110167 := by decide
  rcases family_descends (prefixWord ++ tailWord_110167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110177 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_110177 : Nat := 118140960795 + 110177 * 2 ^ 59
def prefixEnd_110177 : Nat := 4983230072969 + 3 ^ 40 * 110177 * 2
def baseEnd_110177 : Nat := 56573758070520665680811

theorem tailTrace_110177 : CollatzResearch.WordTrace tailWord_110177 prefixEnd_110177 56573758070520665680811 := by
  unfold tailWord_110177
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018485321855020578632785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2678990214570013719088523 4018485321855020578632785)
  ·
    refine ⟨3013863991391265433974589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4018485321855020578632785 3013863991391265433974589)
    ·
      refine ⟨1130198996771724537740471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3013863991391265433974589 1130198996771724537740471)
      ·
        refine ⟨1695298495157586806610707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130198996771724537740471 1695298495157586806610707)
        ·
          refine ⟨2542947742736380209916061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695298495157586806610707 2542947742736380209916061)
          ·
            refine ⟨953605403526142578718523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2542947742736380209916061 953605403526142578718523)
            ·
              refine ⟨1430408105289213868077785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953605403526142578718523 1430408105289213868077785)
              ·
                refine ⟨1072806078966910401058339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430408105289213868077785 1072806078966910401058339)
                ·
                  refine ⟨1609209118450365601587509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072806078966910401058339 1609209118450365601587509)
                  ·
                    refine ⟨150863354854721775148829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1609209118450365601587509 150863354854721775148829)
                    ·
                      refine ⟨56573758070520665680811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 150863354854721775148829 56573758070520665680811)
                      ·
                        rfl

theorem cell23_110177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_110177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110177 prefixEnd_110177 := by exact prefixLift 110177
  have htrace : WordTrace (prefixWord ++ tailWord_110177) baseStart_110177 baseEnd_110177 := by
    simpa [prefixWord, tailWord_110177, baseEnd_110177] using wordTrace_append hprefix tailTrace_110177
  have hstable : (prefixWord ++ tailWord_110177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110177).length < 2 ^ (prefixWord ++ tailWord_110177).sum := by decide
  have hdescent : baseEnd_110177 < baseStart_110177 := by decide
  rcases family_descends (prefixWord ++ tailWord_110177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110194 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_110194 : Nat := 118140960795 + 110194 * 2 ^ 59
def prefixEnd_110194 : Nat := 4983230072969 + 3 ^ 40 * 110194 * 2
def baseEnd_110194 : Nat := 56582487241647099168233

theorem tailTrace_110194 : CollatzResearch.WordTrace tailWord_110194 prefixEnd_110194 56582487241647099168233 := by
  unfold tailWord_110194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004776340698358120500409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2679403575195621654667757 1004776340698358120500409)
  ·
    refine ⟨753582255523768590375307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1004776340698358120500409 753582255523768590375307)
    ·
      refine ⟨1130373383285652885562961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753582255523768590375307 1130373383285652885562961)
      ·
        refine ⟨847780037464239664172221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130373383285652885562961 847780037464239664172221)
        ·
          refine ⟨317917514049089874064583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847780037464239664172221 317917514049089874064583)
          ·
            refine ⟨476876271073634811096875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317917514049089874064583 476876271073634811096875)
            ·
              refine ⟨715314406610452216645313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476876271073634811096875 715314406610452216645313)
              ·
                refine ⟨536485804957839162483985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715314406610452216645313 536485804957839162483985)
                ·
                  refine ⟨402364353718379371862989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536485804957839162483985 402364353718379371862989)
                  ·
                    refine ⟨150886632644392264448621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402364353718379371862989 150886632644392264448621)
                    ·
                      refine ⟨56582487241647099168233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 150886632644392264448621 56582487241647099168233)
                      ·
                        rfl

theorem cell23_110194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_110194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110194 prefixEnd_110194 := by exact prefixLift 110194
  have htrace : WordTrace (prefixWord ++ tailWord_110194) baseStart_110194 baseEnd_110194 := by
    simpa [prefixWord, tailWord_110194, baseEnd_110194] using wordTrace_append hprefix tailTrace_110194
  have hstable : (prefixWord ++ tailWord_110194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110194).length < 2 ^ (prefixWord ++ tailWord_110194).sum := by decide
  have hdescent : baseEnd_110194 < baseStart_110194 := by decide
  rcases family_descends (prefixWord ++ tailWord_110194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110217 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_110217 : Nat := 118140960795 + 110217 * 2 ^ 59
def prefixEnd_110217 : Nat := 4983230072969 + 3 ^ 40 * 110217 * 2
def baseEnd_110217 : Nat := 56594297296700509180627

theorem tailTrace_110217 : CollatzResearch.WordTrace tailWord_110217 prefixEnd_110217 56594297296700509180627 := by
  unfold tailWord_110217
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019944241710107410088905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2679962827806738273392603 4019944241710107410088905)
  ·
    refine ⟨3014958181282580557566679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4019944241710107410088905 3014958181282580557566679)
    ·
      refine ⟨4522437271923870836350019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014958181282580557566679 4522437271923870836350019)
      ·
        refine ⟨6783655907885806254525029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522437271923870836350019 6783655907885806254525029)
        ·
          refine ⟨1271935482728588672723443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6783655907885806254525029 1271935482728588672723443)
          ·
            refine ⟨1907903224092883009085165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271935482728588672723443 1907903224092883009085165)
            ·
              refine ⟨715463709034831128406937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1907903224092883009085165 715463709034831128406937)
              ·
                refine ⟨536597781776123346305203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715463709034831128406937 536597781776123346305203)
                ·
                  refine ⟨804896672664185019457805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536597781776123346305203 804896672664185019457805)
                  ·
                    refine ⟨301836252249069382296677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804896672664185019457805 301836252249069382296677)
                    ·
                      refine ⟨56594297296700509180627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 301836252249069382296677 56594297296700509180627)
                      ·
                        rfl

theorem cell23_110217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_110217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110217 prefixEnd_110217 := by exact prefixLift 110217
  have htrace : WordTrace (prefixWord ++ tailWord_110217) baseStart_110217 baseEnd_110217 := by
    simpa [prefixWord, tailWord_110217, baseEnd_110217] using wordTrace_append hprefix tailTrace_110217
  have hstable : (prefixWord ++ tailWord_110217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110217).length < 2 ^ (prefixWord ++ tailWord_110217).sum := by decide
  have hdescent : baseEnd_110217 < baseStart_110217 := by decide
  rcases family_descends (prefixWord ++ tailWord_110217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110237 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_110237 : Nat := 118140960795 + 110237 * 2 ^ 59
def prefixEnd_110237 : Nat := 4983230072969 + 3 ^ 40 * 110237 * 2
def baseEnd_110237 : Nat := 56604566909790430930535

theorem tailTrace_110237 : CollatzResearch.WordTrace tailWord_110237 prefixEnd_110237 56604566909790430930535 := by
  unfold tailWord_110237
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020673701637650825816965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2680449134425100550544643 4020673701637650825816965)
  ·
    refine ⟨753876319057059529840681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4020673701637650825816965 753876319057059529840681)
    ·
      refine ⟨565407239292794647380511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 753876319057059529840681 565407239292794647380511)
      ·
        refine ⟨848110858939191971070767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565407239292794647380511 848110858939191971070767)
        ·
          refine ⟨1272166288408787956606151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848110858939191971070767 1272166288408787956606151)
          ·
            refine ⟨1908249432613181934909227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272166288408787956606151 1908249432613181934909227)
            ·
              refine ⟨2862374148919772902363841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908249432613181934909227 2862374148919772902363841)
              ·
                refine ⟨2146780611689829676772881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862374148919772902363841 2146780611689829676772881)
                ·
                  refine ⟨1610085458767372257579661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146780611689829676772881 1610085458767372257579661)
                  ·
                    refine ⟨603782047037764596592373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610085458767372257579661 603782047037764596592373)
                    ·
                      refine ⟨56604566909790430930535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 603782047037764596592373 56604566909790430930535)
                      ·
                        rfl

theorem cell23_110237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_110237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110237 prefixEnd_110237 := by exact prefixLift 110237
  have htrace : WordTrace (prefixWord ++ tailWord_110237) baseStart_110237 baseEnd_110237 := by
    simpa [prefixWord, tailWord_110237, baseEnd_110237] using wordTrace_append hprefix tailTrace_110237
  have hstable : (prefixWord ++ tailWord_110237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110237).length < 2 ^ (prefixWord ++ tailWord_110237).sum := by decide
  have hdescent : baseEnd_110237 < baseStart_110237 := by decide
  rcases family_descends (prefixWord ++ tailWord_110237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110304 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_110304 : Nat := 118140960795 + 110304 * 2 ^ 59
def prefixEnd_110304 : Nat := 4983230072969 + 3 ^ 40 * 110304 * 2
def baseEnd_110304 : Nat := 18879656704547222930909

theorem tailTrace_110304 : CollatzResearch.WordTrace tailWord_110304 prefixEnd_110304 18879656704547222930909 := by
  unfold tailWord_110304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011558696197460634252983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2682078261596614179003977 2011558696197460634252983)
  ·
    refine ⟨3017338044296190951379475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011558696197460634252983 3017338044296190951379475)
    ·
      refine ⟨4526007066444286427069213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3017338044296190951379475 4526007066444286427069213)
      ·
        refine ⟨1697252649916607410150955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4526007066444286427069213 1697252649916607410150955)
        ·
          refine ⟨2545878974874911115226433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697252649916607410150955 2545878974874911115226433)
          ·
            refine ⟨1909409231156183336419825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2545878974874911115226433 1909409231156183336419825)
            ·
              refine ⟨1432056923367137502314869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909409231156183336419825 1432056923367137502314869)
              ·
                refine ⟨134255336565669140842019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1432056923367137502314869 134255336565669140842019)
                ·
                  refine ⟨201383004848503711263029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134255336565669140842019 201383004848503711263029)
                  ·
                    refine ⟨18879656704547222930909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201383004848503711263029 18879656704547222930909)
                    ·
                      rfl

theorem cell23_110304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_110304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110304 prefixEnd_110304 := by exact prefixLift 110304
  have htrace : WordTrace (prefixWord ++ tailWord_110304) baseStart_110304 baseEnd_110304 := by
    simpa [prefixWord, tailWord_110304, baseEnd_110304] using wordTrace_append hprefix tailTrace_110304
  have hstable : (prefixWord ++ tailWord_110304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110304).length < 2 ^ (prefixWord ++ tailWord_110304).sum := by decide
  have hdescent : baseEnd_110304 < baseStart_110304 := by decide
  rcases family_descends (prefixWord ++ tailWord_110304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110347 : List Nat := [1, 1, 1, 1, 5, 1, 2, 11]
def baseStart_110347 : Nat := 118140960795 + 110347 * 2 ^ 59
def prefixEnd_110347 : Nat := 4983230072969 + 3 ^ 40 * 110347 * 2
def baseEnd_110347 : Nat := 2098557399325370390927

theorem tailTrace_110347 : CollatzResearch.WordTrace tailWord_110347 prefixEnd_110347 2098557399325370390927 := by
  unfold tailWord_110347
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024685731239139612321295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2683123820826093074880863 4024685731239139612321295)
  ·
    refine ⟨6037028596858709418481943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4024685731239139612321295 6037028596858709418481943)
    ·
      refine ⟨9055542895288064127722915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037028596858709418481943 9055542895288064127722915)
      ·
        refine ⟨13583314342932096191584373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055542895288064127722915 13583314342932096191584373)
        ·
          refine ⟨1273435719649884017961035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13583314342932096191584373 1273435719649884017961035)
          ·
            refine ⟨1910153579474826026941553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273435719649884017961035 1910153579474826026941553)
            ·
              refine ⟨1432615184606119520206165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910153579474826026941553 1432615184606119520206165)
              ·
                refine ⟨2098557399325370390927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1432615184606119520206165 2098557399325370390927)
                ·
                  rfl

theorem cell23_110347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 11].length) (baseStart_110347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110347 prefixEnd_110347 := by exact prefixLift 110347
  have htrace : WordTrace (prefixWord ++ tailWord_110347) baseStart_110347 baseEnd_110347 := by
    simpa [prefixWord, tailWord_110347, baseEnd_110347] using wordTrace_append hprefix tailTrace_110347
  have hstable : (prefixWord ++ tailWord_110347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110347).length < 2 ^ (prefixWord ++ tailWord_110347).sum := by decide
  have hdescent : baseEnd_110347 < baseStart_110347 := by decide
  rcases family_descends (prefixWord ++ tailWord_110347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110388 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_110388 : Nat := 118140960795 + 110388 * 2 ^ 59
def prefixEnd_110388 : Nat := 4983230072969 + 3 ^ 40 * 110388 * 2
def baseEnd_110388 : Nat := 56682102488619340142341

theorem tailTrace_110388 : CollatzResearch.WordTrace tailWord_110388 prefixEnd_110388 56682102488619340142341 := by
  unfold tailWord_110388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2013090562045301807281909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2684120749393735743042545 2013090562045301807281909)
  ·
    refine ⟨188727240191747044432679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2013090562045301807281909 188727240191747044432679)
    ·
      refine ⟨283090860287620566649019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188727240191747044432679 283090860287620566649019)
      ·
        refine ⟨424636290431430849973529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283090860287620566649019 424636290431430849973529)
        ·
          refine ⟨318477217823573137480147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424636290431430849973529 318477217823573137480147)
          ·
            refine ⟨477715826735359706220221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318477217823573137480147 477715826735359706220221)
            ·
              refine ⟨179143435025759889832583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 477715826735359706220221 179143435025759889832583)
              ·
                refine ⟨268715152538639834748875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179143435025759889832583 268715152538639834748875)
                ·
                  refine ⟨403072728807959752123313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268715152538639834748875 403072728807959752123313)
                  ·
                    refine ⟨302304546605969814092485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403072728807959752123313 302304546605969814092485)
                    ·
                      refine ⟨56682102488619340142341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 302304546605969814092485 56682102488619340142341)
                      ·
                        rfl

theorem cell23_110388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_110388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110388 prefixEnd_110388 := by exact prefixLift 110388
  have htrace : WordTrace (prefixWord ++ tailWord_110388) baseStart_110388 baseEnd_110388 := by
    simpa [prefixWord, tailWord_110388, baseEnd_110388] using wordTrace_append hprefix tailTrace_110388
  have hstable : (prefixWord ++ tailWord_110388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110388).length < 2 ^ (prefixWord ++ tailWord_110388).sum := by decide
  have hdescent : baseEnd_110388 < baseStart_110388 := by decide
  rcases family_descends (prefixWord ++ tailWord_110388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110398 : List Nat := [4, 2, 1, 2, 2, 3, 2, 7]
def baseStart_110398 : Nat := 118140960795 + 110398 * 2 ^ 59
def prefixEnd_110398 : Nat := 4983230072969 + 3 ^ 40 * 110398 * 2
def baseEnd_110398 : Nat := 2099527307228307445085

theorem tailTrace_110398 : CollatzResearch.WordTrace tailWord_110398 prefixEnd_110398 2099527307228307445085 := by
  unfold tailWord_110398
  simp only [CollatzResearch.WordTrace]
  refine ⟨503318231756796915303481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2684363902702916881618565 503318231756796915303481)
  ·
    refine ⟨377488673817597686477611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 503318231756796915303481 377488673817597686477611)
    ·
      refine ⟨566233010726396529716417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377488673817597686477611 566233010726396529716417)
      ·
        refine ⟨424674758044797397287313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566233010726396529716417 424674758044797397287313)
        ·
          refine ⟨318506068533598047965485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424674758044797397287313 318506068533598047965485)
          ·
            refine ⟨119439775700099267987057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318506068533598047965485 119439775700099267987057)
            ·
              refine ⟨89579831775074450990293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119439775700099267987057 89579831775074450990293)
              ·
                refine ⟨2099527307228307445085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89579831775074450990293 2099527307228307445085)
                ·
                  rfl

theorem cell23_110398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_110398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110398 prefixEnd_110398 := by exact prefixLift 110398
  have htrace : WordTrace (prefixWord ++ tailWord_110398) baseStart_110398 baseEnd_110398 := by
    simpa [prefixWord, tailWord_110398, baseEnd_110398] using wordTrace_append hprefix tailTrace_110398
  have hstable : (prefixWord ++ tailWord_110398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110398).length < 2 ^ (prefixWord ++ tailWord_110398).sum := by decide
  have hdescent : baseEnd_110398 < baseStart_110398 := by decide
  rcases family_descends (prefixWord ++ tailWord_110398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110414 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_110414 : Nat := 118140960795 + 110414 * 2 ^ 59
def prefixEnd_110414 : Nat := 4983230072969 + 3 ^ 40 * 110414 * 2
def baseEnd_110414 : Nat := 56695452985636238417221

theorem tailTrace_110414 : CollatzResearch.WordTrace tailWord_110414 prefixEnd_110414 56695452985636238417221 := by
  unfold tailWord_110414
  simp only [CollatzResearch.WordTrace]
  refine ⟨503391177749551256876287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2684752947997606703340197 503391177749551256876287)
  ·
    refine ⟨755086766624326885314431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503391177749551256876287 755086766624326885314431)
    ·
      refine ⟨1132630149936490327971647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755086766624326885314431 1132630149936490327971647)
      ·
        refine ⟨1698945224904735491957471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132630149936490327971647 1698945224904735491957471)
        ·
          refine ⟨2548417837357103237936207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698945224904735491957471 2548417837357103237936207)
          ·
            refine ⟨3822626756035654856904311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548417837357103237936207 3822626756035654856904311)
            ·
              refine ⟨5733940134053482285356467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822626756035654856904311 5733940134053482285356467)
              ·
                refine ⟨8600910201080223428034701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733940134053482285356467 8600910201080223428034701)
                ·
                  refine ⟨3225341325405083785513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8600910201080223428034701 3225341325405083785513013)
                  ·
                    refine ⟨302375749256726604891845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3225341325405083785513013 302375749256726604891845)
                    ·
                      refine ⟨56695452985636238417221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 302375749256726604891845 56695452985636238417221)
                      ·
                        rfl

theorem cell23_110414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_110414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110414 prefixEnd_110414 := by exact prefixLift 110414
  have htrace : WordTrace (prefixWord ++ tailWord_110414) baseStart_110414 baseEnd_110414 := by
    simpa [prefixWord, tailWord_110414, baseEnd_110414] using wordTrace_append hprefix tailTrace_110414
  have hstable : (prefixWord ++ tailWord_110414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110414).length < 2 ^ (prefixWord ++ tailWord_110414).sum := by decide
  have hdescent : baseEnd_110414 < baseStart_110414 := by decide
  rcases family_descends (prefixWord ++ tailWord_110414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110442 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_110442 : Nat := 118140960795 + 110442 * 2 ^ 59
def prefixEnd_110442 : Nat := 4983230072969 + 3 ^ 40 * 110442 * 2
def baseEnd_110442 : Nat := 56709830443962128867093

theorem tailTrace_110442 : CollatzResearch.WordTrace tailWord_110442 prefixEnd_110442 56709830443962128867093 := by
  unfold tailWord_110442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007037666473742709257395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2685433777263313891353053 1007037666473742709257395)
  ·
    refine ⟨1510556499710614063886093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007037666473742709257395 1510556499710614063886093)
    ·
      refine ⟨566458687391480273957285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1510556499710614063886093 566458687391480273957285)
      ·
        refine ⟨106211003885902551366991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566458687391480273957285 106211003885902551366991)
        ·
          refine ⟨159316505828853827050487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106211003885902551366991 159316505828853827050487)
          ·
            refine ⟨238974758743280740575731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159316505828853827050487 238974758743280740575731)
            ·
              refine ⟨358462138114921110863597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238974758743280740575731 358462138114921110863597)
              ·
                refine ⟨134423301793095416573849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358462138114921110863597 134423301793095416573849)
                ·
                  refine ⟨100817476344821562430387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134423301793095416573849 100817476344821562430387)
                  ·
                    refine ⟨151226214517232343645581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100817476344821562430387 151226214517232343645581)
                    ·
                      refine ⟨56709830443962128867093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 151226214517232343645581 56709830443962128867093)
                      ·
                        rfl

theorem cell23_110442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_110442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110442 prefixEnd_110442 := by exact prefixLift 110442
  have htrace : WordTrace (prefixWord ++ tailWord_110442) baseStart_110442 baseEnd_110442 := by
    simpa [prefixWord, tailWord_110442, baseEnd_110442] using wordTrace_append hprefix tailTrace_110442
  have hstable : (prefixWord ++ tailWord_110442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110442).length < 2 ^ (prefixWord ++ tailWord_110442).sum := by decide
  have hdescent : baseEnd_110442 < baseStart_110442 := by decide
  rcases family_descends (prefixWord ++ tailWord_110442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110482 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_110482 : Nat := 118140960795 + 110482 * 2 ^ 59
def prefixEnd_110482 : Nat := 4983230072969 + 3 ^ 40 * 110482 * 2
def baseEnd_110482 : Nat := 56730369670141972366909

theorem tailTrace_110482 : CollatzResearch.WordTrace tailWord_110482 prefixEnd_110482 56730369670141972366909 := by
  unfold tailWord_110482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007402396437514417121425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2686406390500038445657133 1007402396437514417121425)
  ·
    refine ⟨755551797328135812841069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1007402396437514417121425 755551797328135812841069)
    ·
      refine ⟨283331923998050929815401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 755551797328135812841069 283331923998050929815401)
      ·
        refine ⟨212498942998538197361551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283331923998050929815401 212498942998538197361551)
        ·
          refine ⟨318748414497807296042327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212498942998538197361551 318748414497807296042327)
          ·
            refine ⟨478122621746710944063491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318748414497807296042327 478122621746710944063491)
            ·
              refine ⟨717183932620066416095237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478122621746710944063491 717183932620066416095237)
              ·
                refine ⟨134471987366262453017857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717183932620066416095237 134471987366262453017857)
                ·
                  refine ⟨100853990524696839763393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134471987366262453017857 100853990524696839763393)
                  ·
                    refine ⟨75640492893522629822545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100853990524696839763393 75640492893522629822545)
                    ·
                      refine ⟨56730369670141972366909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75640492893522629822545 56730369670141972366909)
                      ·
                        rfl

theorem cell23_110482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_110482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110482 prefixEnd_110482 := by exact prefixLift 110482
  have htrace : WordTrace (prefixWord ++ tailWord_110482) baseStart_110482 baseEnd_110482 := by
    simpa [prefixWord, tailWord_110482, baseEnd_110482] using wordTrace_append hprefix tailTrace_110482
  have hstable : (prefixWord ++ tailWord_110482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110482).length < 2 ^ (prefixWord ++ tailWord_110482).sum := by decide
  have hdescent : baseEnd_110482 < baseStart_110482 := by decide
  rcases family_descends (prefixWord ++ tailWord_110482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110521 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_110521 : Nat := 118140960795 + 110521 * 2 ^ 59
def prefixEnd_110521 : Nat := 4983230072969 + 3 ^ 40 * 110521 * 2
def baseEnd_110521 : Nat := 56750395415667319779229

theorem tailTrace_110521 : CollatzResearch.WordTrace tailWord_110521 prefixEnd_110521 56750395415667319779229 := by
  unfold tailWord_110521
  simp only [CollatzResearch.WordTrace]
  refine ⟨4031032032608767329155417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2687354688405844886103611 4031032032608767329155417)
  ·
    refine ⟨3023274024456575496866563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4031032032608767329155417 3023274024456575496866563)
    ·
      refine ⟨4534911036684863245299845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023274024456575496866563 4534911036684863245299845)
      ·
        refine ⟨850295819378411858493721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4534911036684863245299845 850295819378411858493721)
        ·
          refine ⟨637721864533808893870291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850295819378411858493721 637721864533808893870291)
          ·
            refine ⟨956582796800713340805437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637721864533808893870291 956582796800713340805437)
            ·
              refine ⟨358718548800267502802039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956582796800713340805437 358718548800267502802039)
              ·
                refine ⟨538077823200401254203059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358718548800267502802039 538077823200401254203059)
                ·
                  refine ⟨807116734800601881304589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538077823200401254203059 807116734800601881304589)
                  ·
                    refine ⟨302668775550225705489221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807116734800601881304589 302668775550225705489221)
                    ·
                      refine ⟨56750395415667319779229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 302668775550225705489221 56750395415667319779229)
                      ·
                        rfl

theorem cell23_110521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_110521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110521 prefixEnd_110521 := by exact prefixLift 110521
  have htrace : WordTrace (prefixWord ++ tailWord_110521) baseStart_110521 baseEnd_110521 := by
    simpa [prefixWord, tailWord_110521, baseEnd_110521] using wordTrace_append hprefix tailTrace_110521
  have hstable : (prefixWord ++ tailWord_110521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110521).length < 2 ^ (prefixWord ++ tailWord_110521).sum := by decide
  have hdescent : baseEnd_110521 < baseStart_110521 := by decide
  rcases family_descends (prefixWord ++ tailWord_110521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110538 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_110538 : Nat := 118140960795 + 110538 * 2 ^ 59
def prefixEnd_110538 : Nat := 4983230072969 + 3 ^ 40 * 110538 * 2
def baseEnd_110538 : Nat := 56759124586793753266651

theorem tailTrace_110538 : CollatzResearch.WordTrace tailWord_110538 prefixEnd_110538 56759124586793753266651 := by
  unfold tailWord_110538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007913018386794808131067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2687768049031452821682845 1007913018386794808131067)
  ·
    refine ⟨1511869527580192212196601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007913018386794808131067 1511869527580192212196601)
    ·
      refine ⟨1133902145685144159147451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1511869527580192212196601 1133902145685144159147451)
      ·
        refine ⟨1700853218527716238721177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133902145685144159147451 1700853218527716238721177)
        ·
          refine ⟨1275639913895787179040883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700853218527716238721177 1275639913895787179040883)
          ·
            refine ⟨1913459870843680768561325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275639913895787179040883 1913459870843680768561325)
            ·
              refine ⟨717547451566380288210497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913459870843680768561325 717547451566380288210497)
              ·
                refine ⟨538160588674785216157873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717547451566380288210497 538160588674785216157873)
                ·
                  refine ⟨403620441506088912118405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538160588674785216157873 403620441506088912118405)
                  ·
                    refine ⟨75678832782391671022201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 403620441506088912118405 75678832782391671022201)
                    ·
                      refine ⟨56759124586793753266651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75678832782391671022201 56759124586793753266651)
                      ·
                        rfl

theorem cell23_110538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_110538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110538 prefixEnd_110538 := by exact prefixLift 110538
  have htrace : WordTrace (prefixWord ++ tailWord_110538) baseStart_110538 baseEnd_110538 := by
    simpa [prefixWord, tailWord_110538, baseEnd_110538] using wordTrace_append hprefix tailTrace_110538
  have hstable : (prefixWord ++ tailWord_110538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110538).length < 2 ^ (prefixWord ++ tailWord_110538).sum := by decide
  have hdescent : baseEnd_110538 < baseStart_110538 := by decide
  rcases family_descends (prefixWord ++ tailWord_110538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110561 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 6]
def baseStart_110561 : Nat := 118140960795 + 110561 * 2 ^ 59
def prefixEnd_110561 : Nat := 4983230072969 + 3 ^ 40 * 110561 * 2
def baseEnd_110561 : Nat := 6307881626871907031005

theorem tailTrace_110561 : CollatzResearch.WordTrace tailWord_110561 prefixEnd_110561 6307881626871907031005 := by
  unfold tailWord_110561
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032490952463854160611537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2688327301642569440407691 4032490952463854160611537)
  ·
    refine ⟨3024368214347890620458653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4032490952463854160611537 3024368214347890620458653)
    ·
      refine ⟨1134138080380458982671995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3024368214347890620458653 1134138080380458982671995)
      ·
        refine ⟨1701207120570688474007993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134138080380458982671995 1701207120570688474007993)
        ·
          refine ⟨1275905340428016355505995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701207120570688474007993 1275905340428016355505995)
          ·
            refine ⟨1913858010642024533258993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275905340428016355505995 1913858010642024533258993)
            ·
              refine ⟨1435393507981518399944245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913858010642024533258993 1435393507981518399944245)
              ·
                refine ⟨134568141373267349994773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1435393507981518399944245 134568141373267349994773)
                ·
                  refine ⟨6307881626871907031005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134568141373267349994773 6307881626871907031005)
                  ·
                    rfl

theorem cell23_110561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_110561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110561 prefixEnd_110561 := by exact prefixLift 110561
  have htrace : WordTrace (prefixWord ++ tailWord_110561) baseStart_110561 baseEnd_110561 := by
    simpa [prefixWord, tailWord_110561, baseEnd_110561] using wordTrace_append hprefix tailTrace_110561
  have hstable : (prefixWord ++ tailWord_110561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110561).length < 2 ^ (prefixWord ++ tailWord_110561).sum := by decide
  have hdescent : baseEnd_110561 < baseStart_110561 := by decide
  rcases family_descends (prefixWord ++ tailWord_110561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110612 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 6]
def baseStart_110612 : Nat := 118140960795 + 110612 * 2 ^ 59
def prefixEnd_110612 : Nat := 4983230072969 + 3 ^ 40 * 110612 * 2
def baseEnd_110612 : Nat := 6310791350580718193479

theorem tailTrace_110612 : CollatzResearch.WordTrace tailWord_110612 prefixEnd_110612 6310791350580718193479 := by
  unfold tailWord_110612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017175537639544935359045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2689567383519393247145393 2017175537639544935359045)
  ·
    refine ⟨378220413307414675379821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2017175537639544935359045 378220413307414675379821)
    ·
      refine ⟨141832654990280503267433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378220413307414675379821 141832654990280503267433)
      ·
        refine ⟨106374491242710377450575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141832654990280503267433 106374491242710377450575)
        ·
          refine ⟨159561736864065566175863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106374491242710377450575 159561736864065566175863)
          ·
            refine ⟨239342605296098349263795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159561736864065566175863 239342605296098349263795)
            ·
              refine ⟨359013907944147523895693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239342605296098349263795 359013907944147523895693)
              ·
                refine ⟨134630215479055321460885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359013907944147523895693 134630215479055321460885)
                ·
                  refine ⟨6310791350580718193479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134630215479055321460885 6310791350580718193479)
                  ·
                    rfl

theorem cell23_110612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_110612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110612 prefixEnd_110612 := by exact prefixLift 110612
  have htrace : WordTrace (prefixWord ++ tailWord_110612) baseStart_110612 baseEnd_110612 := by
    simpa [prefixWord, tailWord_110612, baseEnd_110612] using wordTrace_append hprefix tailTrace_110612
  have hstable : (prefixWord ++ tailWord_110612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110612).length < 2 ^ (prefixWord ++ tailWord_110612).sum := by decide
  have hdescent : baseEnd_110612 < baseStart_110612 := by decide
  rcases family_descends (prefixWord ++ tailWord_110612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110638 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_110638 : Nat := 118140960795 + 110638 * 2 ^ 59
def prefixEnd_110638 : Nat := 4983230072969 + 3 ^ 40 * 110638 * 2
def baseEnd_110638 : Nat := 18936824217414454005397

theorem tailTrace_110638 : CollatzResearch.WordTrace tailWord_110638 prefixEnd_110638 18936824217414454005397 := by
  unfold tailWord_110638
  simp only [CollatzResearch.WordTrace]
  refine ⟨504412421648112038895571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2690199582123264207443045 504412421648112038895571)
  ·
    refine ⟨756618632472168058343357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 504412421648112038895571 756618632472168058343357)
    ·
      refine ⟨283731987177063021878759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 756618632472168058343357 283731987177063021878759)
      ·
        refine ⟨425597980765594532818139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283731987177063021878759 425597980765594532818139)
        ·
          refine ⟨638396971148391799227209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425597980765594532818139 638396971148391799227209)
          ·
            refine ⟨478797728361293849420407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638396971148391799227209 478797728361293849420407)
            ·
              refine ⟨718196592541940774130611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478797728361293849420407 718196592541940774130611)
              ·
                refine ⟨1077294888812911161195917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718196592541940774130611 1077294888812911161195917)
                ·
                  refine ⟨403985583304841685448469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077294888812911161195917 403985583304841685448469)
                  ·
                    refine ⟨18936824217414454005397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 403985583304841685448469 18936824217414454005397)
                    ·
                      rfl

theorem cell23_110638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_110638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110638 prefixEnd_110638 := by exact prefixLift 110638
  have htrace : WordTrace (prefixWord ++ tailWord_110638) baseStart_110638 baseEnd_110638 := by
    simpa [prefixWord, tailWord_110638, baseEnd_110638] using wordTrace_append hprefix tailTrace_110638
  have hstable : (prefixWord ++ tailWord_110638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110638).length < 2 ^ (prefixWord ++ tailWord_110638).sum := by decide
  have hdescent : baseEnd_110638 < baseStart_110638 := by decide
  rcases family_descends (prefixWord ++ tailWord_110638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110681 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_110681 : Nat := 118140960795 + 110681 * 2 ^ 59
def prefixEnd_110681 : Nat := 4983230072969 + 3 ^ 40 * 110681 * 2
def baseEnd_110681 : Nat := 18944184106795564592831

theorem tailTrace_110681 : CollatzResearch.WordTrace tailWord_110681 prefixEnd_110681 18944184106795564592831 := by
  unfold tailWord_110681
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036867712029114654979897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2691245141352743103319931 4036867712029114654979897)
  ·
    refine ⟨3027650784021835991234923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4036867712029114654979897 3027650784021835991234923)
    ·
      refine ⟨4541476176032753986852385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027650784021835991234923 4541476176032753986852385)
      ·
        refine ⟨3406107132024565490139289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4541476176032753986852385 3406107132024565490139289)
        ·
          refine ⟨2554580349018424117604467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3406107132024565490139289 2554580349018424117604467)
          ·
            refine ⟨3831870523527636176406701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554580349018424117604467 3831870523527636176406701)
            ·
              refine ⟨1436951446322863566152513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3831870523527636176406701 1436951446322863566152513)
              ·
                refine ⟨1077713584742147674614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436951446322863566152513 1077713584742147674614385)
                ·
                  refine ⟨808285188556610755960789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077713584742147674614385 808285188556610755960789)
                  ·
                    refine ⟨18944184106795564592831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 808285188556610755960789 18944184106795564592831)
                    ·
                      rfl

theorem cell23_110681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_110681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110681 prefixEnd_110681 := by exact prefixLift 110681
  have htrace : WordTrace (prefixWord ++ tailWord_110681) baseStart_110681 baseEnd_110681 := by
    simpa [prefixWord, tailWord_110681, baseEnd_110681] using wordTrace_append hprefix tailTrace_110681
  have hstable : (prefixWord ++ tailWord_110681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110681).length < 2 ^ (prefixWord ++ tailWord_110681).sum := by decide
  have hdescent : baseEnd_110681 < baseStart_110681 := by decide
  rcases family_descends (prefixWord ++ tailWord_110681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110695 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_110695 : Nat := 118140960795 + 110695 * 2 ^ 59
def prefixEnd_110695 : Nat := 4983230072969 + 3 ^ 40 * 110695 * 2
def baseEnd_110695 : Nat := 56839741049549639003429

theorem tailTrace_110695 : CollatzResearch.WordTrace tailWord_110695 prefixEnd_110695 56839741049549639003429 := by
  unfold tailWord_110695
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037378333978395045989539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2691585555985596697326359 4037378333978395045989539)
  ·
    refine ⟨6056067500967592568984309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037378333978395045989539 6056067500967592568984309)
    ·
      refine ⟨567756328215711803342279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6056067500967592568984309 567756328215711803342279)
      ·
        refine ⟨851634492323567705013419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567756328215711803342279 851634492323567705013419)
        ·
          refine ⟨1277451738485351557520129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851634492323567705013419 1277451738485351557520129)
          ·
            refine ⟨958088803864013668140097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1277451738485351557520129 958088803864013668140097)
            ·
              refine ⟨718566602898010251105073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958088803864013668140097 718566602898010251105073)
              ·
                refine ⟨538924952173507688328805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718566602898010251105073 538924952173507688328805)
                ·
                  refine ⟨101048428532532691561651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538924952173507688328805 101048428532532691561651)
                  ·
                    refine ⟨151572642798799037342477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101048428532532691561651 151572642798799037342477)
                    ·
                      refine ⟨56839741049549639003429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 151572642798799037342477 56839741049549639003429)
                      ·
                        rfl

theorem cell23_110695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_110695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110695 prefixEnd_110695 := by exact prefixLift 110695
  have htrace : WordTrace (prefixWord ++ tailWord_110695) baseStart_110695 baseEnd_110695 := by
    simpa [prefixWord, tailWord_110695, baseEnd_110695] using wordTrace_append hprefix tailTrace_110695
  have hstable : (prefixWord ++ tailWord_110695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110695).length < 2 ^ (prefixWord ++ tailWord_110695).sum := by decide
  have hdescent : baseEnd_110695 < baseStart_110695 := by decide
  rcases family_descends (prefixWord ++ tailWord_110695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110752 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2]
def baseStart_110752 : Nat := 118140960795 + 110752 * 2 ^ 59
def prefixEnd_110752 : Nat := 4983230072969 + 3 ^ 40 * 110752 * 2
def baseEnd_110752 : Nat := 56869009446855915990667

theorem tailTrace_110752 : CollatzResearch.WordTrace tailWord_110752 prefixEnd_110752 56869009446855915990667 := by
  unfold tailWord_110752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019728647385946890407255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2692971529847929187209673 2019728647385946890407255)
  ·
    refine ⟨3029592971078920335610883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2019728647385946890407255 3029592971078920335610883)
    ·
      refine ⟨4544389456618380503416325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029592971078920335610883 4544389456618380503416325)
      ·
        refine ⟨852073023115946344390561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4544389456618380503416325 852073023115946344390561)
        ·
          refine ⟨639054767336959758292921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852073023115946344390561 639054767336959758292921)
          ·
            refine ⟨479291075502719818719691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639054767336959758292921 479291075502719818719691)
            ·
              refine ⟨718936613254079728079537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479291075502719818719691 718936613254079728079537)
              ·
                refine ⟨539202459940559796059653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718936613254079728079537 539202459940559796059653)
                ·
                  refine ⟨101100461238854961761185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539202459940559796059653 101100461238854961761185)
                  ·
                    refine ⟨75825345929141221320889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101100461238854961761185 75825345929141221320889)
                    ·
                      refine ⟨56869009446855915990667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75825345929141221320889 56869009446855915990667)
                      ·
                        rfl

theorem cell23_110752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_110752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110752 prefixEnd_110752 := by exact prefixLift 110752
  have htrace : WordTrace (prefixWord ++ tailWord_110752) baseStart_110752 baseEnd_110752 := by
    simpa [prefixWord, tailWord_110752, baseEnd_110752] using wordTrace_append hprefix tailTrace_110752
  have hstable : (prefixWord ++ tailWord_110752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110752).length < 2 ^ (prefixWord ++ tailWord_110752).sum := by decide
  have hdescent : baseEnd_110752 < baseStart_110752 := by decide
  rcases family_descends (prefixWord ++ tailWord_110752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110775 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 7]
def baseStart_110775 : Nat := 118140960795 + 110775 * 2 ^ 59
def prefixEnd_110775 : Nat := 4983230072969 + 3 ^ 40 * 110775 * 2
def baseEnd_110775 : Nat := 6320091055767702889229

theorem tailTrace_110775 : CollatzResearch.WordTrace tailWord_110775 prefixEnd_110775 6320091055767702889229 := by
  unfold tailWord_110775
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040296173688568708901779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2693530782459045805934519 4040296173688568708901779)
  ·
    refine ⟨6060444260532853063352669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040296173688568708901779 6060444260532853063352669)
    ·
      refine ⟨2272666597699819898757251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6060444260532853063352669 2272666597699819898757251)
      ·
        refine ⟨3408999896549729848135877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2272666597699819898757251 3408999896549729848135877)
        ·
          refine ⟨639187480603074346525477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3408999896549729848135877 639187480603074346525477)
          ·
            refine ⟨119847652613076439973527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 639187480603074346525477 119847652613076439973527)
            ·
              refine ⟨179771478919614659960291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119847652613076439973527 179771478919614659960291)
              ·
                refine ⟨269657218379421989940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179771478919614659960291 269657218379421989940437)
                ·
                  refine ⟨6320091055767702889229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 269657218379421989940437 6320091055767702889229)
                  ·
                    rfl

theorem cell23_110775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 7].length) (baseStart_110775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110775 prefixEnd_110775 := by exact prefixLift 110775
  have htrace : WordTrace (prefixWord ++ tailWord_110775) baseStart_110775 baseEnd_110775 := by
    simpa [prefixWord, tailWord_110775, baseEnd_110775] using wordTrace_append hprefix tailTrace_110775
  have hstable : (prefixWord ++ tailWord_110775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110775).length < 2 ^ (prefixWord ++ tailWord_110775).sum := by decide
  have hdescent : baseEnd_110775 < baseStart_110775 := by decide
  rcases family_descends (prefixWord ++ tailWord_110775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110825 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 4, 4, 2]
def baseStart_110825 : Nat := 118140960795 + 110825 * 2 ^ 59
def prefixEnd_110825 : Nat := 4983230072969 + 3 ^ 40 * 110825 * 2
def baseEnd_110825 : Nat := 56906493534634130377831

theorem tailTrace_110825 : CollatzResearch.WordTrace tailWord_110825 prefixEnd_110825 56906493534634130377831 := by
  unfold tailWord_110825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042119823507427248221929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2694746549004951498814619 4042119823507427248221929)
  ·
    refine ⟨3031589867630570436166447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4042119823507427248221929 3031589867630570436166447)
    ·
      refine ⟨4547384801445855654249671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031589867630570436166447 4547384801445855654249671)
      ·
        refine ⟨6821077202168783481374507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547384801445855654249671 6821077202168783481374507)
        ·
          refine ⟨10231615803253175222061761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821077202168783481374507 10231615803253175222061761)
          ·
            refine ⟨7673711852439881416546321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10231615803253175222061761 7673711852439881416546321)
            ·
              refine ⟨5755283889329911062409741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673711852439881416546321 5755283889329911062409741)
              ·
                refine ⟨2158231458498716648403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5755283889329911062409741 2158231458498716648403653)
                ·
                  refine ⟨404668398468509371575685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158231458498716648403653 404668398468509371575685)
                  ·
                    refine ⟨75875324712845507170441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404668398468509371575685 75875324712845507170441)
                    ·
                      refine ⟨56906493534634130377831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75875324712845507170441 56906493534634130377831)
                      ·
                        rfl

theorem cell23_110825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4, 2].length) (baseStart_110825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110825 prefixEnd_110825 := by exact prefixLift 110825
  have htrace : WordTrace (prefixWord ++ tailWord_110825) baseStart_110825 baseEnd_110825 := by
    simpa [prefixWord, tailWord_110825, baseEnd_110825] using wordTrace_append hprefix tailTrace_110825
  have hstable : (prefixWord ++ tailWord_110825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110825).length < 2 ^ (prefixWord ++ tailWord_110825).sum := by decide
  have hdescent : baseEnd_110825 < baseStart_110825 := by decide
  rcases family_descends (prefixWord ++ tailWord_110825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110828 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_110828 : Nat := 118140960795 + 110828 * 2 ^ 59
def prefixEnd_110828 : Nat := 4983230072969 + 3 ^ 40 * 110828 * 2
def baseEnd_110828 : Nat := 56908033976597618640317

theorem tailTrace_110828 : CollatzResearch.WordTrace tailWord_110828 prefixEnd_110828 56908033976597618640317 := by
  unfold tailWord_110828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021114621248279380290569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2694819494997705840387425 2021114621248279380290569)
  ·
    refine ⟨1515835965936209535217927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2021114621248279380290569 1515835965936209535217927)
    ·
      refine ⟨2273753948904314302826891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515835965936209535217927 2273753948904314302826891)
      ·
        refine ⟨3410630923356471454240337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273753948904314302826891 3410630923356471454240337)
        ·
          refine ⟨2557973192517353590680253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3410630923356471454240337 2557973192517353590680253)
          ·
            refine ⟨959239947194007596505095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2557973192517353590680253 959239947194007596505095)
            ·
              refine ⟨1438859920791011394757643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959239947194007596505095 1438859920791011394757643)
              ·
                refine ⟨2158289881186517092136465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438859920791011394757643 2158289881186517092136465)
                ·
                  refine ⟨1618717410889887819102349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158289881186517092136465 1618717410889887819102349)
                  ·
                    refine ⟨607019029083707932163381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1618717410889887819102349 607019029083707932163381)
                    ·
                      refine ⟨56908033976597618640317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 607019029083707932163381 56908033976597618640317)
                      ·
                        rfl

theorem cell23_110828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_110828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110828 prefixEnd_110828 := by exact prefixLift 110828
  have htrace : WordTrace (prefixWord ++ tailWord_110828) baseStart_110828 baseEnd_110828 := by
    simpa [prefixWord, tailWord_110828, baseEnd_110828] using wordTrace_append hprefix tailTrace_110828
  have hstable : (prefixWord ++ tailWord_110828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110828).length < 2 ^ (prefixWord ++ tailWord_110828).sum := by decide
  have hdescent : baseEnd_110828 < baseStart_110828 := by decide
  rcases family_descends (prefixWord ++ tailWord_110828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110835 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 3, 4]
def baseStart_110835 : Nat := 118140960795 + 110835 * 2 ^ 59
def prefixEnd_110835 : Nat := 4983230072969 + 3 ^ 40 * 110835 * 2
def baseEnd_110835 : Nat := 18970542780393030417595

theorem tailTrace_110835 : CollatzResearch.WordTrace tailWord_110835 prefixEnd_110835 18970542780393030417595 := by
  unfold tailWord_110835
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042484553471198956085959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2694989702314132637390639 4042484553471198956085959)
  ·
    refine ⟨6063726830206798434128939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042484553471198956085959 6063726830206798434128939)
    ·
      refine ⟨9095590245310197651193409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063726830206798434128939 9095590245310197651193409)
      ·
        refine ⟨6821692683982648238395057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9095590245310197651193409 6821692683982648238395057)
        ·
          refine ⟨5116269512986986178796293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6821692683982648238395057 5116269512986986178796293)
          ·
            refine ⟨959300533685059908524305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5116269512986986178796293 959300533685059908524305)
            ·
              refine ⟨719475400263794931393229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959300533685059908524305 719475400263794931393229)
              ·
                refine ⟨269803275098923099272461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719475400263794931393229 269803275098923099272461)
                ·
                  refine ⟨101176228162096162227173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269803275098923099272461 101176228162096162227173)
                  ·
                    refine ⟨18970542780393030417595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101176228162096162227173 18970542780393030417595)
                    ·
                      rfl

theorem cell23_110835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 4].length) (baseStart_110835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110835 prefixEnd_110835 := by exact prefixLift 110835
  have htrace : WordTrace (prefixWord ++ tailWord_110835) baseStart_110835 baseEnd_110835 := by
    simpa [prefixWord, tailWord_110835, baseEnd_110835] using wordTrace_append hprefix tailTrace_110835
  have hstable : (prefixWord ++ tailWord_110835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110835).length < 2 ^ (prefixWord ++ tailWord_110835).sum := by decide
  have hdescent : baseEnd_110835 < baseStart_110835 := by decide
  rcases family_descends (prefixWord ++ tailWord_110835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110842 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_110842 : Nat := 118140960795 + 110842 * 2 ^ 59
def prefixEnd_110842 : Nat := 4983230072969 + 3 ^ 40 * 110842 * 2
def baseEnd_110842 : Nat := 56915222705760563865253

theorem tailTrace_110842 : CollatzResearch.WordTrace tailWord_110842 prefixEnd_110842 56915222705760563865253 := by
  unfold tailWord_110842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010684966111459787897695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2695159909630559434393853 1010684966111459787897695)
  ·
    refine ⟨1516027449167189681846543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010684966111459787897695 1516027449167189681846543)
    ·
      refine ⟨2274041173750784522769815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516027449167189681846543 2274041173750784522769815)
      ·
        refine ⟨3411061760626176784154723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274041173750784522769815 3411061760626176784154723)
        ·
          refine ⟨5116592640939265176232085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411061760626176784154723 5116592640939265176232085)
          ·
            refine ⟨239840280044028055135879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5116592640939265176232085 239840280044028055135879)
            ·
              refine ⟨359760420066042082703819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239840280044028055135879 359760420066042082703819)
              ·
                refine ⟨539640630099063124055729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359760420066042082703819 539640630099063124055729)
                ·
                  refine ⟨404730472574297343041797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539640630099063124055729 404730472574297343041797)
                  ·
                    refine ⟨75886963607680751820337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404730472574297343041797 75886963607680751820337)
                    ·
                      refine ⟨56915222705760563865253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75886963607680751820337 56915222705760563865253)
                      ·
                        rfl

theorem cell23_110842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_110842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110842 prefixEnd_110842 := by exact prefixLift 110842
  have htrace : WordTrace (prefixWord ++ tailWord_110842) baseStart_110842 baseEnd_110842 := by
    simpa [prefixWord, tailWord_110842, baseEnd_110842] using wordTrace_append hprefix tailTrace_110842
  have hstable : (prefixWord ++ tailWord_110842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110842).length < 2 ^ (prefixWord ++ tailWord_110842).sum := by decide
  have hdescent : baseEnd_110842 < baseStart_110842 := by decide
  rcases family_descends (prefixWord ++ tailWord_110842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110845 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_110845 : Nat := 118140960795 + 110845 * 2 ^ 59
def prefixEnd_110845 : Nat := 4983230072969 + 3 ^ 40 * 110845 * 2
def baseEnd_110845 : Nat := 56916763147724052127739

theorem tailTrace_110845 : CollatzResearch.WordTrace tailWord_110845 prefixEnd_110845 56916763147724052127739 := by
  unfold tailWord_110845
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042849283434970663949989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2695232855623313775966659 4042849283434970663949989)
  ·
    refine ⟨758034240644056999490623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4042849283434970663949989 758034240644056999490623)
    ·
      refine ⟨1137051360966085499235935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758034240644056999490623 1137051360966085499235935)
      ·
        refine ⟨1705577041449128248853903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137051360966085499235935 1705577041449128248853903)
        ·
          refine ⟨2558365562173692373280855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705577041449128248853903 2558365562173692373280855)
          ·
            refine ⟨3837548343260538559921283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558365562173692373280855 3837548343260538559921283)
            ·
              refine ⟨5756322514890807839881925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837548343260538559921283 5756322514890807839881925)
              ·
                refine ⟨1079310471542026469977861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5756322514890807839881925 1079310471542026469977861)
                ·
                  refine ⟨202370713414129963120849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079310471542026469977861 202370713414129963120849)
                  ·
                    refine ⟨151778035060597472340637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202370713414129963120849 151778035060597472340637)
                    ·
                      refine ⟨56916763147724052127739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 151778035060597472340637 56916763147724052127739)
                      ·
                        rfl

theorem cell23_110845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_110845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110845 prefixEnd_110845 := by exact prefixLift 110845
  have htrace : WordTrace (prefixWord ++ tailWord_110845) baseStart_110845 baseEnd_110845 := by
    simpa [prefixWord, tailWord_110845, baseEnd_110845] using wordTrace_append hprefix tailTrace_110845
  have hstable : (prefixWord ++ tailWord_110845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110845).length < 2 ^ (prefixWord ++ tailWord_110845).sum := by decide
  have hdescent : baseEnd_110845 < baseStart_110845 := by decide
  rcases family_descends (prefixWord ++ tailWord_110845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110882 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_110882 : Nat := 118140960795 + 110882 * 2 ^ 59
def prefixEnd_110882 : Nat := 4983230072969 + 3 ^ 40 * 110882 * 2
def baseEnd_110882 : Nat := 6326195770215600818341

theorem tailTrace_110882 : CollatzResearch.WordTrace tailWord_110882 prefixEnd_110882 6326195770215600818341 := by
  unfold tailWord_110882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011049696075231495761725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2696132522867283988697933 1011049696075231495761725)
  ·
    refine ⟨379143636028211810910647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1011049696075231495761725 379143636028211810910647)
    ·
      refine ⟨568715454042317716365971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379143636028211810910647 568715454042317716365971)
      ·
        refine ⟨853073181063476574548957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568715454042317716365971 853073181063476574548957)
        ·
          refine ⟨319902442898803715455859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853073181063476574548957 319902442898803715455859)
          ·
            refine ⟨479853664348205573183789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319902442898803715455859 479853664348205573183789)
            ·
              refine ⟨179945124130577089943921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479853664348205573183789 179945124130577089943921)
              ·
                refine ⟨134958843097932817457941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179945124130577089943921 134958843097932817457941)
                ·
                  refine ⟨6326195770215600818341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134958843097932817457941 6326195770215600818341)
                  ·
                    rfl

theorem cell23_110882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_110882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110882 prefixEnd_110882 := by exact prefixLift 110882
  have htrace : WordTrace (prefixWord ++ tailWord_110882) baseStart_110882 baseEnd_110882 := by
    simpa [prefixWord, tailWord_110882, baseEnd_110882] using wordTrace_append hprefix tailTrace_110882
  have hstable : (prefixWord ++ tailWord_110882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110882).length < 2 ^ (prefixWord ++ tailWord_110882).sum := by decide
  have hdescent : baseEnd_110882 < baseStart_110882 := by decide
  rcases family_descends (prefixWord ++ tailWord_110882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110892 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_110892 : Nat := 118140960795 + 110892 * 2 ^ 59
def prefixEnd_110892 : Nat := 4983230072969 + 3 ^ 40 * 110892 * 2
def baseEnd_110892 : Nat := 56940896738485368240023

theorem tailTrace_110892 : CollatzResearch.WordTrace tailWord_110892 prefixEnd_110892 56940896738485368240023 := by
  unfold tailWord_110892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022281757132348845455465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2696375676176465127273953 2022281757132348845455465)
  ·
    refine ⟨1516711317849261634091599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2022281757132348845455465 1516711317849261634091599)
    ·
      refine ⟨2275066976773892451137399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516711317849261634091599 2275066976773892451137399)
      ·
        refine ⟨3412600465160838676706099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275066976773892451137399 3412600465160838676706099)
        ·
          refine ⟨5118900697741258015059149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412600465160838676706099 5118900697741258015059149)
          ·
            refine ⟨1919587761652971755647181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5118900697741258015059149 1919587761652971755647181)
            ·
              refine ⟨719845410619864408367693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919587761652971755647181 719845410619864408367693)
              ·
                refine ⟨269942028982449153137885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719845410619864408367693 269942028982449153137885)
                ·
                  refine ⟨101228260868418432426707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269942028982449153137885 101228260868418432426707)
                  ·
                    refine ⟨151842391302627648640061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101228260868418432426707 151842391302627648640061)
                    ·
                      refine ⟨56940896738485368240023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 151842391302627648640061 56940896738485368240023)
                      ·
                        rfl

theorem cell23_110892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_110892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110892 prefixEnd_110892 := by exact prefixLift 110892
  have htrace : WordTrace (prefixWord ++ tailWord_110892) baseStart_110892 baseEnd_110892 := by
    simpa [prefixWord, tailWord_110892, baseEnd_110892] using wordTrace_append hprefix tailTrace_110892
  have hstable : (prefixWord ++ tailWord_110892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110892).length < 2 ^ (prefixWord ++ tailWord_110892).sum := by decide
  have hdescent : baseEnd_110892 < baseStart_110892 := by decide
  rcases family_descends (prefixWord ++ tailWord_110892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110915 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4]
def baseStart_110915 : Nat := 118140960795 + 110915 * 2 ^ 59
def prefixEnd_110915 : Nat := 4983230072969 + 3 ^ 40 * 110915 * 2
def baseEnd_110915 : Nat := 56952706793538778252417

theorem tailTrace_110915 : CollatzResearch.WordTrace tailWord_110915 prefixEnd_110915 56952706793538778252417 := by
  unfold tailWord_110915
  simp only [CollatzResearch.WordTrace]
  refine ⟨4045402393181372618998199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2696934928787581745998799 4045402393181372618998199)
  ·
    refine ⟨6068103589772058928497299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4045402393181372618998199 6068103589772058928497299)
    ·
      refine ⟨9102155384658088392745949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068103589772058928497299 9102155384658088392745949)
      ·
        refine ⟨3413308269246783147279731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9102155384658088392745949 3413308269246783147279731)
        ·
          refine ⟨5119962403870174720919597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413308269246783147279731 5119962403870174720919597)
          ·
            refine ⟨1919985901451315520344849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5119962403870174720919597 1919985901451315520344849)
            ·
              refine ⟨1439989426088486640258637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919985901451315520344849 1439989426088486640258637)
              ·
                refine ⟨539996034783182490096989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439989426088486640258637 539996034783182490096989)
                ·
                  refine ⟨202498513043693433786371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539996034783182490096989 202498513043693433786371)
                  ·
                    refine ⟨303747769565540150679557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202498513043693433786371 303747769565540150679557)
                    ·
                      refine ⟨56952706793538778252417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 303747769565540150679557 56952706793538778252417)
                      ·
                        rfl

theorem cell23_110915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_110915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110915 prefixEnd_110915 := by exact prefixLift 110915
  have htrace : WordTrace (prefixWord ++ tailWord_110915) baseStart_110915 baseEnd_110915 := by
    simpa [prefixWord, tailWord_110915, baseEnd_110915] using wordTrace_append hprefix tailTrace_110915
  have hstable : (prefixWord ++ tailWord_110915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110915).length < 2 ^ (prefixWord ++ tailWord_110915).sum := by decide
  have hdescent : baseEnd_110915 < baseStart_110915 := by decide
  rcases family_descends (prefixWord ++ tailWord_110915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110952 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_110952 : Nat := 118140960795 + 110952 * 2 ^ 59
def prefixEnd_110952 : Nat := 4983230072969 + 3 ^ 40 * 110952 * 2
def baseEnd_110952 : Nat := 56971705577755133489747

theorem tailTrace_110952 : CollatzResearch.WordTrace tailWord_110952 prefixEnd_110952 56971705577755133489747 := by
  unfold tailWord_110952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023375947023663969047555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2697834596031551958730073 2023375947023663969047555)
  ·
    refine ⟨3035063920535495953571333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023375947023663969047555 3035063920535495953571333)
    ·
      refine ⟨569074485100405491294625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3035063920535495953571333 569074485100405491294625)
      ·
        refine ⟨426805863825304118470969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569074485100405491294625 426805863825304118470969)
        ·
          refine ⟨320104397868978088853227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426805863825304118470969 320104397868978088853227)
          ·
            refine ⟨480156596803467133279841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320104397868978088853227 480156596803467133279841)
            ·
              refine ⟨360117447602600349959881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480156596803467133279841 360117447602600349959881)
              ·
                refine ⟨270088085701950262469911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360117447602600349959881 270088085701950262469911)
                ·
                  refine ⟨405132128552925393704867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270088085701950262469911 405132128552925393704867)
                  ·
                    refine ⟨607698192829388090557301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405132128552925393704867 607698192829388090557301)
                    ·
                      refine ⟨56971705577755133489747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 607698192829388090557301 56971705577755133489747)
                      ·
                        rfl

theorem cell23_110952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_110952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110952 prefixEnd_110952 := by exact prefixLift 110952
  have htrace : WordTrace (prefixWord ++ tailWord_110952) baseStart_110952 baseEnd_110952 := by
    simpa [prefixWord, tailWord_110952, baseEnd_110952] using wordTrace_append hprefix tailTrace_110952
  have hstable : (prefixWord ++ tailWord_110952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110952).length < 2 ^ (prefixWord ++ tailWord_110952).sum := by decide
  have hdescent : baseEnd_110952 < baseStart_110952 := by decide
  rcases family_descends (prefixWord ++ tailWord_110952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110966 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_110966 : Nat := 118140960795 + 110966 * 2 ^ 59
def prefixEnd_110966 : Nat := 4983230072969 + 3 ^ 40 * 110966 * 2
def baseEnd_110966 : Nat := 56978894306918078714683

theorem tailTrace_110966 : CollatzResearch.WordTrace tailWord_110966 prefixEnd_110966 56978894306918078714683 := by
  unfold tailWord_110966
  simp only [CollatzResearch.WordTrace]
  refine ⟨252953907249788020569047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2698175010664405552736501 252953907249788020569047)
  ·
    refine ⟨379430860874682030853571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252953907249788020569047 379430860874682030853571)
    ·
      refine ⟨569146291312023046280357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379430860874682030853571 569146291312023046280357)
      ·
        refine ⟨106714929621004321177567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 569146291312023046280357 106714929621004321177567)
        ·
          refine ⟨160072394431506481766351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106714929621004321177567 160072394431506481766351)
          ·
            refine ⟨240108591647259722649527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160072394431506481766351 240108591647259722649527)
            ·
              refine ⟨360162887470889583974291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240108591647259722649527 360162887470889583974291)
              ·
                refine ⟨540244331206334375961437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360162887470889583974291 540244331206334375961437)
                ·
                  refine ⟨202591624202375390985539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540244331206334375961437 202591624202375390985539)
                  ·
                    refine ⟨303887436303563086478309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202591624202375390985539 303887436303563086478309)
                    ·
                      refine ⟨56978894306918078714683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 303887436303563086478309 56978894306918078714683)
                      ·
                        rfl

theorem cell23_110966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_110966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110966 prefixEnd_110966 := by exact prefixLift 110966
  have htrace : WordTrace (prefixWord ++ tailWord_110966) baseStart_110966 baseEnd_110966 := by
    simpa [prefixWord, tailWord_110966, baseEnd_110966] using wordTrace_append hprefix tailTrace_110966
  have hstable : (prefixWord ++ tailWord_110966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110966).length < 2 ^ (prefixWord ++ tailWord_110966).sum := by decide
  have hdescent : baseEnd_110966 < baseStart_110966 := by decide
  rcases family_descends (prefixWord ++ tailWord_110966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110986 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_110986 : Nat := 118140960795 + 110986 * 2 ^ 59
def prefixEnd_110986 : Nat := 4983230072969 + 3 ^ 40 * 110986 * 2
def baseEnd_110986 : Nat := 56989163920008000464591

theorem tailTrace_110986 : CollatzResearch.WordTrace tailWord_110986 prefixEnd_110986 56989163920008000464591 := by
  unfold tailWord_110986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011997993981037936208203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2698661317282767829888541 1011997993981037936208203)
  ·
    refine ⟨1517996990971556904312305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1011997993981037936208203 1517996990971556904312305)
    ·
      refine ⟨1138497743228667678234229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517996990971556904312305 1138497743228667678234229)
      ·
        refine ⟨106734163427687594834459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1138497743228667678234229 106734163427687594834459)
        ·
          refine ⟨160101245141531392251689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106734163427687594834459 160101245141531392251689)
          ·
            refine ⟨120075933856148544188767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160101245141531392251689 120075933856148544188767)
            ·
              refine ⟨180113900784222816283151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120075933856148544188767 180113900784222816283151)
              ·
                refine ⟨270170851176334224424727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180113900784222816283151 270170851176334224424727)
                ·
                  refine ⟨405256276764501336637091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270170851176334224424727 405256276764501336637091)
                  ·
                    refine ⟨607884415146752004955637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405256276764501336637091 607884415146752004955637)
                    ·
                      refine ⟨56989163920008000464591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 607884415146752004955637 56989163920008000464591)
                      ·
                        rfl

theorem cell23_110986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_110986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110986 prefixEnd_110986 := by exact prefixLift 110986
  have htrace : WordTrace (prefixWord ++ tailWord_110986) baseStart_110986 baseEnd_110986 := by
    simpa [prefixWord, tailWord_110986, baseEnd_110986] using wordTrace_append hprefix tailTrace_110986
  have hstable : (prefixWord ++ tailWord_110986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110986).length < 2 ^ (prefixWord ++ tailWord_110986).sum := by decide
  have hdescent : baseEnd_110986 < baseStart_110986 := by decide
  rcases family_descends (prefixWord ++ tailWord_110986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110999 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_110999 : Nat := 118140960795 + 110999 * 2 ^ 59
def prefixEnd_110999 : Nat := 4983230072969 + 3 ^ 40 * 110999 * 2
def baseEnd_110999 : Nat := 56995839168516449602031

theorem tailTrace_110999 : CollatzResearch.WordTrace tailWord_110999 prefixEnd_110999 56995839168516449602031 := by
  unfold tailWord_110999
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048466124877054965056051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2698977416584703310037367 4048466124877054965056051)
  ·
    refine ⟨6072699187315582447584077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4048466124877054965056051 6072699187315582447584077)
    ·
      refine ⟨2277262195243343417844029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6072699187315582447584077 2277262195243343417844029)
      ·
        refine ⟨853973323216253781691511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2277262195243343417844029 853973323216253781691511)
        ·
          refine ⟨1280959984824380672537267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853973323216253781691511 1280959984824380672537267)
          ·
            refine ⟨1921439977236571008805901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280959984824380672537267 1921439977236571008805901)
            ·
              refine ⟨720539991463714128302213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1921439977236571008805901 720539991463714128302213)
              ·
                refine ⟨135101248399446399056665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720539991463714128302213 135101248399446399056665)
                ·
                  refine ⟨101325936299584799292499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135101248399446399056665 101325936299584799292499)
                  ·
                    refine ⟨151988904449377198938749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101325936299584799292499 151988904449377198938749)
                    ·
                      refine ⟨56995839168516449602031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 151988904449377198938749 56995839168516449602031)
                      ·
                        rfl

theorem cell23_110999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_110999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_110999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_110999 prefixEnd_110999 := by exact prefixLift 110999
  have htrace : WordTrace (prefixWord ++ tailWord_110999) baseStart_110999 baseEnd_110999 := by
    simpa [prefixWord, tailWord_110999, baseEnd_110999] using wordTrace_append hprefix tailTrace_110999
  have hstable : (prefixWord ++ tailWord_110999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110999).length < 2 ^ (prefixWord ++ tailWord_110999).sum := by decide
  have hdescent : baseEnd_110999 < baseStart_110999 := by decide
  rcases family_descends (prefixWord ++ tailWord_110999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111000 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 1, 2, 2]
def baseStart_111000 : Nat := 118140960795 + 111000 * 2 ^ 59
def prefixEnd_111000 : Nat := 4983230072969 + 3 ^ 40 * 111000 * 2
def baseEnd_111000 : Nat := 56996352649170945689527

theorem tailTrace_111000 : CollatzResearch.WordTrace tailWord_111000 prefixEnd_111000 56996352649170945689527 := by
  unfold tailWord_111000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024251298936716067921227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2699001731915621423894969 2024251298936716067921227)
  ·
    refine ⟨3036376948405074101881841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024251298936716067921227 3036376948405074101881841)
    ·
      refine ⟨2277282711303805576411381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3036376948405074101881841 2277282711303805576411381)
      ·
        refine ⟨213495254184731772788567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2277282711303805576411381 213495254184731772788567)
        ·
          refine ⟨320242881277097659182851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213495254184731772788567 320242881277097659182851)
          ·
            refine ⟨480364321915646488774277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320242881277097659182851 480364321915646488774277)
            ·
              refine ⟨90068310359183716645177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480364321915646488774277 90068310359183716645177)
              ·
                refine ⟨67551232769387787483883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90068310359183716645177 67551232769387787483883)
                ·
                  refine ⟨101326849154081681225825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67551232769387787483883 101326849154081681225825)
                  ·
                    refine ⟨75995136865561260919369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101326849154081681225825 75995136865561260919369)
                    ·
                      refine ⟨56996352649170945689527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 75995136865561260919369 56996352649170945689527)
                      ·
                        rfl

theorem cell23_111000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_111000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111000 prefixEnd_111000 := by exact prefixLift 111000
  have htrace : WordTrace (prefixWord ++ tailWord_111000) baseStart_111000 baseEnd_111000 := by
    simpa [prefixWord, tailWord_111000, baseEnd_111000] using wordTrace_append hprefix tailTrace_111000
  have hstable : (prefixWord ++ tailWord_111000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111000).length < 2 ^ (prefixWord ++ tailWord_111000).sum := by decide
  have hdescent : baseEnd_111000 < baseStart_111000 := by decide
  rcases family_descends (prefixWord ++ tailWord_111000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111016 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_111016 : Nat := 118140960795 + 111016 * 2 ^ 59
def prefixEnd_111016 : Nat := 4983230072969 + 3 ^ 40 * 111016 * 2
def baseEnd_111016 : Nat := 57004568339642883089453

theorem tailTrace_111016 : CollatzResearch.WordTrace tailWord_111016 prefixEnd_111016 57004568339642883089453 := by
  unfold tailWord_111016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024543082907733434212451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2699390777210311245616601 2024543082907733434212451)
  ·
    refine ⟨3036814624361600151318677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024543082907733434212451 3036814624361600151318677)
    ·
      refine ⟨142350685516950007093063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3036814624361600151318677 142350685516950007093063)
      ·
        refine ⟨213526028275425010639595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142350685516950007093063 213526028275425010639595)
        ·
          refine ⟨320289042413137515959393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213526028275425010639595 320289042413137515959393)
          ·
            refine ⟨240216781809853136969545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320289042413137515959393 240216781809853136969545)
            ·
              refine ⟨180162586357389852727159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240216781809853136969545 180162586357389852727159)
              ·
                refine ⟨270243879536084779090739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180162586357389852727159 270243879536084779090739)
                ·
                  refine ⟨405365819304127168636109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270243879536084779090739 405365819304127168636109)
                  ·
                    refine ⟨152012182239047688238541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405365819304127168636109 152012182239047688238541)
                    ·
                      refine ⟨57004568339642883089453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152012182239047688238541 57004568339642883089453)
                      ·
                        rfl

theorem cell23_111016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_111016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111016 prefixEnd_111016 := by exact prefixLift 111016
  have htrace : WordTrace (prefixWord ++ tailWord_111016) baseStart_111016 baseEnd_111016 := by
    simpa [prefixWord, tailWord_111016, baseEnd_111016] using wordTrace_append hprefix tailTrace_111016
  have hstable : (prefixWord ++ tailWord_111016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111016).length < 2 ^ (prefixWord ++ tailWord_111016).sum := by decide
  have hdescent : baseEnd_111016 < baseStart_111016 := by decide
  rcases family_descends (prefixWord ++ tailWord_111016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111072 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_111072 : Nat := 118140960795 + 111072 * 2 ^ 59
def prefixEnd_111072 : Nat := 4983230072969 + 3 ^ 40 * 111072 * 2
def baseEnd_111072 : Nat := 57033323256294663989195

theorem tailTrace_111072 : CollatzResearch.WordTrace tailWord_111072 prefixEnd_111072 57033323256294663989195 := by
  unfold tailWord_111072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025564326806294216231735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2700752435741725621642313 2025564326806294216231735)
  ·
    refine ⟨3038346490209441324347603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025564326806294216231735 3038346490209441324347603)
    ·
      refine ⟨4557519735314161986521405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038346490209441324347603 4557519735314161986521405)
      ·
        refine ⟨1709069900742810744945527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4557519735314161986521405 1709069900742810744945527)
        ·
          refine ⟨2563604851114216117418291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709069900742810744945527 2563604851114216117418291)
          ·
            refine ⟨3845407276671324176127437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563604851114216117418291 3845407276671324176127437)
            ·
              refine ⟨1442027728751746566047789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3845407276671324176127437 1442027728751746566047789)
              ·
                refine ⟨540760398281904962267921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442027728751746566047789 540760398281904962267921)
                ·
                  refine ⟨405570298711428721700941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540760398281904962267921 405570298711428721700941)
                  ·
                    refine ⟨152088862016785770637853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405570298711428721700941 152088862016785770637853)
                    ·
                      refine ⟨57033323256294663989195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152088862016785770637853 57033323256294663989195)
                      ·
                        rfl

theorem cell23_111072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_111072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111072 prefixEnd_111072 := by exact prefixLift 111072
  have htrace : WordTrace (prefixWord ++ tailWord_111072) baseStart_111072 baseEnd_111072 := by
    simpa [prefixWord, tailWord_111072, baseEnd_111072] using wordTrace_append hprefix tailTrace_111072
  have hstable : (prefixWord ++ tailWord_111072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111072).length < 2 ^ (prefixWord ++ tailWord_111072).sum := by decide
  have hdescent : baseEnd_111072 < baseStart_111072 := by decide
  rcases family_descends (prefixWord ++ tailWord_111072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111073 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_111073 : Nat := 118140960795 + 111073 * 2 ^ 59
def prefixEnd_111073 : Nat := 4983230072969 + 3 ^ 40 * 111073 * 2
def baseEnd_111073 : Nat := 57033836736949160076691

theorem tailTrace_111073 : CollatzResearch.WordTrace tailWord_111073 prefixEnd_111073 57033836736949160076691 := by
  unfold tailWord_111073
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051165126608965603249873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2700776751072643735499915 4051165126608965603249873)
  ·
    refine ⟨3038373844956724202437405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4051165126608965603249873 3038373844956724202437405)
    ·
      refine ⟨1139390191858771575914027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3038373844956724202437405 1139390191858771575914027)
      ·
        refine ⟨1709085287788157363871041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139390191858771575914027 1709085287788157363871041)
        ·
          refine ⟨1281813965841118022903281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709085287788157363871041 1281813965841118022903281)
          ·
            refine ⟨961360474380838517177461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281813965841118022903281 961360474380838517177461)
            ·
              refine ⟨90127544473203610985387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 961360474380838517177461 90127544473203610985387)
              ·
                refine ⟨135191316709805416478081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90127544473203610985387 135191316709805416478081)
                ·
                  refine ⟨101393487532354062358561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135191316709805416478081 101393487532354062358561)
                  ·
                    refine ⟨76045115649265546768921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101393487532354062358561 76045115649265546768921)
                    ·
                      refine ⟨57033836736949160076691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76045115649265546768921 57033836736949160076691)
                      ·
                        rfl

theorem cell23_111073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_111073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111073 prefixEnd_111073 := by exact prefixLift 111073
  have htrace : WordTrace (prefixWord ++ tailWord_111073) baseStart_111073 baseEnd_111073 := by
    simpa [prefixWord, tailWord_111073, baseEnd_111073] using wordTrace_append hprefix tailTrace_111073
  have hstable : (prefixWord ++ tailWord_111073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111073).length < 2 ^ (prefixWord ++ tailWord_111073).sum := by decide
  have hdescent : baseEnd_111073 < baseStart_111073 := by decide
  rcases family_descends (prefixWord ++ tailWord_111073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111095 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_111095 : Nat := 118140960795 + 111095 * 2 ^ 59
def prefixEnd_111095 : Nat := 4983230072969 + 3 ^ 40 * 111095 * 2
def baseEnd_111095 : Nat := 57045133311348074001589

theorem tailTrace_111095 : CollatzResearch.WordTrace tailWord_111095 prefixEnd_111095 57045133311348074001589 := by
  unfold tailWord_111095
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051967532529263360550739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701311688352842240367159 4051967532529263360550739)
  ·
    refine ⟨6077951298793895040826109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4051967532529263360550739 6077951298793895040826109)
    ·
      refine ⟨2279231737047710640309791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6077951298793895040826109 2279231737047710640309791)
      ·
        refine ⟨3418847605571565960464687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279231737047710640309791 3418847605571565960464687)
        ·
          refine ⟨5128271408357348940697031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418847605571565960464687 5128271408357348940697031)
          ·
            refine ⟨7692407112536023411045547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128271408357348940697031 7692407112536023411045547)
            ·
              refine ⟨11538610668804035116568321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692407112536023411045547 11538610668804035116568321)
              ·
                refine ⟨8653958001603026337426241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11538610668804035116568321 8653958001603026337426241)
                ·
                  refine ⟨6490468501202269753069681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8653958001603026337426241 6490468501202269753069681)
                  ·
                    refine ⟨4867851375901702314802261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490468501202269753069681 4867851375901702314802261)
                    ·
                      refine ⟨57045133311348074001589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4867851375901702314802261 57045133311348074001589)
                      ·
                        rfl

theorem cell23_111095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_111095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111095 prefixEnd_111095 := by exact prefixLift 111095
  have htrace : WordTrace (prefixWord ++ tailWord_111095) baseStart_111095 baseEnd_111095 := by
    simpa [prefixWord, tailWord_111095, baseEnd_111095] using wordTrace_append hprefix tailTrace_111095
  have hstable : (prefixWord ++ tailWord_111095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111095).length < 2 ^ (prefixWord ++ tailWord_111095).sum := by decide
  have hdescent : baseEnd_111095 < baseStart_111095 := by decide
  rcases family_descends (prefixWord ++ tailWord_111095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111143 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 2, 5]
def baseStart_111143 : Nat := 118140960795 + 111143 * 2 ^ 59
def prefixEnd_111143 : Nat := 4983230072969 + 3 ^ 40 * 111143 * 2
def baseEnd_111143 : Nat := 19023260127587962067123

theorem tailTrace_111143 : CollatzResearch.WordTrace tailWord_111143 prefixEnd_111143 19023260127587962067123 := by
  unfold tailWord_111143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053718236355367558298083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2702478824236911705532055 4053718236355367558298083)
  ·
    refine ⟨6080577354533051337447125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053718236355367558298083 6080577354533051337447125)
    ·
      refine ⟨142513531746868390721417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6080577354533051337447125 142513531746868390721417)
      ·
        refine ⟨106885148810151293041063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142513531746868390721417 106885148810151293041063)
        ·
          refine ⟨160327723215226939561595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106885148810151293041063 160327723215226939561595)
          ·
            refine ⟨240491584822840409342393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160327723215226939561595 240491584822840409342393)
            ·
              refine ⟨180368688617130307006795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240491584822840409342393 180368688617130307006795)
              ·
                refine ⟨270553032925695460510193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180368688617130307006795 270553032925695460510193)
                ·
                  refine ⟨202914774694271595382645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270553032925695460510193 202914774694271595382645)
                  ·
                    refine ⟨19023260127587962067123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202914774694271595382645 19023260127587962067123)
                    ·
                      rfl

theorem cell23_111143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_111143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111143 prefixEnd_111143 := by exact prefixLift 111143
  have htrace : WordTrace (prefixWord ++ tailWord_111143) baseStart_111143 baseEnd_111143 := by
    simpa [prefixWord, tailWord_111143, baseEnd_111143] using wordTrace_append hprefix tailTrace_111143
  have hstable : (prefixWord ++ tailWord_111143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111143).length < 2 ^ (prefixWord ++ tailWord_111143).sum := by decide
  have hdescent : baseEnd_111143 < baseStart_111143 := by decide
  rcases family_descends (prefixWord ++ tailWord_111143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111146 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_111146 : Nat := 118140960795 + 111146 * 2 ^ 59
def prefixEnd_111146 : Nat := 4983230072969 + 3 ^ 40 * 111146 * 2
def baseEnd_111146 : Nat := 57071320824727374463855

theorem tailTrace_111146 : CollatzResearch.WordTrace tailWord_111146 prefixEnd_111146 57071320824727374463855 := by
  unfold tailWord_111146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013456913836124767664323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2702551770229666047104861 1013456913836124767664323)
  ·
    refine ⟨1520185370754187151496485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013456913836124767664323 1520185370754187151496485)
    ·
      refine ⟨285034757016410090905591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1520185370754187151496485 285034757016410090905591)
      ·
        refine ⟨427552135524615136358387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285034757016410090905591 427552135524615136358387)
        ·
          refine ⟨641328203286922704537581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427552135524615136358387 641328203286922704537581)
          ·
            refine ⟨240498076232596014201593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641328203286922704537581 240498076232596014201593)
            ·
              refine ⟨180373557174447010651195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240498076232596014201593 180373557174447010651195)
              ·
                refine ⟨270560335761670515976793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180373557174447010651195 270560335761670515976793)
                ·
                  refine ⟨202920251821252886982595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270560335761670515976793 202920251821252886982595)
                  ·
                    refine ⟨304380377731879330473893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202920251821252886982595 304380377731879330473893)
                    ·
                      refine ⟨57071320824727374463855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 304380377731879330473893 57071320824727374463855)
                      ·
                        rfl

theorem cell23_111146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_111146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111146 prefixEnd_111146 := by exact prefixLift 111146
  have htrace : WordTrace (prefixWord ++ tailWord_111146) baseStart_111146 baseEnd_111146 := by
    simpa [prefixWord, tailWord_111146, baseEnd_111146] using wordTrace_append hprefix tailTrace_111146
  have hstable : (prefixWord ++ tailWord_111146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111146).length < 2 ^ (prefixWord ++ tailWord_111146).sum := by decide
  have hdescent : baseEnd_111146 < baseStart_111146 := by decide
  rcases family_descends (prefixWord ++ tailWord_111146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111169 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 6]
def baseStart_111169 : Nat := 118140960795 + 111169 * 2 ^ 59
def prefixEnd_111169 : Nat := 4983230072969 + 3 ^ 40 * 111169 * 2
def baseEnd_111169 : Nat := 6342570097753420497361

theorem tailTrace_111169 : CollatzResearch.WordTrace tailWord_111169 prefixEnd_111169 6342570097753420497361 := by
  unfold tailWord_111169
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054666534261173998744561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2703111022840782665829707 4054666534261173998744561)
  ·
    refine ⟨3040999900695880499058421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4054666534261173998744561 3040999900695880499058421)
    ·
      refine ⟨285093740690238796786727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3040999900695880499058421 285093740690238796786727)
      ·
        refine ⟨427640611035358195180091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285093740690238796786727 427640611035358195180091)
        ·
          refine ⟨641460916553037292770137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427640611035358195180091 641460916553037292770137)
          ·
            refine ⟨481095687414777969577603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641460916553037292770137 481095687414777969577603)
            ·
              refine ⟨721643531122166954366405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481095687414777969577603 721643531122166954366405)
              ·
                refine ⟨135308162085406303943701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721643531122166954366405 135308162085406303943701)
                ·
                  refine ⟨6342570097753420497361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135308162085406303943701 6342570097753420497361)
                  ·
                    rfl

theorem cell23_111169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_111169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111169 prefixEnd_111169 := by exact prefixLift 111169
  have htrace : WordTrace (prefixWord ++ tailWord_111169) baseStart_111169 baseEnd_111169 := by
    simpa [prefixWord, tailWord_111169, baseEnd_111169] using wordTrace_append hprefix tailTrace_111169
  have hstable : (prefixWord ++ tailWord_111169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111169).length < 2 ^ (prefixWord ++ tailWord_111169).sum := by decide
  have hdescent : baseEnd_111169 < baseStart_111169 := by decide
  rcases family_descends (prefixWord ++ tailWord_111169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111173 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_111173 : Nat := 118140960795 + 111173 * 2 ^ 59
def prefixEnd_111173 : Nat := 4983230072969 + 3 ^ 40 * 111173 * 2
def baseEnd_111173 : Nat := 19028394934132922942077

theorem tailTrace_111173 : CollatzResearch.WordTrace tailWord_111173 prefixEnd_111173 19028394934132922942077 := by
  unfold tailWord_111173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054812426246682681890173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2703208284164455121260115 4054812426246682681890173)
  ·
    refine ⟨1520554659842506005708815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4054812426246682681890173 1520554659842506005708815)
    ·
      refine ⟨2280831989763759008563223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520554659842506005708815 2280831989763759008563223)
      ·
        refine ⟨3421247984645638512844835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280831989763759008563223 3421247984645638512844835)
        ·
          refine ⟨5131871976968457769267253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421247984645638512844835 5131871976968457769267253)
          ·
            refine ⟨481112997840792915868805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5131871976968457769267253 481112997840792915868805)
            ·
              refine ⟨90208687095148671725401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 481112997840792915868805 90208687095148671725401)
              ·
                refine ⟨67656515321361503794051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90208687095148671725401 67656515321361503794051)
                ·
                  refine ⟨101484772982042255691077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67656515321361503794051 101484772982042255691077)
                  ·
                    refine ⟨19028394934132922942077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101484772982042255691077 19028394934132922942077)
                    ·
                      rfl

theorem cell23_111173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_111173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111173 prefixEnd_111173 := by exact prefixLift 111173
  have htrace : WordTrace (prefixWord ++ tailWord_111173) baseStart_111173 baseEnd_111173 := by
    simpa [prefixWord, tailWord_111173, baseEnd_111173] using wordTrace_append hprefix tailTrace_111173
  have hstable : (prefixWord ++ tailWord_111173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111173).length < 2 ^ (prefixWord ++ tailWord_111173).sum := by decide
  have hdescent : baseEnd_111173 < baseStart_111173 := by decide
  rcases family_descends (prefixWord ++ tailWord_111173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111216 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_111216 : Nat := 118140960795 + 111216 * 2 ^ 59
def prefixEnd_111216 : Nat := 4983230072969 + 3 ^ 40 * 111216 * 2
def baseEnd_111216 : Nat := 19035754823514033529511

theorem tailTrace_111216 : CollatzResearch.WordTrace tailWord_111216 prefixEnd_111216 19035754823514033529511 := by
  unfold tailWord_111216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028190382545450512852751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2704253843393934017137001 2028190382545450512852751)
  ·
    refine ⟨3042285573818175769279127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028190382545450512852751 3042285573818175769279127)
    ·
      refine ⟨4563428360727263653918691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042285573818175769279127 4563428360727263653918691)
      ·
        refine ⟨6845142541090895480878037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563428360727263653918691 6845142541090895480878037)
        ·
          refine ⟨160433028306817862833079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6845142541090895480878037 160433028306817862833079)
          ·
            refine ⟨240649542460226794249619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160433028306817862833079 240649542460226794249619)
            ·
              refine ⟨360974313690340191374429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240649542460226794249619 360974313690340191374429)
              ·
                refine ⟨135365367633877571765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360974313690340191374429 135365367633877571765411)
                ·
                  refine ⟨203048051450816357648117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135365367633877571765411 203048051450816357648117)
                  ·
                    refine ⟨19035754823514033529511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203048051450816357648117 19035754823514033529511)
                    ·
                      rfl

theorem cell23_111216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_111216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111216 prefixEnd_111216 := by exact prefixLift 111216
  have htrace : WordTrace (prefixWord ++ tailWord_111216) baseStart_111216 baseEnd_111216 := by
    simpa [prefixWord, tailWord_111216, baseEnd_111216] using wordTrace_append hprefix tailTrace_111216
  have hstable : (prefixWord ++ tailWord_111216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111216).length < 2 ^ (prefixWord ++ tailWord_111216).sum := by decide
  have hdescent : baseEnd_111216 < baseStart_111216 := by decide
  rcases family_descends (prefixWord ++ tailWord_111216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111239 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_111239 : Nat := 118140960795 + 111239 * 2 ^ 59
def prefixEnd_111239 : Nat := 4983230072969 + 3 ^ 40 * 111239 * 2
def baseEnd_111239 : Nat := 57119074525595510600927

theorem tailTrace_111239 : CollatzResearch.WordTrace tailWord_111239 prefixEnd_111239 57119074525595510600927 := by
  unfold tailWord_111239
  simp only [CollatzResearch.WordTrace]
  refine ⟨4057219644007575953792771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2704813096005050635861847 4057219644007575953792771)
  ·
    refine ⟨6085829466011363930689157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4057219644007575953792771 6085829466011363930689157)
    ·
      refine ⟨1141093024877130737004217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6085829466011363930689157 1141093024877130737004217)
      ·
        refine ⟨855819768657848052753163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141093024877130737004217 855819768657848052753163)
        ·
          refine ⟨1283729652986772079129745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855819768657848052753163 1283729652986772079129745)
          ·
            refine ⟨962797239740079059347309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283729652986772079129745 962797239740079059347309)
            ·
              refine ⟨361048964902529647255241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962797239740079059347309 361048964902529647255241)
              ·
                refine ⟨270786723676897235441431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361048964902529647255241 270786723676897235441431)
                ·
                  refine ⟨406180085515345853162147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270786723676897235441431 406180085515345853162147)
                  ·
                    refine ⟨609270128273018779743221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406180085515345853162147 609270128273018779743221)
                    ·
                      refine ⟨57119074525595510600927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 609270128273018779743221 57119074525595510600927)
                      ·
                        rfl

theorem cell23_111239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_111239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111239 prefixEnd_111239 := by exact prefixLift 111239
  have htrace : WordTrace (prefixWord ++ tailWord_111239) baseStart_111239 baseEnd_111239 := by
    simpa [prefixWord, tailWord_111239, baseEnd_111239] using wordTrace_append hprefix tailTrace_111239
  have hstable : (prefixWord ++ tailWord_111239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111239).length < 2 ^ (prefixWord ++ tailWord_111239).sum := by decide
  have hdescent : baseEnd_111239 < baseStart_111239 := by decide
  rcases family_descends (prefixWord ++ tailWord_111239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111269 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_111269 : Nat := 118140960795 + 111269 * 2 ^ 59
def prefixEnd_111269 : Nat := 4983230072969 + 3 ^ 40 * 111269 * 2
def baseEnd_111269 : Nat := 57134478945230393225789

theorem tailTrace_111269 : CollatzResearch.WordTrace tailWord_111269 prefixEnd_111269 57134478945230393225789 := by
  unfold tailWord_111269
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058313833898891077384861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2705542555932594051589907 4058313833898891077384861)
  ·
    refine ⟨1521867687712084154019323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4058313833898891077384861 1521867687712084154019323)
    ·
      refine ⟨2282801531568126231028985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521867687712084154019323 2282801531568126231028985)
      ·
        refine ⟨1712101148676094673271739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2282801531568126231028985 1712101148676094673271739)
        ·
          refine ⟨2568151723014142009907609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712101148676094673271739 2568151723014142009907609)
          ·
            refine ⟨1926113792260606507430707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2568151723014142009907609 1926113792260606507430707)
            ·
              refine ⟨2889170688390909761146061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926113792260606507430707 2889170688390909761146061)
              ·
                refine ⟨1083439008146591160429773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2889170688390909761146061 1083439008146591160429773)
                ·
                  refine ⟨406289628054971685161165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083439008146591160429773 406289628054971685161165)
                  ·
                    refine ⟨152358610520614381935437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406289628054971685161165 152358610520614381935437)
                    ·
                      refine ⟨57134478945230393225789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152358610520614381935437 57134478945230393225789)
                      ·
                        rfl

theorem cell23_111269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_111269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111269 prefixEnd_111269 := by exact prefixLift 111269
  have htrace : WordTrace (prefixWord ++ tailWord_111269) baseStart_111269 baseEnd_111269 := by
    simpa [prefixWord, tailWord_111269, baseEnd_111269] using wordTrace_append hprefix tailTrace_111269
  have hstable : (prefixWord ++ tailWord_111269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111269).length < 2 ^ (prefixWord ++ tailWord_111269).sum := by decide
  have hdescent : baseEnd_111269 < baseStart_111269 := by decide
  rcases family_descends (prefixWord ++ tailWord_111269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111287 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_111287 : Nat := 118140960795 + 111287 * 2 ^ 59
def prefixEnd_111287 : Nat := 4983230072969 + 3 ^ 40 * 111287 * 2
def baseEnd_111287 : Nat := 57143721597011322800707

theorem tailTrace_111287 : CollatzResearch.WordTrace tailWord_111287 prefixEnd_111287 57143721597011322800707 := by
  unfold tailWord_111287
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058970347833680151540115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2705980231889120101026743 4058970347833680151540115)
  ·
    refine ⟨6088455521750520227310173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058970347833680151540115 6088455521750520227310173)
    ·
      refine ⟨2283170820656445085241315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6088455521750520227310173 2283170820656445085241315)
      ·
        refine ⟨3424756230984667627861973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283170820656445085241315 3424756230984667627861973)
        ·
          refine ⟨80267724163703147528015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3424756230984667627861973 80267724163703147528015)
          ·
            refine ⟨120401586245554721292023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80267724163703147528015 120401586245554721292023)
            ·
              refine ⟨180602379368332081938035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120401586245554721292023 180602379368332081938035)
              ·
                refine ⟨270903569052498122907053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180602379368332081938035 270903569052498122907053)
                ·
                  refine ⟨101588838394686796090145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270903569052498122907053 101588838394686796090145)
                  ·
                    refine ⟨76191628796015097067609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101588838394686796090145 76191628796015097067609)
                    ·
                      refine ⟨57143721597011322800707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76191628796015097067609 57143721597011322800707)
                      ·
                        rfl

theorem cell23_111287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_111287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111287 prefixEnd_111287 := by exact prefixLift 111287
  have htrace : WordTrace (prefixWord ++ tailWord_111287) baseStart_111287 baseEnd_111287 := by
    simpa [prefixWord, tailWord_111287, baseEnd_111287] using wordTrace_append hprefix tailTrace_111287
  have hstable : (prefixWord ++ tailWord_111287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111287).length < 2 ^ (prefixWord ++ tailWord_111287).sum := by decide
  have hdescent : baseEnd_111287 < baseStart_111287 := by decide
  rcases family_descends (prefixWord ++ tailWord_111287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111339 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_111339 : Nat := 118140960795 + 111339 * 2 ^ 59
def prefixEnd_111339 : Nat := 4983230072969 + 3 ^ 40 * 111339 * 2
def baseEnd_111339 : Nat := 57170422591045119350467

theorem tailTrace_111339 : CollatzResearch.WordTrace tailWord_111339 prefixEnd_111339 57170422591045119350467 := by
  unfold tailWord_111339
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060866943645293032433071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2707244629096862021622047 4060866943645293032433071)
  ·
    refine ⟨6091300415467939548649607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4060866943645293032433071 6091300415467939548649607)
    ·
      refine ⟨9136950623201909322974411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6091300415467939548649607 9136950623201909322974411)
      ·
        refine ⟨13705425934802863984461617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9136950623201909322974411 13705425934802863984461617)
        ·
          refine ⟨10279069451102147988346213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13705425934802863984461617 10279069451102147988346213)
          ·
            refine ⟨1927325522081652747814915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10279069451102147988346213 1927325522081652747814915)
            ·
              refine ⟨2890988283122479121722373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927325522081652747814915 2890988283122479121722373)
              ·
                refine ⟨542060303085464835322945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890988283122479121722373 542060303085464835322945)
                ·
                  refine ⟨406545227314098626492209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542060303085464835322945 406545227314098626492209)
                  ·
                    refine ⟨304908920485573969869157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406545227314098626492209 304908920485573969869157)
                    ·
                      refine ⟨57170422591045119350467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 304908920485573969869157 57170422591045119350467)
                      ·
                        rfl

theorem cell23_111339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_111339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111339 prefixEnd_111339 := by exact prefixLift 111339
  have htrace : WordTrace (prefixWord ++ tailWord_111339) baseStart_111339 baseEnd_111339 := by
    simpa [prefixWord, tailWord_111339, baseEnd_111339] using wordTrace_append hprefix tailTrace_111339
  have hstable : (prefixWord ++ tailWord_111339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111339).length < 2 ^ (prefixWord ++ tailWord_111339).sum := by decide
  have hdescent : baseEnd_111339 < baseStart_111339 := by decide
  rcases family_descends (prefixWord ++ tailWord_111339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111346 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_111346 : Nat := 118140960795 + 111346 * 2 ^ 59
def prefixEnd_111346 : Nat := 4983230072969 + 3 ^ 40 * 111346 * 2
def baseEnd_111346 : Nat := 57174016955626591962935

theorem tailTrace_111346 : CollatzResearch.WordTrace tailWord_111346 prefixEnd_111346 57174016955626591962935 := by
  unfold tailWord_111346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015280563654983306984473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2707414836413288818625261 1015280563654983306984473)
  ·
    refine ⟨761460422741237480238355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1015280563654983306984473 761460422741237480238355)
    ·
      refine ⟨1142190634111856220357533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761460422741237480238355 1142190634111856220357533)
      ·
        refine ⟨428321487791946082634075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1142190634111856220357533 428321487791946082634075)
        ·
          refine ⟨642482231687919123951113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428321487791946082634075 642482231687919123951113)
          ·
            refine ⟨481861673765939342963335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642482231687919123951113 481861673765939342963335)
            ·
              refine ⟨722792510648909014445003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481861673765939342963335 722792510648909014445003)
              ·
                refine ⟨1084188765973363521667505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722792510648909014445003 1084188765973363521667505)
                ·
                  refine ⟨813141574480022641250629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084188765973363521667505 813141574480022641250629)
                  ·
                    refine ⟨152464045215004245234493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813141574480022641250629 152464045215004245234493)
                    ·
                      refine ⟨57174016955626591962935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152464045215004245234493 57174016955626591962935)
                      ·
                        rfl

theorem cell23_111346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_111346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111346 prefixEnd_111346 := by exact prefixLift 111346
  have htrace : WordTrace (prefixWord ++ tailWord_111346) baseStart_111346 baseEnd_111346 := by
    simpa [prefixWord, tailWord_111346, baseEnd_111346] using wordTrace_append hprefix tailTrace_111346
  have hstable : (prefixWord ++ tailWord_111346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111346).length < 2 ^ (prefixWord ++ tailWord_111346).sum := by decide
  have hdescent : baseEnd_111346 < baseStart_111346 := by decide
  rcases family_descends (prefixWord ++ tailWord_111346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111356 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_111356 : Nat := 118140960795 + 111356 * 2 ^ 59
def prefixEnd_111356 : Nat := 4983230072969 + 3 ^ 40 * 111356 * 2
def baseEnd_111356 : Nat := 57179151762171552837889

theorem tailTrace_111356 : CollatzResearch.WordTrace tailWord_111356 prefixEnd_111356 57179151762171552837889 := by
  unfold tailWord_111356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030743492291852467900961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2707657989722469957201281 2030743492291852467900961)
  ·
    refine ⟨1523057619218889350925721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2030743492291852467900961 1523057619218889350925721)
    ·
      refine ⟨1142293214414167013194291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1523057619218889350925721 1142293214414167013194291)
      ·
        refine ⟨1713439821621250519791437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142293214414167013194291 1713439821621250519791437)
        ·
          refine ⟨642539933107968944921789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1713439821621250519791437 642539933107968944921789)
          ·
            refine ⟨240952474915488354345671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642539933107968944921789 240952474915488354345671)
            ·
              refine ⟨361428712373232531518507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240952474915488354345671 361428712373232531518507)
              ·
                refine ⟨542143068559848797277761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361428712373232531518507 542143068559848797277761)
                ·
                  refine ⟨406607301419886597958321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542143068559848797277761 406607301419886597958321)
                  ·
                    refine ⟨304955476064914948468741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406607301419886597958321 304955476064914948468741)
                    ·
                      refine ⟨57179151762171552837889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 304955476064914948468741 57179151762171552837889)
                      ·
                        rfl

theorem cell23_111356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_111356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111356 prefixEnd_111356 := by exact prefixLift 111356
  have htrace : WordTrace (prefixWord ++ tailWord_111356) baseStart_111356 baseEnd_111356 := by
    simpa [prefixWord, tailWord_111356, baseEnd_111356] using wordTrace_append hprefix tailTrace_111356
  have hstable : (prefixWord ++ tailWord_111356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111356).length < 2 ^ (prefixWord ++ tailWord_111356).sum := by decide
  have hdescent : baseEnd_111356 < baseStart_111356 := by decide
  rcases family_descends (prefixWord ++ tailWord_111356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111379 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 7]
def baseStart_111379 : Nat := 118140960795 + 111379 * 2 ^ 59
def prefixEnd_111379 : Nat := 4983230072969 + 3 ^ 40 * 111379 * 2
def baseEnd_111379 : Nat := 19063653939074987616761

theorem tailTrace_111379 : CollatzResearch.WordTrace tailWord_111379 prefixEnd_111379 19063653939074987616761 := by
  unfold tailWord_111379
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062325863500379863889191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2708217242333586575926127 4062325863500379863889191)
  ·
    refine ⟨6093488795250569795833787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4062325863500379863889191 6093488795250569795833787)
    ·
      refine ⟨9140233192875854693750681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093488795250569795833787 9140233192875854693750681)
      ·
        refine ⟨6855174894656891020313011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9140233192875854693750681 6855174894656891020313011)
        ·
          refine ⟨10282762341985336530469517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6855174894656891020313011 10282762341985336530469517)
          ·
            refine ⟨3856035878244501198926069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10282762341985336530469517 3856035878244501198926069)
            ·
              refine ⟨361503363585421987399319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3856035878244501198926069 361503363585421987399319)
              ·
                refine ⟨542255045378132981098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361503363585421987399319 542255045378132981098979)
                ·
                  refine ⟨813382568067199471648469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542255045378132981098979 813382568067199471648469)
                  ·
                    refine ⟨19063653939074987616761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 813382568067199471648469 19063653939074987616761)
                    ·
                      rfl

theorem cell23_111379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_111379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111379 prefixEnd_111379 := by exact prefixLift 111379
  have htrace : WordTrace (prefixWord ++ tailWord_111379) baseStart_111379 baseEnd_111379 := by
    simpa [prefixWord, tailWord_111379, baseEnd_111379] using wordTrace_append hprefix tailTrace_111379
  have hstable : (prefixWord ++ tailWord_111379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111379).length < 2 ^ (prefixWord ++ tailWord_111379).sum := by decide
  have hdescent : baseEnd_111379 < baseStart_111379 := by decide
  rcases family_descends (prefixWord ++ tailWord_111379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111429 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_111429 : Nat := 118140960795 + 111429 * 2 ^ 59
def prefixEnd_111429 : Nat := 4983230072969 + 3 ^ 40 * 111429 * 2
def baseEnd_111429 : Nat := 57216635849949767225053

theorem tailTrace_111429 : CollatzResearch.WordTrace tailWord_111429 prefixEnd_111429 57216635849949767225053 := by
  unfold tailWord_111429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064149513319238403209341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2709433008879492268806227 4064149513319238403209341)
  ·
    refine ⟨1524056067494714401203503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4064149513319238403209341 1524056067494714401203503)
    ·
      refine ⟨2286084101242071601805255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524056067494714401203503 2286084101242071601805255)
      ·
        refine ⟨3429126151863107402707883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286084101242071601805255 3429126151863107402707883)
        ·
          refine ⟨5143689227794661104061825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429126151863107402707883 5143689227794661104061825)
          ·
            refine ⟨3857766920845995828046369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5143689227794661104061825 3857766920845995828046369)
            ·
              refine ⟨2893325190634496871034777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857766920845995828046369 2893325190634496871034777)
              ·
                refine ⟨2169993892975872653276083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893325190634496871034777 2169993892975872653276083)
                ·
                  refine ⟨3254990839463808979914125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169993892975872653276083 3254990839463808979914125)
                  ·
                    refine ⟨1220621564798928367467797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254990839463808979914125 1220621564798928367467797)
                    ·
                      refine ⟨57216635849949767225053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1220621564798928367467797 57216635849949767225053)
                      ·
                        rfl

theorem cell23_111429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_111429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111429 prefixEnd_111429 := by exact prefixLift 111429
  have htrace : WordTrace (prefixWord ++ tailWord_111429) baseStart_111429 baseEnd_111429 := by
    simpa [prefixWord, tailWord_111429, baseEnd_111429] using wordTrace_append hprefix tailTrace_111429
  have hstable : (prefixWord ++ tailWord_111429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111429).length < 2 ^ (prefixWord ++ tailWord_111429).sum := by decide
  have hdescent : baseEnd_111429 < baseStart_111429 := by decide
  rcases family_descends (prefixWord ++ tailWord_111429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111456 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 6]
def baseStart_111456 : Nat := 118140960795 + 111456 * 2 ^ 59
def prefixEnd_111456 : Nat := 4983230072969 + 3 ^ 40 * 111456 * 2
def baseEnd_111456 : Nat := 6358944425291240176381

theorem tailTrace_111456 : CollatzResearch.WordTrace tailWord_111456 prefixEnd_111456 6358944425291240176381 := by
  unfold tailWord_111456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032567142110711007221111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2710089522814281342961481 2032567142110711007221111)
  ·
    refine ⟨3048850713166066510831667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032567142110711007221111 3048850713166066510831667)
    ·
      refine ⟨4573276069749099766247501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3048850713166066510831667 4573276069749099766247501)
      ·
        refine ⟨1714978526155912412342813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4573276069749099766247501 1714978526155912412342813)
        ·
          refine ⟨643116947308467154628555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1714978526155912412342813 643116947308467154628555)
          ·
            refine ⟨964675420962700731942833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643116947308467154628555 964675420962700731942833)
            ·
              refine ⟨723506565722025548957125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964675420962700731942833 723506565722025548957125)
              ·
                refine ⟨135657481072879790429461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723506565722025548957125 135657481072879790429461)
                ·
                  refine ⟨6358944425291240176381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135657481072879790429461 6358944425291240176381)
                  ·
                    rfl

theorem cell23_111456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_111456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111456 prefixEnd_111456 := by exact prefixLift 111456
  have htrace : WordTrace (prefixWord ++ tailWord_111456) baseStart_111456 baseEnd_111456 := by
    simpa [prefixWord, tailWord_111456, baseEnd_111456] using wordTrace_append hprefix tailTrace_111456
  have hstable : (prefixWord ++ tailWord_111456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111456).length < 2 ^ (prefixWord ++ tailWord_111456).sum := by decide
  have hdescent : baseEnd_111456 < baseStart_111456 := by decide
  rcases family_descends (prefixWord ++ tailWord_111456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111460 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_111460 : Nat := 118140960795 + 111460 * 2 ^ 59
def prefixEnd_111460 : Nat := 4983230072969 + 3 ^ 40 * 111460 * 2
def baseEnd_111460 : Nat := 19077517916746381979137

theorem tailTrace_111460 : CollatzResearch.WordTrace tailWord_111460 prefixEnd_111460 19077517916746381979137 := by
  unfold tailWord_111460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032640088103465348793917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2710186784137953798391889 2032640088103465348793917)
  ·
    refine ⟨762240033038799505797719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2032640088103465348793917 762240033038799505797719)
    ·
      refine ⟨1143360049558199258696579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762240033038799505797719 1143360049558199258696579)
      ·
        refine ⟨1715040074337298888044869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143360049558199258696579 1715040074337298888044869)
        ·
          refine ⟨321570013938243541508413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1715040074337298888044869 321570013938243541508413)
          ·
            refine ⟨120588755226841328065655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321570013938243541508413 120588755226841328065655)
            ·
              refine ⟨180883132840261992098483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120588755226841328065655 180883132840261992098483)
              ·
                refine ⟨271324699260392988147725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180883132840261992098483 271324699260392988147725)
                ·
                  refine ⟨101746762222647370555397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271324699260392988147725 101746762222647370555397)
                  ·
                    refine ⟨19077517916746381979137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101746762222647370555397 19077517916746381979137)
                    ·
                      rfl

theorem cell23_111460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_111460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111460 prefixEnd_111460 := by exact prefixLift 111460
  have htrace : WordTrace (prefixWord ++ tailWord_111460) baseStart_111460 baseEnd_111460 := by
    simpa [prefixWord, tailWord_111460, baseEnd_111460] using wordTrace_append hprefix tailTrace_111460
  have hstable : (prefixWord ++ tailWord_111460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111460).length < 2 ^ (prefixWord ++ tailWord_111460).sum := by decide
  have hdescent : baseEnd_111460 < baseStart_111460 := by decide
  rcases family_descends (prefixWord ++ tailWord_111460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111473 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 6]
def baseStart_111473 : Nat := 118140960795 + 111473 * 2 ^ 59
def prefixEnd_111473 : Nat := 4983230072969 + 3 ^ 40 * 111473 * 2
def baseEnd_111473 : Nat := 6359914333194177230539

theorem tailTrace_111473 : CollatzResearch.WordTrace tailWord_111473 prefixEnd_111473 6359914333194177230539 := by
  unfold tailWord_111473
  simp only [CollatzResearch.WordTrace]
  refine ⟨4065754325159833917811073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2710502883439889278540715 4065754325159833917811073)
  ·
    refine ⟨3049315743869875438358305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4065754325159833917811073 3049315743869875438358305)
    ·
      refine ⟨2286986807902406578768729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3049315743869875438358305 2286986807902406578768729)
      ·
        refine ⟨1715240105926804934076547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2286986807902406578768729 1715240105926804934076547)
        ·
          refine ⟨2572860158890207401114821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715240105926804934076547 2572860158890207401114821)
          ·
            refine ⟨482411279791913887709029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2572860158890207401114821 482411279791913887709029)
            ·
              refine ⟨90452114960983853945443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 482411279791913887709029 90452114960983853945443)
              ·
                refine ⟨135678172441475780918165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90452114960983853945443 135678172441475780918165)
                ·
                  refine ⟨6359914333194177230539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135678172441475780918165 6359914333194177230539)
                  ·
                    rfl

theorem cell23_111473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 6].length) (baseStart_111473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111473 prefixEnd_111473 := by exact prefixLift 111473
  have htrace : WordTrace (prefixWord ++ tailWord_111473) baseStart_111473 baseEnd_111473 := by
    simpa [prefixWord, tailWord_111473, baseEnd_111473] using wordTrace_append hprefix tailTrace_111473
  have hstable : (prefixWord ++ tailWord_111473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111473).length < 2 ^ (prefixWord ++ tailWord_111473).sum := by decide
  have hdescent : baseEnd_111473 < baseStart_111473 := by decide
  rcases family_descends (prefixWord ++ tailWord_111473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111483 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 3]
def baseStart_111483 : Nat := 118140960795 + 111483 * 2 ^ 59
def prefixEnd_111483 : Nat := 4983230072969 + 3 ^ 40 * 111483 * 2
def baseEnd_111483 : Nat := 57244363805292555949805

theorem tailTrace_111483 : CollatzResearch.WordTrace tailWord_111483 prefixEnd_111483 57244363805292555949805 := by
  unfold tailWord_111483
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066119055123605625675103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2710746036749070417116735 4066119055123605625675103)
  ·
    refine ⟨6099178582685408438512655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4066119055123605625675103 6099178582685408438512655)
    ·
      refine ⟨9148767874028112657768983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099178582685408438512655 9148767874028112657768983)
      ·
        refine ⟨13723151811042168986653475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9148767874028112657768983 13723151811042168986653475)
        ·
          refine ⟨20584727716563253479980213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723151811042168986653475 20584727716563253479980213)
          ·
            refine ⟨1929818223427805013748145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20584727716563253479980213 1929818223427805013748145)
            ·
              refine ⟨1447363667570853760311109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929818223427805013748145 1447363667570853760311109)
              ·
                refine ⟨271380687669535080058333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1447363667570853760311109 271380687669535080058333)
                ·
                  refine ⟨101767757876075655021875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271380687669535080058333 101767757876075655021875)
                  ·
                    refine ⟨152651636814113482532813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101767757876075655021875 152651636814113482532813)
                    ·
                      refine ⟨57244363805292555949805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152651636814113482532813 57244363805292555949805)
                      ·
                        rfl

theorem cell23_111483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 3].length) (baseStart_111483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111483 prefixEnd_111483 := by exact prefixLift 111483
  have htrace : WordTrace (prefixWord ++ tailWord_111483) baseStart_111483 baseEnd_111483 := by
    simpa [prefixWord, tailWord_111483, baseEnd_111483] using wordTrace_append hprefix tailTrace_111483
  have hstable : (prefixWord ++ tailWord_111483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111483).length < 2 ^ (prefixWord ++ tailWord_111483).sum := by decide
  have hdescent : baseEnd_111483 < baseStart_111483 := by decide
  rcases family_descends (prefixWord ++ tailWord_111483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111517 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_111517 : Nat := 118140960795 + 111517 * 2 ^ 59
def prefixEnd_111517 : Nat := 4983230072969 + 3 ^ 40 * 111517 * 2
def baseEnd_111517 : Nat := 57261822147545422924649

theorem tailTrace_111517 : CollatzResearch.WordTrace tailWord_111517 prefixEnd_111517 57261822147545422924649 := by
  unfold tailWord_111517
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067359137000429432412805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2711572758000286288275203 4067359137000429432412805)
  ·
    refine ⟨762629838187580518577401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4067359137000429432412805 762629838187580518577401)
    ·
      refine ⟨571972378640685388933051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762629838187580518577401 571972378640685388933051)
      ·
        refine ⟨857958567961028083399577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571972378640685388933051 857958567961028083399577)
        ·
          refine ⟨643468925970771062549683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857958567961028083399577 643468925970771062549683)
          ·
            refine ⟨965203388956156593824525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643468925970771062549683 965203388956156593824525)
            ·
              refine ⟨361951270858558722684197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 965203388956156593824525 361951270858558722684197)
              ·
                refine ⟨67865863285979760503287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361951270858558722684197 67865863285979760503287)
                ·
                  refine ⟨101798794928969640754931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67865863285979760503287 101798794928969640754931)
                  ·
                    refine ⟨152698192393454461132397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101798794928969640754931 152698192393454461132397)
                    ·
                      refine ⟨57261822147545422924649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152698192393454461132397 57261822147545422924649)
                      ·
                        rfl

theorem cell23_111517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_111517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111517 prefixEnd_111517 := by exact prefixLift 111517
  have htrace : WordTrace (prefixWord ++ tailWord_111517) baseStart_111517 baseEnd_111517 := by
    simpa [prefixWord, tailWord_111517, baseEnd_111517] using wordTrace_append hprefix tailTrace_111517
  have hstable : (prefixWord ++ tailWord_111517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111517).length < 2 ^ (prefixWord ++ tailWord_111517).sum := by decide
  have hdescent : baseEnd_111517 < baseStart_111517 := by decide
  rcases family_descends (prefixWord ++ tailWord_111517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111543 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_111543 : Nat := 118140960795 + 111543 * 2 ^ 59
def prefixEnd_111543 : Nat := 4983230072969 + 3 ^ 40 * 111543 * 2
def baseEnd_111543 : Nat := 57275172644562321199529

theorem tailTrace_111543 : CollatzResearch.WordTrace tailWord_111543 prefixEnd_111543 57275172644562321199529 := by
  unfold tailWord_111543
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068307434906235872859283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2712204956604157248572855 4068307434906235872859283)
  ·
    refine ⟨6102461152359353809288925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4068307434906235872859283 6102461152359353809288925)
    ·
      refine ⟨2288422932134757678483347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6102461152359353809288925 2288422932134757678483347)
      ·
        refine ⟨3432634398202136517725021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288422932134757678483347 3432634398202136517725021)
        ·
          refine ⟨1287237899325801194146883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3432634398202136517725021 1287237899325801194146883)
          ·
            refine ⟨1930856848988701791220325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287237899325801194146883 1930856848988701791220325)
            ·
              refine ⟨362035659185381585853811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1930856848988701791220325 362035659185381585853811)
              ·
                refine ⟨543053488778072378780717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362035659185381585853811 543053488778072378780717)
                ·
                  refine ⟨203645058291777142042769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543053488778072378780717 203645058291777142042769)
                  ·
                    refine ⟨152733793718832856532077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203645058291777142042769 152733793718832856532077)
                    ·
                      refine ⟨57275172644562321199529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 152733793718832856532077 57275172644562321199529)
                      ·
                        rfl

theorem cell23_111543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_111543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111543 prefixEnd_111543 := by exact prefixLift 111543
  have htrace : WordTrace (prefixWord ++ tailWord_111543) baseStart_111543 baseEnd_111543 := by
    simpa [prefixWord, tailWord_111543, baseEnd_111543] using wordTrace_append hprefix tailTrace_111543
  have hstable : (prefixWord ++ tailWord_111543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111543).length < 2 ^ (prefixWord ++ tailWord_111543).sum := by decide
  have hdescent : baseEnd_111543 < baseStart_111543 := by decide
  rcases family_descends (prefixWord ++ tailWord_111543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111558 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_111558 : Nat := 118140960795 + 111558 * 2 ^ 59
def prefixEnd_111558 : Nat := 4983230072969 + 3 ^ 40 * 111558 * 2
def baseEnd_111558 : Nat := 6364763872708862501329

theorem tailTrace_111558 : CollatzResearch.WordTrace tailWord_111558 prefixEnd_111558 6364763872708862501329 := by
  unfold tailWord_111558
  simp only [CollatzResearch.WordTrace]
  refine ⟨127151704057871669832979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2712569686567928956436885 127151704057871669832979)
  ·
    refine ⟨190727556086807504749469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127151704057871669832979 190727556086807504749469)
    ·
      refine ⟨71522833532552814281051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190727556086807504749469 71522833532552814281051)
      ·
        refine ⟨107284250298829221421577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71522833532552814281051 107284250298829221421577)
        ·
          refine ⟨80463187724121916066183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107284250298829221421577 80463187724121916066183)
          ·
            refine ⟨120694781586182874099275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80463187724121916066183 120694781586182874099275)
            ·
              refine ⟨181042172379274311148913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120694781586182874099275 181042172379274311148913)
              ·
                refine ⟨135781629284455733361685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181042172379274311148913 135781629284455733361685)
                ·
                  refine ⟨6364763872708862501329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135781629284455733361685 6364763872708862501329)
                  ·
                    rfl

theorem cell23_111558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_111558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111558 prefixEnd_111558 := by exact prefixLift 111558
  have htrace : WordTrace (prefixWord ++ tailWord_111558) baseStart_111558 baseEnd_111558 := by
    simpa [prefixWord, tailWord_111558, baseEnd_111558] using wordTrace_append hprefix tailTrace_111558
  have hstable : (prefixWord ++ tailWord_111558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111558).length < 2 ^ (prefixWord ++ tailWord_111558).sum := by decide
  have hdescent : baseEnd_111558 < baseStart_111558 := by decide
  rcases family_descends (prefixWord ++ tailWord_111558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111574 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_111574 : Nat := 118140960795 + 111574 * 2 ^ 59
def prefixEnd_111574 : Nat := 4983230072969 + 3 ^ 40 * 111574 * 2
def baseEnd_111574 : Nat := 57291090544851699911887

theorem tailTrace_111574 : CollatzResearch.WordTrace tailWord_111574 prefixEnd_111574 57291090544851699911887 := by
  unfold tailWord_111574
  simp only [CollatzResearch.WordTrace]
  refine ⟨254339881112120510452361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2712958731862618778158517 254339881112120510452361)
  ·
    refine ⟨190754910834090382839271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254339881112120510452361 190754910834090382839271)
    ·
      refine ⟨286132366251135574258907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190754910834090382839271 286132366251135574258907)
      ·
        refine ⟨429198549376703361388361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286132366251135574258907 429198549376703361388361)
        ·
          refine ⟨321898912032527521041271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429198549376703361388361 321898912032527521041271)
          ·
            refine ⟨482848368048791281561907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321898912032527521041271 482848368048791281561907)
            ·
              refine ⟨724272552073186922342861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482848368048791281561907 724272552073186922342861)
              ·
                refine ⟨271602207027445095878573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724272552073186922342861 271602207027445095878573)
                ·
                  refine ⟨101850827635291910954465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271602207027445095878573 101850827635291910954465)
                  ·
                    refine ⟨76388120726468933215849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101850827635291910954465 76388120726468933215849)
                    ·
                      refine ⟨57291090544851699911887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76388120726468933215849 57291090544851699911887)
                      ·
                        rfl

theorem cell23_111574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_111574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111574 prefixEnd_111574 := by exact prefixLift 111574
  have htrace : WordTrace (prefixWord ++ tailWord_111574) baseStart_111574 baseEnd_111574 := by
    simpa [prefixWord, tailWord_111574, baseEnd_111574] using wordTrace_append hprefix tailTrace_111574
  have hstable : (prefixWord ++ tailWord_111574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111574).length < 2 ^ (prefixWord ++ tailWord_111574).sum := by decide
  have hdescent : baseEnd_111574 < baseStart_111574 := by decide
  rcases family_descends (prefixWord ++ tailWord_111574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111617 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_111617 : Nat := 118140960795 + 111617 * 2 ^ 59
def prefixEnd_111617 : Nat := 4983230072969 + 3 ^ 40 * 111617 * 2
def baseEnd_111617 : Nat := 57313170212995031674189

theorem tailTrace_111617 : CollatzResearch.WordTrace tailWord_111617 prefixEnd_111617 57313170212995031674189 := by
  unfold tailWord_111617
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071006436638146511053105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2714004291092097674035403 4071006436638146511053105)
  ·
    refine ⟨3053254827478609883289829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4071006436638146511053105 3053254827478609883289829)
    ·
      refine ⟨572485280152239353116843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3053254827478609883289829 572485280152239353116843)
      ·
        refine ⟨858727920228359029675265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572485280152239353116843 858727920228359029675265)
        ·
          refine ⟨644045940171269272256449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858727920228359029675265 644045940171269272256449)
          ·
            refine ⟨483034455128451954192337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644045940171269272256449 483034455128451954192337)
            ·
              refine ⟨362275841346338965644253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483034455128451954192337 362275841346338965644253)
              ·
                refine ⟨135853440504877112116595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362275841346338965644253 135853440504877112116595)
                ·
                  refine ⟨203780160757315668174893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135853440504877112116595 203780160757315668174893)
                  ·
                    refine ⟨76417560283993375565585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203780160757315668174893 76417560283993375565585)
                    ·
                      refine ⟨57313170212995031674189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76417560283993375565585 57313170212995031674189)
                      ·
                        rfl

theorem cell23_111617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_111617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111617 prefixEnd_111617 := by exact prefixLift 111617
  have htrace : WordTrace (prefixWord ++ tailWord_111617) baseStart_111617 baseEnd_111617 := by
    simpa [prefixWord, tailWord_111617, baseEnd_111617] using wordTrace_append hprefix tailTrace_111617
  have hstable : (prefixWord ++ tailWord_111617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111617).length < 2 ^ (prefixWord ++ tailWord_111617).sum := by decide
  have hdescent : baseEnd_111617 < baseStart_111617 := by decide
  rcases family_descends (prefixWord ++ tailWord_111617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111681 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_111681 : Nat := 118140960795 + 111681 * 2 ^ 59
def prefixEnd_111681 : Nat := 4983230072969 + 3 ^ 40 * 111681 * 2
def baseEnd_111681 : Nat := 57346032974882781273895

theorem tailTrace_111681 : CollatzResearch.WordTrace tailWord_111681 prefixEnd_111681 57346032974882781273895 := by
  unfold tailWord_111681
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073340708406285441382897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2715560472270856960921931 4073340708406285441382897)
  ·
    refine ⟨3055005531304714081037173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4073340708406285441382897 3055005531304714081037173)
    ·
      refine ⟨286406768559816945097235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3055005531304714081037173 286406768559816945097235)
      ·
        refine ⟨429610152839725417645853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286406768559816945097235 429610152839725417645853)
        ·
          refine ⟨161103807314897031617195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429610152839725417645853 161103807314897031617195)
          ·
            refine ⟨241655710972345547425793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161103807314897031617195 241655710972345547425793)
            ·
              refine ⟨181241783229259160569345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241655710972345547425793 181241783229259160569345)
              ·
                refine ⟨135931337421944370427009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181241783229259160569345 135931337421944370427009)
                ·
                  refine ⟨101948503066458277820257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135931337421944370427009 101948503066458277820257)
                  ·
                    refine ⟨76461377299843708365193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101948503066458277820257 76461377299843708365193)
                    ·
                      refine ⟨57346032974882781273895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76461377299843708365193 57346032974882781273895)
                      ·
                        rfl

theorem cell23_111681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_111681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111681 prefixEnd_111681 := by exact prefixLift 111681
  have htrace : WordTrace (prefixWord ++ tailWord_111681) baseStart_111681 baseEnd_111681 := by
    simpa [prefixWord, tailWord_111681, baseEnd_111681] using wordTrace_append hprefix tailTrace_111681
  have hstable : (prefixWord ++ tailWord_111681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111681).length < 2 ^ (prefixWord ++ tailWord_111681).sum := by decide
  have hdescent : baseEnd_111681 < baseStart_111681 := by decide
  rcases family_descends (prefixWord ++ tailWord_111681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111683 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 2, 5]
def baseStart_111683 : Nat := 118140960795 + 111683 * 2 ^ 59
def prefixEnd_111683 : Nat := 4983230072969 + 3 ^ 40 * 111683 * 2
def baseEnd_111683 : Nat := 19115686645397257816295

theorem tailTrace_111683 : CollatzResearch.WordTrace tailWord_111683 prefixEnd_111683 19115686645397257816295 := by
  unfold tailWord_111683
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073413654399039782955703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2715609102932693188637135 4073413654399039782955703)
  ·
    refine ⟨6110120481598559674433555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4073413654399039782955703 6110120481598559674433555)
    ·
      refine ⟨9165180722397839511650333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110120481598559674433555 9165180722397839511650333)
      ·
        refine ⟨3436942770899189816868875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9165180722397839511650333 3436942770899189816868875)
        ·
          refine ⟨5155414156348784725303313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436942770899189816868875 5155414156348784725303313)
          ·
            refine ⟨3866560617261588543977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155414156348784725303313 3866560617261588543977485)
            ·
              refine ⟨1449960231473095703991557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866560617261588543977485 1449960231473095703991557)
              ·
                refine ⟨271867543401205444498417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1449960231473095703991557 271867543401205444498417)
                ·
                  refine ⟨203900657550904083373813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271867543401205444498417 203900657550904083373813)
                  ·
                    refine ⟨19115686645397257816295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203900657550904083373813 19115686645397257816295)
                    ·
                      rfl

theorem cell23_111683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 5].length) (baseStart_111683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111683 prefixEnd_111683 := by exact prefixLift 111683
  have htrace : WordTrace (prefixWord ++ tailWord_111683) baseStart_111683 baseEnd_111683 := by
    simpa [prefixWord, tailWord_111683, baseEnd_111683] using wordTrace_append hprefix tailTrace_111683
  have hstable : (prefixWord ++ tailWord_111683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111683).length < 2 ^ (prefixWord ++ tailWord_111683).sum := by decide
  have hdescent : baseEnd_111683 < baseStart_111683 := by decide
  rcases family_descends (prefixWord ++ tailWord_111683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111687 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 5]
def baseStart_111687 : Nat := 118140960795 + 111687 * 2 ^ 59
def prefixEnd_111687 : Nat := 4983230072969 + 3 ^ 40 * 111687 * 2
def baseEnd_111687 : Nat := 6372123762089973088763

theorem tailTrace_111687 : CollatzResearch.WordTrace tailWord_111687 prefixEnd_111687 6372123762089973088763 := by
  unfold tailWord_111687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073559546384548466101315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2715706364256365644067543 4073559546384548466101315)
  ·
    refine ⟨6110339319576822699151973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4073559546384548466101315 6110339319576822699151973)
    ·
      refine ⟨1145688622420654256090995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6110339319576822699151973 1145688622420654256090995)
      ·
        refine ⟨1718532933630981384136493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145688622420654256090995 1718532933630981384136493)
        ·
          refine ⟨644449850111618019051185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1718532933630981384136493 644449850111618019051185)
          ·
            refine ⟨483337387583713514288389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644449850111618019051185 483337387583713514288389)
            ·
              refine ⟨90625760171946283929073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483337387583713514288389 90625760171946283929073)
              ·
                refine ⟨67969320128959712946805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90625760171946283929073 67969320128959712946805)
                ·
                  refine ⟨6372123762089973088763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67969320128959712946805 6372123762089973088763)
                  ·
                    rfl

theorem cell23_111687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 5].length) (baseStart_111687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111687 prefixEnd_111687 := by exact prefixLift 111687
  have htrace : WordTrace (prefixWord ++ tailWord_111687) baseStart_111687 baseEnd_111687 := by
    simpa [prefixWord, tailWord_111687, baseEnd_111687] using wordTrace_append hprefix tailTrace_111687
  have hstable : (prefixWord ++ tailWord_111687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111687).length < 2 ^ (prefixWord ++ tailWord_111687).sum := by decide
  have hdescent : baseEnd_111687 < baseStart_111687 := by decide
  rcases family_descends (prefixWord ++ tailWord_111687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111690 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_111690 : Nat := 118140960795 + 111690 * 2 ^ 59
def prefixEnd_111690 : Nat := 4983230072969 + 3 ^ 40 * 111690 * 2
def baseEnd_111690 : Nat := 57350654300773246061353

theorem tailTrace_111690 : CollatzResearch.WordTrace tailWord_111690 prefixEnd_111690 57350654300773246061353 := by
  unfold tailWord_111690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018417241343419994615131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2715779310249119985640349 1018417241343419994615131)
  ·
    refine ⟨1527625862015129991922697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018417241343419994615131 1527625862015129991922697)
    ·
      refine ⟨1145719396511347493942023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1527625862015129991922697 1145719396511347493942023)
      ·
        refine ⟨1718579094767021240913035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145719396511347493942023 1718579094767021240913035)
        ·
          refine ⟨2577868642150531861369553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718579094767021240913035 2577868642150531861369553)
          ·
            refine ⟨1933401481612898896027165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577868642150531861369553 1933401481612898896027165)
            ·
              refine ⟨725025555604837086010187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1933401481612898896027165 725025555604837086010187)
              ·
                refine ⟨1087538333407255629015281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725025555604837086010187 1087538333407255629015281)
                ·
                  refine ⟨815653750055441721761461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087538333407255629015281 815653750055441721761461)
                  ·
                    refine ⟨76467539067697661415137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 815653750055441721761461 76467539067697661415137)
                    ·
                      refine ⟨57350654300773246061353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76467539067697661415137 57350654300773246061353)
                      ·
                        rfl

theorem cell23_111690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_111690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111690 prefixEnd_111690 := by exact prefixLift 111690
  have htrace : WordTrace (prefixWord ++ tailWord_111690) baseStart_111690 baseEnd_111690 := by
    simpa [prefixWord, tailWord_111690, baseEnd_111690] using wordTrace_append hprefix tailTrace_111690
  have hstable : (prefixWord ++ tailWord_111690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111690).length < 2 ^ (prefixWord ++ tailWord_111690).sum := by decide
  have hdescent : baseEnd_111690 < baseStart_111690 := by decide
  rcases family_descends (prefixWord ++ tailWord_111690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111703 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_111703 : Nat := 118140960795 + 111703 * 2 ^ 59
def prefixEnd_111703 : Nat := 4983230072969 + 3 ^ 40 * 111703 * 2
def baseEnd_111703 : Nat := 57357329549281695198793

theorem tailTrace_111703 : CollatzResearch.WordTrace tailWord_111703 prefixEnd_111703 57357329549281695198793 := by
  unfold tailWord_111703
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074143114326583198683763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2716095409551055465789175 4074143114326583198683763)
  ·
    refine ⟨6111214671489874798025645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4074143114326583198683763 6111214671489874798025645)
    ·
      refine ⟨2291705501808703049259617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6111214671489874798025645 2291705501808703049259617)
      ·
        refine ⟨1718779126356527286944713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2291705501808703049259617 1718779126356527286944713)
        ·
          refine ⟨1289084344767395465208535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718779126356527286944713 1289084344767395465208535)
          ·
            refine ⟨1933626517151093197812803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289084344767395465208535 1933626517151093197812803)
            ·
              refine ⟨2900439775726639796719205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933626517151093197812803 2900439775726639796719205)
              ·
                refine ⟨543832457948744961884851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2900439775726639796719205 543832457948744961884851)
                ·
                  refine ⟨815748686923117442827277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543832457948744961884851 815748686923117442827277)
                  ·
                    refine ⟨305905757596169041060229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815748686923117442827277 305905757596169041060229)
                    ·
                      refine ⟨57357329549281695198793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 305905757596169041060229 57357329549281695198793)
                      ·
                        rfl

theorem cell23_111703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_111703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111703 prefixEnd_111703 := by exact prefixLift 111703
  have htrace : WordTrace (prefixWord ++ tailWord_111703) baseStart_111703 baseEnd_111703 := by
    simpa [prefixWord, tailWord_111703, baseEnd_111703] using wordTrace_append hprefix tailTrace_111703
  have hstable : (prefixWord ++ tailWord_111703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111703).length < 2 ^ (prefixWord ++ tailWord_111703).sum := by decide
  have hdescent : baseEnd_111703 < baseStart_111703 := by decide
  rcases family_descends (prefixWord ++ tailWord_111703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111730 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_111730 : Nat := 118140960795 + 111730 * 2 ^ 59
def prefixEnd_111730 : Nat := 4983230072969 + 3 ^ 40 * 111730 * 2
def baseEnd_111730 : Nat := 19123731175651029853723

theorem tailTrace_111730 : CollatzResearch.WordTrace tailWord_111730 prefixEnd_111730 19123731175651029853723 := by
  unfold tailWord_111730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018781971307191702479161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2716751923485844539944429 1018781971307191702479161)
  ·
    refine ⟨764086478480393776859371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018781971307191702479161 764086478480393776859371)
    ·
      refine ⟨1146129717720590665289057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764086478480393776859371 1146129717720590665289057)
      ·
        refine ⟨859597288290442998966793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146129717720590665289057 859597288290442998966793)
        ·
          refine ⟨644697966217832249225095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859597288290442998966793 644697966217832249225095)
          ·
            refine ⟨967046949326748373837643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644697966217832249225095 967046949326748373837643)
            ·
              refine ⟨1450570423990122560756465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967046949326748373837643 1450570423990122560756465)
              ·
                refine ⟨1087927817992591920567349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450570423990122560756465 1087927817992591920567349)
                ·
                  refine ⟨101993232936805492553189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1087927817992591920567349 101993232936805492553189)
                  ·
                    refine ⟨19123731175651029853723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101993232936805492553189 19123731175651029853723)
                    ·
                      rfl

theorem cell23_111730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_111730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111730 prefixEnd_111730 := by exact prefixLift 111730
  have htrace : WordTrace (prefixWord ++ tailWord_111730) baseStart_111730 baseEnd_111730 := by
    simpa [prefixWord, tailWord_111730, baseEnd_111730] using wordTrace_append hprefix tailTrace_111730
  have hstable : (prefixWord ++ tailWord_111730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111730).length < 2 ^ (prefixWord ++ tailWord_111730).sum := by decide
  have hdescent : baseEnd_111730 < baseStart_111730 := by decide
  rcases family_descends (prefixWord ++ tailWord_111730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111740 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_111740 : Nat := 118140960795 + 111740 * 2 ^ 59
def prefixEnd_111740 : Nat := 4983230072969 + 3 ^ 40 * 111740 * 2
def baseEnd_111740 : Nat := 57376328333498050436123

theorem tailTrace_111740 : CollatzResearch.WordTrace tailWord_111740 prefixEnd_111740 57376328333498050436123 := by
  unfold tailWord_111740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037746307596269258890337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2716995076795025678520449 2037746307596269258890337)
  ·
    refine ⟨1528309730697201944167753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2037746307596269258890337 1528309730697201944167753)
    ·
      refine ⟨1146232298022901458125815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528309730697201944167753 1146232298022901458125815)
      ·
        refine ⟨1719348447034352187188723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146232298022901458125815 1719348447034352187188723)
        ·
          refine ⟨2579022670551528280783085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719348447034352187188723 2579022670551528280783085)
          ·
            refine ⟨967133501456823105293657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2579022670551528280783085 967133501456823105293657)
            ·
              refine ⟨725350126092617328970243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967133501456823105293657 725350126092617328970243)
              ·
                refine ⟨1088025189138925993455365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725350126092617328970243 1088025189138925993455365)
                ·
                  refine ⟨204004722963548623772881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088025189138925993455365 204004722963548623772881)
                  ·
                    refine ⟨153003542222661467829661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204004722963548623772881 153003542222661467829661)
                    ·
                      refine ⟨57376328333498050436123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153003542222661467829661 57376328333498050436123)
                      ·
                        rfl

theorem cell23_111740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_111740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111740 prefixEnd_111740 := by exact prefixLift 111740
  have htrace : WordTrace (prefixWord ++ tailWord_111740) baseStart_111740 baseEnd_111740 := by
    simpa [prefixWord, tailWord_111740, baseEnd_111740] using wordTrace_append hprefix tailTrace_111740
  have hstable : (prefixWord ++ tailWord_111740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111740).length < 2 ^ (prefixWord ++ tailWord_111740).sum := by decide
  have hdescent : baseEnd_111740 < baseStart_111740 := by decide
  rcases family_descends (prefixWord ++ tailWord_111740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111747 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 1, 4]
def baseStart_111747 : Nat := 118140960795 + 111747 * 2 ^ 59
def prefixEnd_111747 : Nat := 4983230072969 + 3 ^ 40 * 111747 * 2
def baseEnd_111747 : Nat := 19126640899359841016197

theorem tailTrace_111747 : CollatzResearch.WordTrace tailWord_111747 prefixEnd_111747 19126640899359841016197 := by
  unfold tailWord_111747
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075747926167178713285495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2717165284111452475523663 4075747926167178713285495)
  ·
    refine ⟨6113621889250768069928243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4075747926167178713285495 6113621889250768069928243)
    ·
      refine ⟨9170432833876152104892365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113621889250768069928243 9170432833876152104892365)
      ·
        refine ⟨3438912312703557039334637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9170432833876152104892365 3438912312703557039334637)
        ·
          refine ⟨1289592117263833889750489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3438912312703557039334637 1289592117263833889750489)
          ·
            refine ⟨967194087947875417312867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289592117263833889750489 967194087947875417312867)
            ·
              refine ⟨1450791131921813125969301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967194087947875417312867 1450791131921813125969301)
              ·
                refine ⟨68005834308834990279811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1450791131921813125969301 68005834308834990279811)
                ·
                  refine ⟨102008751463252485419717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68005834308834990279811 102008751463252485419717)
                  ·
                    refine ⟨19126640899359841016197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102008751463252485419717 19126640899359841016197)
                    ·
                      rfl

theorem cell23_111747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 4].length) (baseStart_111747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111747 prefixEnd_111747 := by exact prefixLift 111747
  have htrace : WordTrace (prefixWord ++ tailWord_111747) baseStart_111747 baseEnd_111747 := by
    simpa [prefixWord, tailWord_111747, baseEnd_111747] using wordTrace_append hprefix tailTrace_111747
  have hstable : (prefixWord ++ tailWord_111747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111747).length < 2 ^ (prefixWord ++ tailWord_111747).sum := by decide
  have hdescent : baseEnd_111747 < baseStart_111747 := by decide
  rcases family_descends (prefixWord ++ tailWord_111747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111798 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_111798 : Nat := 118140960795 + 111798 * 2 ^ 59
def prefixEnd_111798 : Nat := 4983230072969 + 3 ^ 40 * 111798 * 2
def baseEnd_111798 : Nat := 19135370070486274503619

theorem tailTrace_111798 : CollatzResearch.WordTrace tailWord_111798 prefixEnd_111798 19135370070486274503619 := by
  unfold tailWord_111798
  simp only [CollatzResearch.WordTrace]
  refine ⟨254850503061400901462003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2718405365988276282261365 254850503061400901462003)
  ·
    refine ⟨382275754592101352193005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254850503061400901462003 382275754592101352193005)
    ·
      refine ⟨143353407972038007072377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382275754592101352193005 143353407972038007072377)
      ·
        refine ⟨107515055979028505304283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143353407972038007072377 107515055979028505304283)
        ·
          refine ⟨161272583968542757956425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107515055979028505304283 161272583968542757956425)
          ·
            refine ⟨120954437976407068467319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161272583968542757956425 120954437976407068467319)
            ·
              refine ⟨181431656964610602700979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120954437976407068467319 181431656964610602700979)
              ·
                refine ⟨272147485446915904051469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181431656964610602700979 272147485446915904051469)
                ·
                  refine ⟨102055307042593464019301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272147485446915904051469 102055307042593464019301)
                  ·
                    refine ⟨19135370070486274503619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102055307042593464019301 19135370070486274503619)
                    ·
                      rfl

theorem cell23_111798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_111798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111798 prefixEnd_111798 := by exact prefixLift 111798
  have htrace : WordTrace (prefixWord ++ tailWord_111798) baseStart_111798 baseEnd_111798 := by
    simpa [prefixWord, tailWord_111798, baseEnd_111798] using wordTrace_append hprefix tailTrace_111798
  have hstable : (prefixWord ++ tailWord_111798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111798).length < 2 ^ (prefixWord ++ tailWord_111798).sum := by decide
  have hdescent : baseEnd_111798 < baseStart_111798 := by decide
  rcases family_descends (prefixWord ++ tailWord_111798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111803 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 5, 6]
def baseStart_111803 : Nat := 118140960795 + 111803 * 2 ^ 59
def prefixEnd_111803 : Nat := 4983230072969 + 3 ^ 40 * 111803 * 2
def baseEnd_111803 : Nat := 19136225871577101316111

theorem tailTrace_111803 : CollatzResearch.WordTrace tailWord_111803 prefixEnd_111803 19136225871577101316111 := by
  unfold tailWord_111803
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077790413964300277324063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2718526942642866851549375 4077790413964300277324063)
  ·
    refine ⟨6116685620946450415986095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077790413964300277324063 6116685620946450415986095)
    ·
      refine ⟨9175028431419675623979143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116685620946450415986095 9175028431419675623979143)
      ·
        refine ⟨13762542647129513435968715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175028431419675623979143 13762542647129513435968715)
        ·
          refine ⟨20643813970694270153953073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762542647129513435968715 20643813970694270153953073)
          ·
            refine ⟨15482860478020702615464805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20643813970694270153953073 15482860478020702615464805)
            ·
              refine ⟨2903036339628881740399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15482860478020702615464805 2903036339628881740399651)
              ·
                refine ⟨4354554509443322610599477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903036339628881740399651 4354554509443322610599477)
                ·
                  refine ⟨408239485260311494743701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4354554509443322610599477 408239485260311494743701)
                  ·
                    refine ⟨19136225871577101316111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 408239485260311494743701 19136225871577101316111)
                    ·
                      rfl

theorem cell23_111803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_111803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111803 prefixEnd_111803 := by exact prefixLift 111803
  have htrace : WordTrace (prefixWord ++ tailWord_111803) baseStart_111803 baseEnd_111803 := by
    simpa [prefixWord, tailWord_111803, baseEnd_111803] using wordTrace_append hprefix tailTrace_111803
  have hstable : (prefixWord ++ tailWord_111803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111803).length < 2 ^ (prefixWord ++ tailWord_111803).sum := by decide
  have hdescent : baseEnd_111803 < baseStart_111803 := by decide
  rcases family_descends (prefixWord ++ tailWord_111803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111804 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_111804 : Nat := 118140960795 + 111804 * 2 ^ 59
def prefixEnd_111804 : Nat := 4983230072969 + 3 ^ 40 * 111804 * 2
def baseEnd_111804 : Nat := 57409191095385800035829

theorem tailTrace_111804 : CollatzResearch.WordTrace tailWord_111804 prefixEnd_111804 57409191095385800035829 := by
  unfold tailWord_111804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038913443480338724055233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2718551257973784965406977 2038913443480338724055233)
  ·
    refine ⟨1529185082610254043041425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2038913443480338724055233 1529185082610254043041425)
    ·
      refine ⟨1146888811957690532281069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1529185082610254043041425 1146888811957690532281069)
      ·
        refine ⟨430083304484133949605401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1146888811957690532281069 430083304484133949605401)
        ·
          refine ⟨322562478363100462204051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430083304484133949605401 322562478363100462204051)
          ·
            refine ⟨483843717544650693306077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322562478363100462204051 483843717544650693306077)
            ·
              refine ⟨181441394079244009989779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483843717544650693306077 181441394079244009989779)
              ·
                refine ⟨272162091118866014984669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181441394079244009989779 272162091118866014984669)
                ·
                  refine ⟨102060784169574755619251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272162091118866014984669 102060784169574755619251)
                  ·
                    refine ⟨153091176254362133428877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102060784169574755619251 153091176254362133428877)
                    ·
                      refine ⟨57409191095385800035829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153091176254362133428877 57409191095385800035829)
                      ·
                        rfl

theorem cell23_111804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_111804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111804 prefixEnd_111804 := by exact prefixLift 111804
  have htrace : WordTrace (prefixWord ++ tailWord_111804) baseStart_111804 baseEnd_111804 := by
    simpa [prefixWord, tailWord_111804, baseEnd_111804] using wordTrace_append hprefix tailTrace_111804
  have hstable : (prefixWord ++ tailWord_111804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111804).length < 2 ^ (prefixWord ++ tailWord_111804).sum := by decide
  have hdescent : baseEnd_111804 < baseStart_111804 := by decide
  rcases family_descends (prefixWord ++ tailWord_111804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111840 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_111840 : Nat := 118140960795 + 111840 * 2 ^ 59
def prefixEnd_111840 : Nat := 4983230072969 + 3 ^ 40 * 111840 * 2
def baseEnd_111840 : Nat := 57427676398947659185663

theorem tailTrace_111840 : CollatzResearch.WordTrace tailWord_111840 prefixEnd_111840 57427676398947659185663 := by
  unfold tailWord_111840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039569957415127798210487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2719426609886837064280649 2039569957415127798210487)
  ·
    refine ⟨3059354936122691697315731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039569957415127798210487 3059354936122691697315731)
    ·
      refine ⟨4589032404184037545973597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059354936122691697315731 4589032404184037545973597)
      ·
        refine ⟨1720887151569014079740099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4589032404184037545973597 1720887151569014079740099)
        ·
          refine ⟨2581330727353521119610149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720887151569014079740099 2581330727353521119610149)
          ·
            refine ⟨483999511378785209926903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2581330727353521119610149 483999511378785209926903)
            ·
              refine ⟨725999267068177814890355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483999511378785209926903 725999267068177814890355)
              ·
                refine ⟨1088998900602266722335533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725999267068177814890355 1088998900602266722335533)
                ·
                  refine ⟨408374587725850020875825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088998900602266722335533 408374587725850020875825)
                  ·
                    refine ⟨306280940794387515656869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 408374587725850020875825 306280940794387515656869)
                    ·
                      refine ⟨57427676398947659185663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 306280940794387515656869 57427676398947659185663)
                      ·
                        rfl

theorem cell23_111840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_111840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111840 prefixEnd_111840 := by exact prefixLift 111840
  have htrace : WordTrace (prefixWord ++ tailWord_111840) baseStart_111840 baseEnd_111840 := by
    simpa [prefixWord, tailWord_111840, baseEnd_111840] using wordTrace_append hprefix tailTrace_111840
  have hstable : (prefixWord ++ tailWord_111840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111840).length < 2 ^ (prefixWord ++ tailWord_111840).sum := by decide
  have hdescent : baseEnd_111840 < baseStart_111840 := by decide
  rcases family_descends (prefixWord ++ tailWord_111840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111855 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 1, 1, 3]
def baseStart_111855 : Nat := 118140960795 + 111855 * 2 ^ 59
def prefixEnd_111855 : Nat := 4983230072969 + 3 ^ 40 * 111855 * 2
def baseEnd_111855 : Nat := 57435378608765100498095

theorem tailTrace_111855 : CollatzResearch.WordTrace tailWord_111855 prefixEnd_111855 57435378608765100498095 := by
  unfold tailWord_111855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079687009775913158217019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2719791339850608772144679 4079687009775913158217019)
  ·
    refine ⟨6119530514663869737325529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4079687009775913158217019 6119530514663869737325529)
    ·
      refine ⟨4589647885997902302994147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6119530514663869737325529 4589647885997902302994147)
      ·
        refine ⟨6884471828996853454491221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589647885997902302994147 6884471828996853454491221)
        ·
          refine ⟨80677404246056876419819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 6884471828996853454491221 80677404246056876419819)
          ·
            refine ⟨121016106369085314629729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80677404246056876419819 121016106369085314629729)
            ·
              refine ⟨90762079776813985972297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121016106369085314629729 90762079776813985972297)
              ·
                refine ⟨68071559832610489479223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90762079776813985972297 68071559832610489479223)
                ·
                  refine ⟨102107339748915734218835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68071559832610489479223 102107339748915734218835)
                  ·
                    refine ⟨153161009623373601328253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102107339748915734218835 153161009623373601328253)
                    ·
                      refine ⟨57435378608765100498095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153161009623373601328253 57435378608765100498095)
                      ·
                        rfl

theorem cell23_111855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 1, 3].length) (baseStart_111855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111855 prefixEnd_111855 := by exact prefixLift 111855
  have htrace : WordTrace (prefixWord ++ tailWord_111855) baseStart_111855 baseEnd_111855 := by
    simpa [prefixWord, tailWord_111855, baseEnd_111855] using wordTrace_append hprefix tailTrace_111855
  have hstable : (prefixWord ++ tailWord_111855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111855).length < 2 ^ (prefixWord ++ tailWord_111855).sum := by decide
  have hdescent : baseEnd_111855 < baseStart_111855 := by decide
  rcases family_descends (prefixWord ++ tailWord_111855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111877 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_111877 : Nat := 118140960795 + 111877 * 2 ^ 59
def prefixEnd_111877 : Nat := 4983230072969 + 3 ^ 40 * 111877 * 2
def baseEnd_111877 : Nat := 57446675183164014422993

theorem tailTrace_111877 : CollatzResearch.WordTrace tailWord_111877 prefixEnd_111877 57446675183164014422993 := by
  unfold tailWord_111877
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080489415696210915517885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2720326277130807277011923 4080489415696210915517885)
  ·
    refine ⟨1530183530886079093319207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4080489415696210915517885 1530183530886079093319207)
    ·
      refine ⟨2295275296329118639978811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530183530886079093319207 2295275296329118639978811)
      ·
        refine ⟨3442912944493677959968217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295275296329118639978811 3442912944493677959968217)
        ·
          refine ⟨2582184708370258469976163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442912944493677959968217 2582184708370258469976163)
          ·
            refine ⟨3873277062555387704964245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582184708370258469976163 3873277062555387704964245)
            ·
              refine ⟨181559862307283798670199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3873277062555387704964245 181559862307283798670199)
              ·
                refine ⟨272339793460925698005299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181559862307283798670199 272339793460925698005299)
                ·
                  refine ⟨408509690191388547007949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272339793460925698005299 408509690191388547007949)
                  ·
                    refine ⟨153191133821770705127981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408509690191388547007949 153191133821770705127981)
                    ·
                      refine ⟨57446675183164014422993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153191133821770705127981 57446675183164014422993)
                      ·
                        rfl

theorem cell23_111877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_111877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_111877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_111877 prefixEnd_111877 := by exact prefixLift 111877
  have htrace : WordTrace (prefixWord ++ tailWord_111877) baseStart_111877 baseEnd_111877 := by
    simpa [prefixWord, tailWord_111877, baseEnd_111877] using wordTrace_append hprefix tailTrace_111877
  have hstable : (prefixWord ++ tailWord_111877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111877).length < 2 ^ (prefixWord ++ tailWord_111877).sum := by decide
  have hdescent : baseEnd_111877 < baseStart_111877 := by decide
  rcases family_descends (prefixWord ++ tailWord_111877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112000 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_112000 : Nat := 118140960795 + 112000 * 2 ^ 59
def prefixEnd_112000 : Nat := 4983230072969 + 3 ^ 40 * 112000 * 2
def baseEnd_112000 : Nat := 19169944434555677728309

theorem tailTrace_112000 : CollatzResearch.WordTrace tailWord_112000 prefixEnd_112000 19169944434555677728309 := by
  unfold tailWord_112000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042487797125301461122727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2723317062833735281496969 2042487797125301461122727)
  ·
    refine ⟨3063731695687952191684091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042487797125301461122727 3063731695687952191684091)
    ·
      refine ⟨4595597543531928287526137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063731695687952191684091 4595597543531928287526137)
      ·
        refine ⟨3446698157648946215644603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4595597543531928287526137 3446698157648946215644603)
        ·
          refine ⟨5170047236473419323466905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446698157648946215644603 5170047236473419323466905)
          ·
            refine ⟨3877535427355064492600179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170047236473419323466905 3877535427355064492600179)
            ·
              refine ⟨5816303141032596738900269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877535427355064492600179 5816303141032596738900269)
              ·
                refine ⟨2181113677887223777087601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5816303141032596738900269 2181113677887223777087601)
                ·
                  refine ⟨1635835258415417832815701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181113677887223777087601 1635835258415417832815701)
                  ·
                    refine ⟨19169944434555677728309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1635835258415417832815701 19169944434555677728309)
                    ·
                      rfl

theorem cell23_112000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_112000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112000 prefixEnd_112000 := by exact prefixLift 112000
  have htrace : WordTrace (prefixWord ++ tailWord_112000) baseStart_112000 baseEnd_112000 := by
    simpa [prefixWord, tailWord_112000, baseEnd_112000] using wordTrace_append hprefix tailTrace_112000
  have hstable : (prefixWord ++ tailWord_112000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112000).length < 2 ^ (prefixWord ++ tailWord_112000).sum := by decide
  have hdescent : baseEnd_112000 < baseStart_112000 := by decide
  rcases family_descends (prefixWord ++ tailWord_112000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112004 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_112004 : Nat := 118140960795 + 112004 * 2 ^ 59
def prefixEnd_112004 : Nat := 4983230072969 + 3 ^ 40 * 112004 * 2
def baseEnd_112004 : Nat := 19170629075428339178303

theorem tailTrace_112004 : CollatzResearch.WordTrace tailWord_112004 prefixEnd_112004 19170629075428339178303 := by
  unfold tailWord_112004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042560743118055802695533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2723414324157407736927377 2042560743118055802695533)
  ·
    refine ⟨765960278669270926010825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2042560743118055802695533 765960278669270926010825)
    ·
      refine ⟨574470209001953194508119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 765960278669270926010825 574470209001953194508119)
      ·
        refine ⟨861705313502929791762179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574470209001953194508119 861705313502929791762179)
        ·
          refine ⟨1292557970254394687643269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861705313502929791762179 1292557970254394687643269)
          ·
            refine ⟨242354619422699003933113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1292557970254394687643269 242354619422699003933113)
            ·
              refine ⟨181765964567024252949835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242354619422699003933113 181765964567024252949835)
              ·
                refine ⟨272648946850536379424753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181765964567024252949835 272648946850536379424753)
                ·
                  refine ⟨204486710137902284568565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272648946850536379424753 204486710137902284568565)
                  ·
                    refine ⟨19170629075428339178303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 204486710137902284568565 19170629075428339178303)
                    ·
                      rfl

theorem cell23_112004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_112004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112004 prefixEnd_112004 := by exact prefixLift 112004
  have htrace : WordTrace (prefixWord ++ tailWord_112004) baseStart_112004 baseEnd_112004 := by
    simpa [prefixWord, tailWord_112004, baseEnd_112004] using wordTrace_append hprefix tailTrace_112004
  have hstable : (prefixWord ++ tailWord_112004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112004).length < 2 ^ (prefixWord ++ tailWord_112004).sum := by decide
  have hdescent : baseEnd_112004 < baseStart_112004 := by decide
  rcases family_descends (prefixWord ++ tailWord_112004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112017 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_112017 : Nat := 118140960795 + 112017 * 2 ^ 59
def prefixEnd_112017 : Nat := 4983230072969 + 3 ^ 40 * 112017 * 2
def baseEnd_112017 : Nat := 19172854158264488890783

theorem tailTrace_112017 : CollatzResearch.WordTrace tailWord_112017 prefixEnd_112017 19172854158264488890783 := by
  unfold tailWord_112017
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085595635189014825614305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2723730423459343217076203 4085595635189014825614305)
  ·
    refine ⟨3064196726391761119210729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4085595635189014825614305 3064196726391761119210729)
    ·
      refine ⟨2298147544793820839408047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064196726391761119210729 2298147544793820839408047)
      ·
        refine ⟨3447221317190731259112071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298147544793820839408047 3447221317190731259112071)
        ·
          refine ⟨5170831975786096888668107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3447221317190731259112071 5170831975786096888668107)
          ·
            refine ⟨7756247963679145333002161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170831975786096888668107 7756247963679145333002161)
            ·
              refine ⟨5817185972759358999751621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7756247963679145333002161 5817185972759358999751621)
              ·
                refine ⟨1090722369892379812453429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5817185972759358999751621 1090722369892379812453429)
                ·
                  refine ⟨102255222177410607417509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090722369892379812453429 102255222177410607417509)
                  ·
                    refine ⟨19172854158264488890783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102255222177410607417509 19172854158264488890783)
                    ·
                      rfl

theorem cell23_112017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_112017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112017 prefixEnd_112017 := by exact prefixLift 112017
  have htrace : WordTrace (prefixWord ++ tailWord_112017) baseStart_112017 baseEnd_112017 := by
    simpa [prefixWord, tailWord_112017, baseEnd_112017] using wordTrace_append hprefix tailTrace_112017
  have hstable : (prefixWord ++ tailWord_112017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112017).length < 2 ^ (prefixWord ++ tailWord_112017).sum := by decide
  have hdescent : baseEnd_112017 < baseStart_112017 := by decide
  rcases family_descends (prefixWord ++ tailWord_112017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112068 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_112068 : Nat := 118140960795 + 112068 * 2 ^ 59
def prefixEnd_112068 : Nat := 4983230072969 + 3 ^ 40 * 112068 * 2
def baseEnd_112068 : Nat := 19181583329390922378205

theorem tailTrace_112068 : CollatzResearch.WordTrace tailWord_112068 prefixEnd_112068 19181583329390922378205 := by
  unfold tailWord_112068
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043727879002125267860429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2724970505336167023813905 2043727879002125267860429)
  ·
    refine ⟨766397954625796975447661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2043727879002125267860429 766397954625796975447661)
    ·
      refine ⟨287399232984673865792873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 766397954625796975447661 287399232984673865792873)
      ·
        refine ⟨215549424738505399344655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287399232984673865792873 215549424738505399344655)
        ·
          refine ⟨323324137107758099016983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215549424738505399344655 323324137107758099016983)
          ·
            refine ⟨484986205661637148525475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323324137107758099016983 484986205661637148525475)
            ·
              refine ⟨727479308492455722788213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484986205661637148525475 727479308492455722788213)
              ·
                refine ⟨68201185171167724011395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 727479308492455722788213 68201185171167724011395)
                ·
                  refine ⟨102301777756751586017093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68201185171167724011395 102301777756751586017093)
                  ·
                    refine ⟨19181583329390922378205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102301777756751586017093 19181583329390922378205)
                    ·
                      rfl

theorem cell23_112068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_112068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112068 prefixEnd_112068 := by exact prefixLift 112068
  have htrace : WordTrace (prefixWord ++ tailWord_112068) baseStart_112068 baseEnd_112068 := by
    simpa [prefixWord, tailWord_112068, baseEnd_112068] using wordTrace_append hprefix tailTrace_112068
  have hstable : (prefixWord ++ tailWord_112068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112068).length < 2 ^ (prefixWord ++ tailWord_112068).sum := by decide
  have hdescent : baseEnd_112068 < baseStart_112068 := by decide
  rcases family_descends (prefixWord ++ tailWord_112068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112101 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_112101 : Nat := 118140960795 + 112101 * 2 ^ 59
def prefixEnd_112101 : Nat := 4983230072969 + 3 ^ 40 * 112101 * 2
def baseEnd_112101 : Nat := 57561694849771138021963

theorem tailTrace_112101 : CollatzResearch.WordTrace tailWord_112101 prefixEnd_112101 57561694849771138021963 := by
  unfold tailWord_112101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088659366884697171672157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2725772911256464781114771 4088659366884697171672157)
  ·
    refine ⟨1533247262581761439377059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4088659366884697171672157 1533247262581761439377059)
    ·
      refine ⟨2299870893872642159065589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533247262581761439377059 2299870893872642159065589)
      ·
        refine ⟨215612896300560202412399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2299870893872642159065589 215612896300560202412399)
        ·
          refine ⟨323419344450840303618599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215612896300560202412399 323419344450840303618599)
          ·
            refine ⟨485129016676260455427899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323419344450840303618599 485129016676260455427899)
            ·
              refine ⟨727693525014390683141849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485129016676260455427899 727693525014390683141849)
              ·
                refine ⟨545770143760793012356387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727693525014390683141849 545770143760793012356387)
                ·
                  refine ⟨818655215641189518534581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545770143760793012356387 818655215641189518534581)
                  ·
                    refine ⟨76748926466361517362617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 818655215641189518534581 76748926466361517362617)
                    ·
                      refine ⟨57561694849771138021963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76748926466361517362617 57561694849771138021963)
                      ·
                        rfl

theorem cell23_112101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_112101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112101 prefixEnd_112101 := by exact prefixLift 112101
  have htrace : WordTrace (prefixWord ++ tailWord_112101) baseStart_112101 baseEnd_112101 := by
    simpa [prefixWord, tailWord_112101, baseEnd_112101] using wordTrace_append hprefix tailTrace_112101
  have hstable : (prefixWord ++ tailWord_112101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112101).length < 2 ^ (prefixWord ++ tailWord_112101).sum := by decide
  have hdescent : baseEnd_112101 < baseStart_112101 := by decide
  rcases family_descends (prefixWord ++ tailWord_112101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112107 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 1, 6]
def baseStart_112107 : Nat := 118140960795 + 112107 * 2 ^ 59
def prefixEnd_112107 : Nat := 4983230072969 + 3 ^ 40 * 112107 * 2
def baseEnd_112107 : Nat := 19188258577899371515645

theorem tailTrace_112107 : CollatzResearch.WordTrace tailWord_112107 prefixEnd_112107 19188258577899371515645 := by
  unfold tailWord_112107
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088878204862960196390575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2725918803241973464260383 4088878204862960196390575)
  ·
    refine ⟨6133317307294440294585863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4088878204862960196390575 6133317307294440294585863)
    ·
      refine ⟨9199975960941660441878795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6133317307294440294585863 9199975960941660441878795)
      ·
        refine ⟨13799963941412490662818193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199975960941660441878795 13799963941412490662818193)
        ·
          refine ⟨10349972956059367997113645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799963941412490662818193 10349972956059367997113645)
          ·
            refine ⟨3881239858522262998917617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10349972956059367997113645 3881239858522262998917617)
            ·
              refine ⟨2910929893891697249188213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881239858522262998917617 2910929893891697249188213)
              ·
                refine ⟨272899677552346617111395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2910929893891697249188213 272899677552346617111395)
                ·
                  refine ⟨409349516328519925667093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272899677552346617111395 409349516328519925667093)
                  ·
                    refine ⟨19188258577899371515645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 409349516328519925667093 19188258577899371515645)
                    ·
                      rfl

theorem cell23_112107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 6].length) (baseStart_112107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112107 prefixEnd_112107 := by exact prefixLift 112107
  have htrace : WordTrace (prefixWord ++ tailWord_112107) baseStart_112107 baseEnd_112107 := by
    simpa [prefixWord, tailWord_112107, baseEnd_112107] using wordTrace_append hprefix tailTrace_112107
  have hstable : (prefixWord ++ tailWord_112107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112107).length < 2 ^ (prefixWord ++ tailWord_112107).sum := by decide
  have hdescent : baseEnd_112107 < baseStart_112107 := by decide
  rcases family_descends (prefixWord ++ tailWord_112107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112124 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_112124 : Nat := 118140960795 + 112124 * 2 ^ 59
def prefixEnd_112124 : Nat := 4983230072969 + 3 ^ 40 * 112124 * 2
def baseEnd_112124 : Nat := 19191168301608182678119

theorem tailTrace_112124 : CollatzResearch.WordTrace tailWord_112124 prefixEnd_112124 19191168301608182678119 := by
  unfold tailWord_112124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044749122900686049879713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2726332163867581399839617 2044749122900686049879713)
  ·
    refine ⟨1533561842175514537409785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2044749122900686049879713 1533561842175514537409785)
    ·
      refine ⟨1150171381631635903057339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533561842175514537409785 1150171381631635903057339)
      ·
        refine ⟨1725257072447453854586009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150171381631635903057339 1725257072447453854586009)
        ·
          refine ⟨1293942804335590390939507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725257072447453854586009 1293942804335590390939507)
          ·
            refine ⟨1940914206503385586409261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293942804335590390939507 1940914206503385586409261)
            ·
              refine ⟨727842827438769594903473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1940914206503385586409261 727842827438769594903473)
              ·
                refine ⟨545882120579077196177605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727842827438769594903473 545882120579077196177605)
                ·
                  refine ⟨102352897608576974283301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545882120579077196177605 102352897608576974283301)
                  ·
                    refine ⟨19191168301608182678119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102352897608576974283301 19191168301608182678119)
                    ·
                      rfl

theorem cell23_112124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_112124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112124 prefixEnd_112124 := by exact prefixLift 112124
  have htrace : WordTrace (prefixWord ++ tailWord_112124) baseStart_112124 baseEnd_112124 := by
    simpa [prefixWord, tailWord_112124, baseEnd_112124] using wordTrace_append hprefix tailTrace_112124
  have hstable : (prefixWord ++ tailWord_112124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112124).length < 2 ^ (prefixWord ++ tailWord_112124).sum := by decide
  have hdescent : baseEnd_112124 < baseStart_112124 := by decide
  rcases family_descends (prefixWord ++ tailWord_112124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112125 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_112125 : Nat := 118140960795 + 112125 * 2 ^ 59
def prefixEnd_112125 : Nat := 4983230072969 + 3 ^ 40 * 112125 * 2
def baseEnd_112125 : Nat := 57574018385479044121853

theorem tailTrace_112125 : CollatzResearch.WordTrace tailWord_112125 prefixEnd_112125 57574018385479044121853 := by
  unfold tailWord_112125
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089534718797749270545829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2726356479198499513697219 4089534718797749270545829)
  ·
    refine ⟨766787759774577988227343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4089534718797749270545829 766787759774577988227343)
    ·
      refine ⟨1150181639661866982341015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766787759774577988227343 1150181639661866982341015)
      ·
        refine ⟨1725272459492800473511523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150181639661866982341015 1725272459492800473511523)
        ·
          refine ⟨2587908689239200710267285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725272459492800473511523 2587908689239200710267285)
          ·
            refine ⟨121308219808087533293779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2587908689239200710267285 121308219808087533293779)
            ·
              refine ⟨181962329712131299940669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121308219808087533293779 181962329712131299940669)
              ·
                refine ⟨68235873642049237477751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181962329712131299940669 68235873642049237477751)
                ·
                  refine ⟨102353810463073856216627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68235873642049237477751 102353810463073856216627)
                  ·
                    refine ⟨153530715694610784324941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102353810463073856216627 153530715694610784324941)
                    ·
                      refine ⟨57574018385479044121853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153530715694610784324941 57574018385479044121853)
                      ·
                        rfl

theorem cell23_112125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_112125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112125 prefixEnd_112125 := by exact prefixLift 112125
  have htrace : WordTrace (prefixWord ++ tailWord_112125) baseStart_112125 baseEnd_112125 := by
    simpa [prefixWord, tailWord_112125, baseEnd_112125] using wordTrace_append hprefix tailTrace_112125
  have hstable : (prefixWord ++ tailWord_112125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112125).length < 2 ^ (prefixWord ++ tailWord_112125).sum := by decide
  have hdescent : baseEnd_112125 < baseStart_112125 := by decide
  rcases family_descends (prefixWord ++ tailWord_112125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112142 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_112142 : Nat := 118140960795 + 112142 * 2 ^ 59
def prefixEnd_112142 : Nat := 4983230072969 + 3 ^ 40 * 112142 * 2
def baseEnd_112142 : Nat := 57582747556605477609275

theorem tailTrace_112142 : CollatzResearch.WordTrace tailWord_112142 prefixEnd_112142 57582747556605477609275 := by
  unfold tailWord_112142
  simp only [CollatzResearch.WordTrace]
  refine ⟨511269344967020146739335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2726769839824107449276453 511269344967020146739335)
  ·
    refine ⟨766904017450530220109003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511269344967020146739335 766904017450530220109003)
    ·
      refine ⟨1150356026175795330163505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766904017450530220109003 1150356026175795330163505)
      ·
        refine ⟨862767019631846497622629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1150356026175795330163505 862767019631846497622629)
        ·
          refine ⟨161768816180971218304243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862767019631846497622629 161768816180971218304243)
          ·
            refine ⟨242653224271456827456365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161768816180971218304243 242653224271456827456365)
            ·
              refine ⟨90994959101796310296137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242653224271456827456365 90994959101796310296137)
              ·
                refine ⟨68246219326347232722103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90994959101796310296137 68246219326347232722103)
                ·
                  refine ⟨102369328989520849083155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68246219326347232722103 102369328989520849083155)
                  ·
                    refine ⟨153553993484281273624733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102369328989520849083155 153553993484281273624733)
                    ·
                      refine ⟨57582747556605477609275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153553993484281273624733 57582747556605477609275)
                      ·
                        rfl

theorem cell23_112142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_112142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112142 prefixEnd_112142 := by exact prefixLift 112142
  have htrace : WordTrace (prefixWord ++ tailWord_112142) baseStart_112142 baseEnd_112142 := by
    simpa [prefixWord, tailWord_112142, baseEnd_112142] using wordTrace_append hprefix tailTrace_112142
  have hstable : (prefixWord ++ tailWord_112142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112142).length < 2 ^ (prefixWord ++ tailWord_112142).sum := by decide
  have hdescent : baseEnd_112142 < baseStart_112142 := by decide
  rcases family_descends (prefixWord ++ tailWord_112142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112168 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_112168 : Nat := 118140960795 + 112168 * 2 ^ 59
def prefixEnd_112168 : Nat := 4983230072969 + 3 ^ 40 * 112168 * 2
def baseEnd_112168 : Nat := 57596098053622375884155

theorem tailTrace_112168 : CollatzResearch.WordTrace tailWord_112168 prefixEnd_112168 57596098053622375884155 := by
  unfold tailWord_112168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045551528820983807180579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2727402038427978409574105 2045551528820983807180579)
  ·
    refine ⟨3068327293231475710770869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045551528820983807180579 3068327293231475710770869)
    ·
      refine ⟨287655683740450847884769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3068327293231475710770869 287655683740450847884769)
      ·
        refine ⟨215741762805338135913577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287655683740450847884769 215741762805338135913577)
        ·
          refine ⟨161806322104003601935183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215741762805338135913577 161806322104003601935183)
          ·
            refine ⟨242709483156005402902775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161806322104003601935183 242709483156005402902775)
            ·
              refine ⟨364064224734008104354163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242709483156005402902775 364064224734008104354163)
              ·
                refine ⟨546096337101012156531245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364064224734008104354163 546096337101012156531245)
                ·
                  refine ⟨204786126412879558699217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546096337101012156531245 204786126412879558699217)
                  ·
                    refine ⟨153589594809659669024413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204786126412879558699217 153589594809659669024413)
                    ·
                      refine ⟨57596098053622375884155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153589594809659669024413 57596098053622375884155)
                      ·
                        rfl

theorem cell23_112168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_112168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112168 prefixEnd_112168 := by exact prefixLift 112168
  have htrace : WordTrace (prefixWord ++ tailWord_112168) baseStart_112168 baseEnd_112168 := by
    simpa [prefixWord, tailWord_112168, baseEnd_112168] using wordTrace_append hprefix tailTrace_112168
  have hstable : (prefixWord ++ tailWord_112168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112168).length < 2 ^ (prefixWord ++ tailWord_112168).sum := by decide
  have hdescent : baseEnd_112168 < baseStart_112168 := by decide
  rcases family_descends (prefixWord ++ tailWord_112168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112181 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_112181 : Nat := 118140960795 + 112181 * 2 ^ 59
def prefixEnd_112181 : Nat := 4983230072969 + 3 ^ 40 * 112181 * 2
def baseEnd_112181 : Nat := 57602773302130825021595

theorem tailTrace_112181 : CollatzResearch.WordTrace tailWord_112181 prefixEnd_112181 57602773302130825021595 := by
  unfold tailWord_112181
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091577206594870834584397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2727718137729913889722931 4091577206594870834584397)
  ·
    refine ⟨1534341452473076562969149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4091577206594870834584397 1534341452473076562969149)
    ·
      refine ⟨575378044677403711113431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1534341452473076562969149 575378044677403711113431)
      ·
        refine ⟨863067067016105566670147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575378044677403711113431 863067067016105566670147)
        ·
          refine ⟨1294600600524158350005221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863067067016105566670147 1294600600524158350005221)
          ·
            refine ⟨242737612598279690625979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1294600600524158350005221 242737612598279690625979)
            ·
              refine ⟨364106418897419535938969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242737612598279690625979 364106418897419535938969)
              ·
                refine ⟨273079814173064651954227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364106418897419535938969 273079814173064651954227)
                ·
                  refine ⟨409619721259596977931341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273079814173064651954227 409619721259596977931341)
                  ·
                    refine ⟨153607395472348866724253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409619721259596977931341 153607395472348866724253)
                    ·
                      refine ⟨57602773302130825021595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153607395472348866724253 57602773302130825021595)
                      ·
                        rfl

theorem cell23_112181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_112181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112181 prefixEnd_112181 := by exact prefixLift 112181
  have htrace : WordTrace (prefixWord ++ tailWord_112181) baseStart_112181 baseEnd_112181 := by
    simpa [prefixWord, tailWord_112181, baseEnd_112181] using wordTrace_append hprefix tailTrace_112181
  have hstable : (prefixWord ++ tailWord_112181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112181).length < 2 ^ (prefixWord ++ tailWord_112181).sum := by decide
  have hdescent : baseEnd_112181 < baseStart_112181 := by decide
  rcases family_descends (prefixWord ++ tailWord_112181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112199 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_112199 : Nat := 118140960795 + 112199 * 2 ^ 59
def prefixEnd_112199 : Nat := 4983230072969 + 3 ^ 40 * 112199 * 2
def baseEnd_112199 : Nat := 57612015953911754596513

theorem tailTrace_112199 : CollatzResearch.WordTrace tailWord_112199 prefixEnd_112199 57612015953911754596513 := by
  unfold tailWord_112199
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092233720529659908739651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2728155813686439939159767 4092233720529659908739651)
  ·
    refine ⟨6138350580794489863109477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4092233720529659908739651 6138350580794489863109477)
    ·
      refine ⟨1150940733898966849333027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6138350580794489863109477 1150940733898966849333027)
      ·
        refine ⟨1726411100848450273999541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150940733898966849333027 1726411100848450273999541)
        ·
          refine ⟨161851040704542213187457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1726411100848450273999541 161851040704542213187457)
          ·
            refine ⟨121388280528406659890593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161851040704542213187457 121388280528406659890593)
            ·
              refine ⟨91041210396304994917945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121388280528406659890593 91041210396304994917945)
              ·
                refine ⟨68280907797228746188459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91041210396304994917945 68280907797228746188459)
                ·
                  refine ⟨102421361695843119282689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68280907797228746188459 102421361695843119282689)
                  ·
                    refine ⟨76816021271882339462017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102421361695843119282689 76816021271882339462017)
                    ·
                      refine ⟨57612015953911754596513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76816021271882339462017 57612015953911754596513)
                      ·
                        rfl

theorem cell23_112199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_112199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112199 prefixEnd_112199 := by exact prefixLift 112199
  have htrace : WordTrace (prefixWord ++ tailWord_112199) baseStart_112199 baseEnd_112199 := by
    simpa [prefixWord, tailWord_112199, baseEnd_112199] using wordTrace_append hprefix tailTrace_112199
  have hstable : (prefixWord ++ tailWord_112199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112199).length < 2 ^ (prefixWord ++ tailWord_112199).sum := by decide
  have hdescent : baseEnd_112199 < baseStart_112199 := by decide
  rcases family_descends (prefixWord ++ tailWord_112199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112204 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_112204 : Nat := 118140960795 + 112204 * 2 ^ 59
def prefixEnd_112204 : Nat := 4983230072969 + 3 ^ 40 * 112204 * 2
def baseEnd_112204 : Nat := 57614583357184235033989

theorem tailTrace_112204 : CollatzResearch.WordTrace tailWord_112204 prefixEnd_112204 57614583357184235033989 := by
  unfold tailWord_112204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046208042755772881335833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2728277390341030508447777 2046208042755772881335833)
  ·
    refine ⟨1534656032066829661001875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2046208042755772881335833 1534656032066829661001875)
    ·
      refine ⟨2301984048100244491502813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534656032066829661001875 2301984048100244491502813)
      ·
        refine ⟨863244018037591684313555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2301984048100244491502813 863244018037591684313555)
        ·
          refine ⟨1294866027056387526470333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863244018037591684313555 1294866027056387526470333)
          ·
            refine ⟨485574760146145322426375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1294866027056387526470333 485574760146145322426375)
            ·
              refine ⟨728362140219217983639563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485574760146145322426375 728362140219217983639563)
              ·
                refine ⟨1092543210328826975459345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728362140219217983639563 1092543210328826975459345)
                ·
                  refine ⟨819407407746620231594509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092543210328826975459345 819407407746620231594509)
                  ·
                    refine ⟨307277777904982586847941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819407407746620231594509 307277777904982586847941)
                    ·
                      refine ⟨57614583357184235033989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 307277777904982586847941 57614583357184235033989)
                      ·
                        rfl

theorem cell23_112204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_112204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112204 prefixEnd_112204 := by exact prefixLift 112204
  have htrace : WordTrace (prefixWord ++ tailWord_112204) baseStart_112204 baseEnd_112204 := by
    simpa [prefixWord, tailWord_112204, baseEnd_112204] using wordTrace_append hprefix tailTrace_112204
  have hstable : (prefixWord ++ tailWord_112204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112204).length < 2 ^ (prefixWord ++ tailWord_112204).sum := by decide
  have hdescent : baseEnd_112204 < baseStart_112204 := by decide
  rcases family_descends (prefixWord ++ tailWord_112204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112224 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_112224 : Nat := 118140960795 + 112224 * 2 ^ 59
def prefixEnd_112224 : Nat := 4983230072969 + 3 ^ 40 * 112224 * 2
def baseEnd_112224 : Nat := 57624852970274156783897

theorem tailTrace_112224 : CollatzResearch.WordTrace tailWord_112224 prefixEnd_112224 57624852970274156783897 := by
  unfold tailWord_112224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046572772719544589199863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2728763696959392785599817 2046572772719544589199863)
  ·
    refine ⟨3069859159079316883799795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046572772719544589199863 3069859159079316883799795)
    ·
      refine ⟨4604788738618975325699693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069859159079316883799795 4604788738618975325699693)
      ·
        refine ⟨1726795776982115747137385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4604788738618975325699693 1726795776982115747137385)
        ·
          refine ⟨1295096832736586810353039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726795776982115747137385 1295096832736586810353039)
          ·
            refine ⟨1942645249104880215529559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295096832736586810353039 1942645249104880215529559)
            ·
              refine ⟨2913967873657320323294339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942645249104880215529559 2913967873657320323294339)
              ·
                refine ⟨4370951810485980484941509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913967873657320323294339 4370951810485980484941509)
                ·
                  refine ⟨819553464466121340926533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4370951810485980484941509 819553464466121340926533)
                  ·
                    refine ⟨153666274587397751423725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819553464466121340926533 153666274587397751423725)
                    ·
                      refine ⟨57624852970274156783897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153666274587397751423725 57624852970274156783897)
                      ·
                        rfl

theorem cell23_112224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_112224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112224 prefixEnd_112224 := by exact prefixLift 112224
  have htrace : WordTrace (prefixWord ++ tailWord_112224) baseStart_112224 baseEnd_112224 := by
    simpa [prefixWord, tailWord_112224, baseEnd_112224] using wordTrace_append hprefix tailTrace_112224
  have hstable : (prefixWord ++ tailWord_112224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112224).length < 2 ^ (prefixWord ++ tailWord_112224).sum := by decide
  have hdescent : baseEnd_112224 < baseStart_112224 := by decide
  rcases family_descends (prefixWord ++ tailWord_112224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112242 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_112242 : Nat := 118140960795 + 112242 * 2 ^ 59
def prefixEnd_112242 : Nat := 4983230072969 + 3 ^ 40 * 112242 * 2
def baseEnd_112242 : Nat := 57634095622055086358815

theorem tailTrace_112242 : CollatzResearch.WordTrace tailWord_112242 prefixEnd_112242 57634095622055086358815 := by
  unfold tailWord_112242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023450514843469563138745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2729201372915918835036653 1023450514843469563138745)
  ·
    refine ⟨767587886132602172354059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1023450514843469563138745 767587886132602172354059)
    ·
      refine ⟨1151381829198903258531089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767587886132602172354059 1151381829198903258531089)
      ·
        refine ⟨863536371899177443898317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151381829198903258531089 863536371899177443898317)
        ·
          refine ⟨323826139462191541461869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 863536371899177443898317 323826139462191541461869)
          ·
            refine ⟨121434802298321828048201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323826139462191541461869 121434802298321828048201)
            ·
              refine ⟨91076101723741371036151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121434802298321828048201 91076101723741371036151)
              ·
                refine ⟨136614152585612056554227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91076101723741371036151 136614152585612056554227)
                ·
                  refine ⟨204921228878418084831341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136614152585612056554227 204921228878418084831341)
                  ·
                    refine ⟨76845460829406781811753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204921228878418084831341 76845460829406781811753)
                    ·
                      refine ⟨57634095622055086358815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76845460829406781811753 57634095622055086358815)
                      ·
                        rfl

theorem cell23_112242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_112242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112242 prefixEnd_112242 := by exact prefixLift 112242
  have htrace : WordTrace (prefixWord ++ tailWord_112242) baseStart_112242 baseEnd_112242 := by
    simpa [prefixWord, tailWord_112242, baseEnd_112242] using wordTrace_append hprefix tailTrace_112242
  have hstable : (prefixWord ++ tailWord_112242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112242).length < 2 ^ (prefixWord ++ tailWord_112242).sum := by decide
  have hdescent : baseEnd_112242 < baseStart_112242 := by decide
  rcases family_descends (prefixWord ++ tailWord_112242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
