import V185TrunkScan20Chunk059

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_365561 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_365561 : Nat := 118140960795 + 365561 * 2 ^ 59
def prefixEnd_365561 : Nat := 4983230072969 + 3 ^ 40 * 365561 * 2
def baseEnd_365561 : Nat := 166852001367421755205619

theorem tailTrace_365561 : CollatzResearch.WordTrace tailWord_365561 prefixEnd_365561 166852001367421755205619 := by
  unfold tailWord_365561
  simp only [CollatzResearch.WordTrace]
  refine ⟨13333105028642404693376537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8888736685761603128917691 13333105028642404693376537)
  ·
    refine ⟨9999828771481803520032403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13333105028642404693376537 9999828771481803520032403)
    ·
      refine ⟨14999743157222705280048605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9999828771481803520032403 14999743157222705280048605)
      ·
        refine ⟨5624903683958514480018227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14999743157222705280048605 5624903683958514480018227)
        ·
          refine ⟨8437355525937771720027341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624903683958514480018227 8437355525937771720027341)
          ·
            refine ⟨3164008322226664395010253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8437355525937771720027341 3164008322226664395010253)
            ·
              refine ⟨1186503120834999148128845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3164008322226664395010253 1186503120834999148128845)
              ·
                refine ⟨444938670313124680548317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1186503120834999148128845 444938670313124680548317)
                ·
                  refine ⟨166852001367421755205619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444938670313124680548317 166852001367421755205619)
                  ·
                    rfl

theorem cell20_365561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_365561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365561 prefixEnd_365561 := by exact prefixLift 365561
  have htrace : WordTrace (prefixWord ++ tailWord_365561) baseStart_365561 baseEnd_365561 := by
    simpa [prefixWord, tailWord_365561, baseEnd_365561] using wordTrace_append hprefix tailTrace_365561
  have hstable : (prefixWord ++ tailWord_365561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365561).length < 2 ^ (prefixWord ++ tailWord_365561).sum := by decide
  have hdescent : baseEnd_365561 < baseStart_365561 := by decide
  rcases family_descends (prefixWord ++ tailWord_365561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365575 : List Nat := [1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_365575 : Nat := 118140960795 + 365575 * 2 ^ 59
def prefixEnd_365575 : Nat := 4983230072969 + 3 ^ 40 * 365575 * 2
def baseEnd_365575 : Nat := 55619463782966642912965

theorem tailTrace_365575 : CollatzResearch.WordTrace tailWord_365575 prefixEnd_365575 55619463782966642912965 := by
  unfold tailWord_365575
  simp only [CollatzResearch.WordTrace]
  refine ⟨13333615650591685084386179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8889077100394456722924119 13333615650591685084386179)
  ·
    refine ⟨20000423475887527626579269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13333615650591685084386179 20000423475887527626579269)
    ·
      refine ⟨3750079401728911429983613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20000423475887527626579269 3750079401728911429983613)
      ·
        refine ⟨1406279775648341786243855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3750079401728911429983613 1406279775648341786243855)
        ·
          refine ⟨2109419663472512679365783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406279775648341786243855 2109419663472512679365783)
          ·
            refine ⟨3164129495208769019048675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109419663472512679365783 3164129495208769019048675)
            ·
              refine ⟨4746194242813153528573013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164129495208769019048675 4746194242813153528573013)
              ·
                refine ⟨55619463782966642912965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4746194242813153528573013 55619463782966642912965)
                ·
                  rfl

theorem cell20_365575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_365575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365575 prefixEnd_365575 := by exact prefixLift 365575
  have htrace : WordTrace (prefixWord ++ tailWord_365575) baseStart_365575 baseEnd_365575 := by
    simpa [prefixWord, tailWord_365575, baseEnd_365575] using wordTrace_append hprefix tailTrace_365575
  have hstable : (prefixWord ++ tailWord_365575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365575).length < 2 ^ (prefixWord ++ tailWord_365575).sum := by decide
  have hdescent : baseEnd_365575 < baseStart_365575 := by decide
  rcases family_descends (prefixWord ++ tailWord_365575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365599 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_365599 : Nat := 118140960795 + 365599 * 2 ^ 59
def prefixEnd_365599 : Nat := 4983230072969 + 3 ^ 40 * 365599 * 2
def baseEnd_365599 : Nat := 166869345602862511938797

theorem tailTrace_365599 : CollatzResearch.WordTrace tailWord_365599 prefixEnd_365599 166869345602862511938797 := by
  unfold tailWord_365599
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334491002504737183259851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8889660668336491455506567 13334491002504737183259851)
  ·
    refine ⟨20001736503757105774889777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13334491002504737183259851 20001736503757105774889777)
    ·
      refine ⟨15001302377817829331167333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20001736503757105774889777 15001302377817829331167333)
      ·
        refine ⟨2812744195840842999593875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15001302377817829331167333 2812744195840842999593875)
        ·
          refine ⟨4219116293761264499390813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812744195840842999593875 4219116293761264499390813)
          ·
            refine ⟨1582168610160474187271555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4219116293761264499390813 1582168610160474187271555)
            ·
              refine ⟨2373252915240711280907333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582168610160474187271555 2373252915240711280907333)
              ·
                refine ⟨444984921607633365170125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2373252915240711280907333 444984921607633365170125)
                ·
                  refine ⟨166869345602862511938797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444984921607633365170125 166869345602862511938797)
                  ·
                    rfl

theorem cell20_365599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_365599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365599 prefixEnd_365599 := by exact prefixLift 365599
  have htrace : WordTrace (prefixWord ++ tailWord_365599) baseStart_365599 baseEnd_365599 := by
    simpa [prefixWord, tailWord_365599, baseEnd_365599] using wordTrace_append hprefix tailTrace_365599
  have hstable : (prefixWord ++ tailWord_365599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365599).length < 2 ^ (prefixWord ++ tailWord_365599).sum := by decide
  have hdescent : baseEnd_365599 < baseStart_365599 := by decide
  rcases family_descends (prefixWord ++ tailWord_365599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365602 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_365602 : Nat := 118140960795 + 365602 * 2 ^ 59
def prefixEnd_365602 : Nat := 4983230072969 + 3 ^ 40 * 365602 * 2
def baseEnd_365602 : Nat := 166870714884607834838785

theorem tailTrace_365602 : CollatzResearch.WordTrace tailWord_365602 prefixEnd_365602 166870714884607834838785 := by
  unfold tailWord_365602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333650105373467173904765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8889733614329245797079373 3333650105373467173904765)
  ·
    refine ⟨1250118789515050190214287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3333650105373467173904765 1250118789515050190214287)
    ·
      refine ⟨1875178184272575285321431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250118789515050190214287 1875178184272575285321431)
      ·
        refine ⟨2812767276408862927982147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875178184272575285321431 2812767276408862927982147)
        ·
          refine ⟨4219150914613294391973221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812767276408862927982147 4219150914613294391973221)
          ·
            refine ⟨791090796489992698494979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4219150914613294391973221 791090796489992698494979)
            ·
              refine ⟨1186636194734989047742469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791090796489992698494979 1186636194734989047742469)
              ·
                refine ⟨222494286512810446451713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1186636194734989047742469 222494286512810446451713)
                ·
                  refine ⟨166870714884607834838785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222494286512810446451713 166870714884607834838785)
                  ·
                    rfl

theorem cell20_365602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_365602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365602 prefixEnd_365602 := by exact prefixLift 365602
  have htrace : WordTrace (prefixWord ++ tailWord_365602) baseStart_365602 baseEnd_365602 := by
    simpa [prefixWord, tailWord_365602, baseEnd_365602] using wordTrace_append hprefix tailTrace_365602
  have hstable : (prefixWord ++ tailWord_365602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365602).length < 2 ^ (prefixWord ++ tailWord_365602).sum := by decide
  have hdescent : baseEnd_365602 < baseStart_365602 := by decide
  rcases family_descends (prefixWord ++ tailWord_365602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365682 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_365682 : Nat := 118140960795 + 365682 * 2 ^ 59
def prefixEnd_365682 : Nat := 4983230072969 + 3 ^ 40 * 365682 * 2
def baseEnd_365682 : Nat := 166907229064483112171791

theorem tailTrace_365682 : CollatzResearch.WordTrace tailWord_365682 prefixEnd_365682 166907229064483112171791 := by
  unfold tailWord_365682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334379565301010589632825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8891678840802694905687533 3334379565301010589632825)
  ·
    refine ⟨2500784673975757942224619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3334379565301010589632825 2500784673975757942224619)
    ·
      refine ⟨3751177010963636913336929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500784673975757942224619 3751177010963636913336929)
      ·
        refine ⟨2813382758222727685002697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3751177010963636913336929 2813382758222727685002697)
        ·
          refine ⟨2110037068667045763752023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2813382758222727685002697 2110037068667045763752023)
          ·
            refine ⟨3165055603000568645628035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110037068667045763752023 3165055603000568645628035)
            ·
              refine ⟨4747583404500852968442053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165055603000568645628035 4747583404500852968442053)
              ·
                refine ⟨890171888343909931582885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4747583404500852968442053 890171888343909931582885)
                ·
                  refine ⟨166907229064483112171791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890171888343909931582885 166907229064483112171791)
                  ·
                    rfl

theorem cell20_365682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_365682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365682 prefixEnd_365682 := by exact prefixLift 365682
  have htrace : WordTrace (prefixWord ++ tailWord_365682) baseStart_365682 baseEnd_365682 := by
    simpa [prefixWord, tailWord_365682, baseEnd_365682] using wordTrace_append hprefix tailTrace_365682
  have hstable : (prefixWord ++ tailWord_365682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365682).length < 2 ^ (prefixWord ++ tailWord_365682).sum := by decide
  have hdescent : baseEnd_365682 < baseStart_365682 := by decide
  rcases family_descends (prefixWord ++ tailWord_365682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365685 : List Nat := [1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_365685 : Nat := 118140960795 + 365685 * 2 ^ 59
def prefixEnd_365685 : Nat := 4983230072969 + 3 ^ 40 * 365685 * 2
def baseEnd_365685 : Nat := 55636199448742811690593

theorem tailTrace_365685 : CollatzResearch.WordTrace tailWord_365685 prefixEnd_365685 55636199448742811690593 := by
  unfold tailWord_365685
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337627680193173870890509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8891751786795449247260339 13337627680193173870890509)
  ·
    refine ⟨5001610380072440201583941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13337627680193173870890509 5001610380072440201583941)
    ·
      refine ⟨937801946263582537796989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5001610380072440201583941 937801946263582537796989)
      ·
        refine ⟨351675729848843451673871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 937801946263582537796989 351675729848843451673871)
        ·
          refine ⟨527513594773265177510807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351675729848843451673871 527513594773265177510807)
          ·
            refine ⟨791270392159897766266211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527513594773265177510807 791270392159897766266211)
            ·
              refine ⟨1186905588239846649399317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791270392159897766266211 1186905588239846649399317)
              ·
                refine ⟨55636199448742811690593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1186905588239846649399317 55636199448742811690593)
                ·
                  rfl

theorem cell20_365685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_365685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365685 prefixEnd_365685 := by exact prefixLift 365685
  have htrace : WordTrace (prefixWord ++ tailWord_365685) baseStart_365685 baseEnd_365685 := by
    simpa [prefixWord, tailWord_365685, baseEnd_365685] using wordTrace_append hprefix tailTrace_365685
  have hstable : (prefixWord ++ tailWord_365685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365685).length < 2 ^ (prefixWord ++ tailWord_365685).sum := by decide
  have hdescent : baseEnd_365685 < baseStart_365685 := by decide
  rcases family_descends (prefixWord ++ tailWord_365685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365696 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_365696 : Nat := 118140960795 + 365696 * 2 ^ 59
def prefixEnd_365696 : Nat := 4983230072969 + 3 ^ 40 * 365696 * 2
def baseEnd_365696 : Nat := 166913619045961285705067

theorem tailTrace_365696 : CollatzResearch.WordTrace tailWord_365696 prefixEnd_365696 166913619045961285705067 := by
  unfold tailWord_365696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669014441576661374770471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8892019255435548499693961 6669014441576661374770471)
  ·
    refine ⟨10003521662364992062155707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6669014441576661374770471 10003521662364992062155707)
    ·
      refine ⟨15005282493547488093233561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003521662364992062155707 15005282493547488093233561)
      ·
        refine ⟨11253961870160616069925171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15005282493547488093233561 11253961870160616069925171)
        ·
          refine ⟨16880942805240924104887757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11253961870160616069925171 16880942805240924104887757)
          ·
            refine ⟨6330353551965346539332909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16880942805240924104887757 6330353551965346539332909)
            ·
              refine ⟨2373882581987004952249841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6330353551965346539332909 2373882581987004952249841)
              ·
                refine ⟨1780411936490253714187381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373882581987004952249841 1780411936490253714187381)
                ·
                  refine ⟨166913619045961285705067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1780411936490253714187381 166913619045961285705067)
                  ·
                    rfl

theorem cell20_365696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_365696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365696 prefixEnd_365696 := by exact prefixLift 365696
  have htrace : WordTrace (prefixWord ++ tailWord_365696) baseStart_365696 baseEnd_365696 := by
    simpa [prefixWord, tailWord_365696, baseEnd_365696] using wordTrace_append hprefix tailTrace_365696
  have hstable : (prefixWord ++ tailWord_365696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365696).length < 2 ^ (prefixWord ++ tailWord_365696).sum := by decide
  have hdescent : baseEnd_365696 < baseStart_365696 := by decide
  rcases family_descends (prefixWord ++ tailWord_365696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365726 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_365726 : Nat := 118140960795 + 365726 * 2 ^ 59
def prefixEnd_365726 : Nat := 4983230072969 + 3 ^ 40 * 365726 * 2
def baseEnd_365726 : Nat := 166927311863414514704945

theorem tailTrace_365726 : CollatzResearch.WordTrace tailWord_365726 prefixEnd_365726 166927311863414514704945 := by
  unfold tailWord_365726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667390384130579734141629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8892748715363091915422021 1667390384130579734141629)
  ·
    refine ⟨625271394048967400303111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1667390384130579734141629 625271394048967400303111)
    ·
      refine ⟨937907091073451100454667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625271394048967400303111 937907091073451100454667)
      ·
        refine ⟨1406860636610176650682001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937907091073451100454667 1406860636610176650682001)
        ·
          refine ⟨1055145477457632488011501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406860636610176650682001 1055145477457632488011501)
          ·
            refine ⟨395679554046612183004313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1055145477457632488011501 395679554046612183004313)
            ·
              refine ⟨296759665534959137253235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395679554046612183004313 296759665534959137253235)
              ·
                refine ⟨445139498302438705879853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296759665534959137253235 445139498302438705879853)
                ·
                  refine ⟨166927311863414514704945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445139498302438705879853 166927311863414514704945)
                  ·
                    rfl

theorem cell20_365726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_365726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365726 prefixEnd_365726 := by exact prefixLift 365726
  have htrace : WordTrace (prefixWord ++ tailWord_365726) baseStart_365726 baseEnd_365726 := by
    simpa [prefixWord, tailWord_365726, baseEnd_365726] using wordTrace_append hprefix tailTrace_365726
  have hstable : (prefixWord ++ tailWord_365726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365726).length < 2 ^ (prefixWord ++ tailWord_365726).sum := by decide
  have hdescent : baseEnd_365726 < baseStart_365726 := by decide
  rcases family_descends (prefixWord ++ tailWord_365726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365799 : List Nat := [1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_365799 : Nat := 118140960795 + 365799 * 2 ^ 59
def prefixEnd_365799 : Nat := 4983230072969 + 3 ^ 40 * 365799 * 2
def baseEnd_365799 : Nat := 55653543684183568423771

theorem tailTrace_365799 : CollatzResearch.WordTrace tailWord_365799 prefixEnd_365799 55653543684183568423771 := by
  unfold tailWord_365799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341785601780171340540451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8894523734520114227026967 13341785601780171340540451)
  ·
    refine ⟨20012678402670257010810677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13341785601780171340540451 20012678402670257010810677)
    ·
      refine ⟨1876188600250336594763501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20012678402670257010810677 1876188600250336594763501)
      ·
        refine ⟨703570725093876223036313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1876188600250336594763501 703570725093876223036313)
        ·
          refine ⟨527678043820407167277235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 703570725093876223036313 527678043820407167277235)
          ·
            refine ⟨791517065730610750915853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527678043820407167277235 791517065730610750915853)
            ·
              refine ⟨296818899648979031593445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 791517065730610750915853 296818899648979031593445)
              ·
                refine ⟨55653543684183568423771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296818899648979031593445 55653543684183568423771)
                ·
                  rfl

theorem cell20_365799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_365799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365799 prefixEnd_365799 := by exact prefixLift 365799
  have htrace : WordTrace (prefixWord ++ tailWord_365799) baseStart_365799 baseEnd_365799 := by
    simpa [prefixWord, tailWord_365799, baseEnd_365799] using wordTrace_append hprefix tailTrace_365799
  have hstable : (prefixWord ++ tailWord_365799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365799).length < 2 ^ (prefixWord ++ tailWord_365799).sum := by decide
  have hdescent : baseEnd_365799 < baseStart_365799 := by decide
  rcases family_descends (prefixWord ++ tailWord_365799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365817 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_365817 : Nat := 118140960795 + 365817 * 2 ^ 59
def prefixEnd_365817 : Nat := 4983230072969 + 3 ^ 40 * 365817 * 2
def baseEnd_365817 : Nat := 166968846743022642671239

theorem tailTrace_365817 : CollatzResearch.WordTrace tailWord_365817 prefixEnd_365817 166968846743022642671239 := by
  unfold tailWord_365817
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342442115714960414695705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8894961410476640276463803 13342442115714960414695705)
  ·
    refine ⟨10006831586786220311021779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13342442115714960414695705 10006831586786220311021779)
    ·
      refine ⟨15010247380179330466532669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006831586786220311021779 15010247380179330466532669)
      ·
        refine ⟨5628842767567248924949751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15010247380179330466532669 5628842767567248924949751)
        ·
          refine ⟨8443264151350873387424627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628842767567248924949751 8443264151350873387424627)
          ·
            refine ⟨12664896227026310081136941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443264151350873387424627 12664896227026310081136941)
            ·
              refine ⟨4749336085134866280426353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12664896227026310081136941 4749336085134866280426353)
              ·
                refine ⟨3562002063851149710319765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749336085134866280426353 3562002063851149710319765)
                ·
                  refine ⟨166968846743022642671239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3562002063851149710319765 166968846743022642671239)
                  ·
                    rfl

theorem cell20_365817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_365817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365817 prefixEnd_365817 := by exact prefixLift 365817
  have htrace : WordTrace (prefixWord ++ tailWord_365817) baseStart_365817 baseEnd_365817 := by
    simpa [prefixWord, tailWord_365817, baseEnd_365817] using wordTrace_append hprefix tailTrace_365817
  have hstable : (prefixWord ++ tailWord_365817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365817).length < 2 ^ (prefixWord ++ tailWord_365817).sum := by decide
  have hdescent : baseEnd_365817 < baseStart_365817 := by decide
  rcases family_descends (prefixWord ++ tailWord_365817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365827 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_365827 : Nat := 118140960795 + 365827 * 2 ^ 59
def prefixEnd_365827 : Nat := 4983230072969 + 3 ^ 40 * 365827 * 2
def baseEnd_365827 : Nat := 166973411015507052337865

theorem tailTrace_365827 : CollatzResearch.WordTrace tailWord_365827 prefixEnd_365827 166973411015507052337865 := by
  unfold tailWord_365827
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342806845678732122559735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895204563785821415039823 13342806845678732122559735)
  ·
    refine ⟨20014210268518098183839603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13342806845678732122559735 20014210268518098183839603)
    ·
      refine ⟨30021315402777147275759405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20014210268518098183839603 30021315402777147275759405)
      ·
        refine ⟨11257993276041430228409777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30021315402777147275759405 11257993276041430228409777)
        ·
          refine ⟨8443494957031072671307333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11257993276041430228409777 8443494957031072671307333)
          ·
            refine ⟨1583155304443326125870125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8443494957031072671307333 1583155304443326125870125)
            ·
              refine ⟨593683239166247297201297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1583155304443326125870125 593683239166247297201297)
              ·
                refine ⟨445262429374685472900973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593683239166247297201297 445262429374685472900973)
                ·
                  refine ⟨166973411015507052337865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445262429374685472900973 166973411015507052337865)
                  ·
                    rfl

theorem cell20_365827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_365827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365827 prefixEnd_365827 := by exact prefixLift 365827
  have htrace : WordTrace (prefixWord ++ tailWord_365827) baseStart_365827 baseEnd_365827 := by
    simpa [prefixWord, tailWord_365827, baseEnd_365827] using wordTrace_append hprefix tailTrace_365827
  have hstable : (prefixWord ++ tailWord_365827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365827).length < 2 ^ (prefixWord ++ tailWord_365827).sum := by decide
  have hdescent : baseEnd_365827 < baseStart_365827 := by decide
  rcases family_descends (prefixWord ++ tailWord_365827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365858 : List Nat := [3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_365858 : Nat := 118140960795 + 365858 * 2 ^ 59
def prefixEnd_365858 : Nat := 4983230072969 + 3 ^ 40 * 365858 * 2
def baseEnd_365858 : Nat := 55662520086736240768135

theorem tailTrace_365858 : CollatzResearch.WordTrace tailWord_365858 prefixEnd_365858 55662520086736240768135 := by
  unfold tailWord_365858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335984377141606104234557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8895958339044282944625485 3335984377141606104234557)
  ·
    refine ⟨1250994141428102289087959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3335984377141606104234557 1250994141428102289087959)
    ·
      refine ⟨1876491212142153433631939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250994141428102289087959 1876491212142153433631939)
      ·
        refine ⟨2814736818213230150447909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876491212142153433631939 2814736818213230150447909)
        ·
          refine ⟨527763153414980653208983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2814736818213230150447909 527763153414980653208983)
          ·
            refine ⟨791644730122470979813475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527763153414980653208983 791644730122470979813475)
            ·
              refine ⟨1187467095183706469720213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791644730122470979813475 1187467095183706469720213)
              ·
                refine ⟨55662520086736240768135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1187467095183706469720213 55662520086736240768135)
                ·
                  rfl

theorem cell20_365858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_365858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365858 prefixEnd_365858 := by exact prefixLift 365858
  have htrace : WordTrace (prefixWord ++ tailWord_365858) baseStart_365858 baseEnd_365858 := by
    simpa [prefixWord, tailWord_365858, baseEnd_365858] using wordTrace_append hprefix tailTrace_365858
  have hstable : (prefixWord ++ tailWord_365858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365858).length < 2 ^ (prefixWord ++ tailWord_365858).sum := by decide
  have hdescent : baseEnd_365858 < baseStart_365858 := by decide
  rcases family_descends (prefixWord ++ tailWord_365858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365885 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 4]
def baseStart_365885 : Nat := 118140960795 + 365885 * 2 ^ 59
def prefixEnd_365885 : Nat := 4983230072969 + 3 ^ 40 * 365885 * 2
def baseEnd_365885 : Nat := 166999883795916628404295

theorem tailTrace_365885 : CollatzResearch.WordTrace tailWord_365885 prefixEnd_365885 166999883795916628404295 := by
  unfold tailWord_365885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344922279468608028171109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8896614852979072018780739 13344922279468608028171109)
  ·
    refine ⟨2502172927400364005282083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13344922279468608028171109 2502172927400364005282083)
    ·
      refine ⟨3753259391100546007923125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502172927400364005282083 3753259391100546007923125)
      ·
        refine ⟨351868067915676188242793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3753259391100546007923125 351868067915676188242793)
        ·
          refine ⟨263901050936757141182095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351868067915676188242793 263901050936757141182095)
          ·
            refine ⟨395851576405135711773143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263901050936757141182095 395851576405135711773143)
            ·
              refine ⟨593777364607703567659715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395851576405135711773143 593777364607703567659715)
              ·
                refine ⟨890666046911555351489573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593777364607703567659715 890666046911555351489573)
                ·
                  refine ⟨166999883795916628404295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890666046911555351489573 166999883795916628404295)
                  ·
                    rfl

theorem cell20_365885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_365885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365885 prefixEnd_365885 := by exact prefixLift 365885
  have htrace : WordTrace (prefixWord ++ tailWord_365885) baseStart_365885 baseEnd_365885 := by
    simpa [prefixWord, tailWord_365885, baseEnd_365885] using wordTrace_append hprefix tailTrace_365885
  have hstable : (prefixWord ++ tailWord_365885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365885).length < 2 ^ (prefixWord ++ tailWord_365885).sum := by decide
  have hdescent : baseEnd_365885 < baseStart_365885 := by decide
  rcases family_descends (prefixWord ++ tailWord_365885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365889 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_365889 : Nat := 118140960795 + 365889 * 2 ^ 59
def prefixEnd_365889 : Nat := 4983230072969 + 3 ^ 40 * 365889 * 2
def baseEnd_365889 : Nat := 167001709504910392270945

theorem tailTrace_365889 : CollatzResearch.WordTrace tailWord_365889 prefixEnd_365889 167001709504910392270945 := by
  unfold tailWord_365889
  simp only [CollatzResearch.WordTrace]
  refine ⟨13345068171454116711316721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8896712114302744474211147 13345068171454116711316721)
  ·
    refine ⟨10008801128590587533487541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13345068171454116711316721 10008801128590587533487541)
    ·
      refine ⟨938325105805367581264457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10008801128590587533487541 938325105805367581264457)
      ·
        refine ⟨703743829354025685948343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938325105805367581264457 703743829354025685948343)
        ·
          refine ⟨1055615744031038528922515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703743829354025685948343 1055615744031038528922515)
          ·
            refine ⟨1583423616046557793383773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055615744031038528922515 1583423616046557793383773)
            ·
              refine ⟨593783856017459172518915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1583423616046557793383773 593783856017459172518915)
              ·
                refine ⟨890675784026188758778373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593783856017459172518915 890675784026188758778373)
                ·
                  refine ⟨167001709504910392270945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890675784026188758778373 167001709504910392270945)
                  ·
                    rfl

theorem cell20_365889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_365889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365889 prefixEnd_365889 := by exact prefixLift 365889
  have htrace : WordTrace (prefixWord ++ tailWord_365889) baseStart_365889 baseEnd_365889 := by
    simpa [prefixWord, tailWord_365889, baseEnd_365889] using wordTrace_append hprefix tailTrace_365889
  have hstable : (prefixWord ++ tailWord_365889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365889).length < 2 ^ (prefixWord ++ tailWord_365889).sum := by decide
  have hdescent : baseEnd_365889 < baseStart_365889 := by decide
  rcases family_descends (prefixWord ++ tailWord_365889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365934 : List Nat := [4, 1, 2, 4, 1, 8]
def baseStart_365934 : Nat := 118140960795 + 365934 * 2 ^ 59
def prefixEnd_365934 : Nat := 4983230072969 + 3 ^ 40 * 365934 * 2
def baseEnd_365934 : Nat := 6186009212262601324843

theorem tailTrace_365934 : CollatzResearch.WordTrace tailWord_365934 prefixEnd_365934 6186009212262601324843 := by
  unfold tailWord_365934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668338682036386174588107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8897806304194059597803237 1668338682036386174588107)
  ·
    refine ⟨2502508023054579261882161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668338682036386174588107 2502508023054579261882161)
    ·
      refine ⟨1876881017290934446411621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2502508023054579261882161 1876881017290934446411621)
      ·
        refine ⟨351915190742050208702179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1876881017290934446411621 351915190742050208702179)
        ·
          refine ⟨527872786113075313053269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351915190742050208702179 527872786113075313053269)
          ·
            refine ⟨6186009212262601324843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 527872786113075313053269 6186009212262601324843)
            ·
              rfl

theorem cell20_365934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 8].length) (baseStart_365934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365934 prefixEnd_365934 := by exact prefixLift 365934
  have htrace : WordTrace (prefixWord ++ tailWord_365934) baseStart_365934 baseEnd_365934 := by
    simpa [prefixWord, tailWord_365934, baseEnd_365934] using wordTrace_append hprefix tailTrace_365934
  have hstable : (prefixWord ++ tailWord_365934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365934).length < 2 ^ (prefixWord ++ tailWord_365934).sum := by decide
  have hdescent : baseEnd_365934 < baseStart_365934 := by decide
  rcases family_descends (prefixWord ++ tailWord_365934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365955 : List Nat := [1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_365955 : Nat := 118140960795 + 365955 * 2 ^ 59
def prefixEnd_365955 : Nat := 4983230072969 + 3 ^ 40 * 365955 * 2
def baseEnd_365955 : Nat := 55677277901102498690225

theorem tailTrace_365955 : CollatzResearch.WordTrace tailWord_365955 prefixEnd_365955 55677277901102498690225 := by
  unfold tailWord_365955
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347475389215009983219319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8898316926143339988812879 13347475389215009983219319)
  ·
    refine ⟨20021213083822514974828979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13347475389215009983219319 20021213083822514974828979)
    ·
      refine ⟨30031819625733772462243469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20021213083822514974828979 30031819625733772462243469)
      ·
        refine ⟨11261932359650164673341301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30031819625733772462243469 11261932359650164673341301)
        ·
          refine ⟨1055806158717202938125747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11261932359650164673341301 1055806158717202938125747)
          ·
            refine ⟨1583709238075804407188621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055806158717202938125747 1583709238075804407188621)
            ·
              refine ⟨593890964278426652695733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1583709238075804407188621 593890964278426652695733)
              ·
                refine ⟨55677277901102498690225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 593890964278426652695733 55677277901102498690225)
                ·
                  rfl

theorem cell20_365955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_365955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365955 prefixEnd_365955 := by exact prefixLift 365955
  have htrace : WordTrace (prefixWord ++ tailWord_365955) baseStart_365955 baseEnd_365955 := by
    simpa [prefixWord, tailWord_365955, baseEnd_365955] using wordTrace_append hprefix tailTrace_365955
  have hstable : (prefixWord ++ tailWord_365955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365955).length < 2 ^ (prefixWord ++ tailWord_365955).sum := by decide
  have hdescent : baseEnd_365955 < baseStart_365955 := by decide
  rcases family_descends (prefixWord ++ tailWord_365955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365969 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_365969 : Nat := 118140960795 + 365969 * 2 ^ 59
def prefixEnd_365969 : Nat := 4983230072969 + 3 ^ 40 * 365969 * 2
def baseEnd_365969 : Nat := 167038223684785669603951

theorem tailTrace_365969 : CollatzResearch.WordTrace tailWord_365969 prefixEnd_365969 167038223684785669603951 := by
  unfold tailWord_365969
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347986011164290374228961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8898657340776193582819307 13347986011164290374228961)
  ·
    refine ⟨10010989508373217780671721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13347986011164290374228961 10010989508373217780671721)
    ·
      refine ⟨7508242131279913335503791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10010989508373217780671721 7508242131279913335503791)
      ·
        refine ⟨11262363196919870003255687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7508242131279913335503791 11262363196919870003255687)
        ·
          refine ⟨16893544795379805004883531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11262363196919870003255687 16893544795379805004883531)
          ·
            refine ⟨25340317193069707507325297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16893544795379805004883531 25340317193069707507325297)
            ·
              refine ⟨19005237894802280630493973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25340317193069707507325297 19005237894802280630493973)
              ·
                refine ⟨890870526318856904554405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19005237894802280630493973 890870526318856904554405)
                ·
                  refine ⟨167038223684785669603951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890870526318856904554405 167038223684785669603951)
                  ·
                    rfl

theorem cell20_365969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_365969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365969 prefixEnd_365969 := by exact prefixLift 365969
  have htrace : WordTrace (prefixWord ++ tailWord_365969) baseStart_365969 baseEnd_365969 := by
    simpa [prefixWord, tailWord_365969, baseEnd_365969] using wordTrace_append hprefix tailTrace_365969
  have hstable : (prefixWord ++ tailWord_365969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365969).length < 2 ^ (prefixWord ++ tailWord_365969).sum := by decide
  have hdescent : baseEnd_365969 < baseStart_365969 := by decide
  rcases family_descends (prefixWord ++ tailWord_365969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365992 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_365992 : Nat := 118140960795 + 365992 * 2 ^ 59
def prefixEnd_365992 : Nat := 4983230072969 + 3 ^ 40 * 365992 * 2
def baseEnd_365992 : Nat := 167048721511499811837191

theorem tailTrace_365992 : CollatzResearch.WordTrace tailWord_365992 prefixEnd_365992 167048721511499811837191 := by
  unfold tailWord_365992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674412445040482651158115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8899216593387310201544153 6674412445040482651158115)
  ·
    refine ⟨10011618667560723976737173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6674412445040482651158115 10011618667560723976737173)
    ·
      refine ⟨469294625041908936409555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10011618667560723976737173 469294625041908936409555)
      ·
        refine ⟨703941937562863404614333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469294625041908936409555 703941937562863404614333)
        ·
          refine ⟨263978226586073776730375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703941937562863404614333 263978226586073776730375)
          ·
            refine ⟨395967339879110665095563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263978226586073776730375 395967339879110665095563)
            ·
              refine ⟨593951009818665997643345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395967339879110665095563 593951009818665997643345)
              ·
                refine ⟨445463257363999498232509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593951009818665997643345 445463257363999498232509)
                ·
                  refine ⟨167048721511499811837191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445463257363999498232509 167048721511499811837191)
                  ·
                    rfl

theorem cell20_365992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_365992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365992 prefixEnd_365992 := by exact prefixLift 365992
  have htrace : WordTrace (prefixWord ++ tailWord_365992) baseStart_365992 baseEnd_365992 := by
    simpa [prefixWord, tailWord_365992, baseEnd_365992] using wordTrace_append hprefix tailTrace_365992
  have hstable : (prefixWord ++ tailWord_365992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365992).length < 2 ^ (prefixWord ++ tailWord_365992).sum := by decide
  have hdescent : baseEnd_365992 < baseStart_365992 := by decide
  rcases family_descends (prefixWord ++ tailWord_365992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366000 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_366000 : Nat := 118140960795 + 366000 * 2 ^ 59
def prefixEnd_366000 : Nat := 4983230072969 + 3 ^ 40 * 366000 * 2
def baseEnd_366000 : Nat := 167052372929487339570491

theorem tailTrace_366000 : CollatzResearch.WordTrace tailWord_366000 prefixEnd_366000 167052372929487339570491 := by
  unfold tailWord_366000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674558337025991334303727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8899411116034655112404969 6674558337025991334303727)
  ·
    refine ⟨10011837505538987001455591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6674558337025991334303727 10011837505538987001455591)
    ·
      refine ⟨15017756258308480502183387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10011837505538987001455591 15017756258308480502183387)
      ·
        refine ⟨22526634387462720753275081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15017756258308480502183387 22526634387462720753275081)
        ·
          refine ⟨16894975790597040564956311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22526634387462720753275081 16894975790597040564956311)
          ·
            refine ⟨25342463685895560847434467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16894975790597040564956311 25342463685895560847434467)
            ·
              refine ⟨38013695528843341271151701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25342463685895560847434467 38013695528843341271151701)
              ·
                refine ⟨445472994478632905521309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 38013695528843341271151701 445472994478632905521309)
                ·
                  refine ⟨167052372929487339570491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445472994478632905521309 167052372929487339570491)
                  ·
                    rfl

theorem cell20_366000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_366000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366000 prefixEnd_366000 := by exact prefixLift 366000
  have htrace : WordTrace (prefixWord ++ tailWord_366000) baseStart_366000 baseEnd_366000 := by
    simpa [prefixWord, tailWord_366000, baseEnd_366000] using wordTrace_append hprefix tailTrace_366000
  have hstable : (prefixWord ++ tailWord_366000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366000).length < 2 ^ (prefixWord ++ tailWord_366000).sum := by decide
  have hdescent : baseEnd_366000 < baseStart_366000 := by decide
  rcases family_descends (prefixWord ++ tailWord_366000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366031 : List Nat := [1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_366031 : Nat := 118140960795 + 366031 * 2 ^ 59
def prefixEnd_366031 : Nat := 4983230072969 + 3 ^ 40 * 366031 * 2
def baseEnd_366031 : Nat := 55688840724729669845677

theorem tailTrace_366031 : CollatzResearch.WordTrace tailWord_366031 prefixEnd_366031 55688840724729669845677 := by
  unfold tailWord_366031
  simp only [CollatzResearch.WordTrace]
  refine ⟨13350247336939674962985947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8900164891293116641990631 13350247336939674962985947)
  ·
    refine ⟨20025371005409512444478921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13350247336939674962985947 20025371005409512444478921)
    ·
      refine ⟨15019028254057134333359191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20025371005409512444478921 15019028254057134333359191)
      ·
        refine ⟨22528542381085701500038787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15019028254057134333359191 22528542381085701500038787)
        ·
          refine ⟨33792813571628552250058181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22528542381085701500038787 33792813571628552250058181)
          ·
            refine ⟨6336152544680353546885909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33792813571628552250058181 6336152544680353546885909)
            ·
              refine ⟨297007150531891572510277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6336152544680353546885909 297007150531891572510277)
              ·
                refine ⟨55688840724729669845677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297007150531891572510277 55688840724729669845677)
                ·
                  rfl

theorem cell20_366031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_366031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366031 prefixEnd_366031 := by exact prefixLift 366031
  have htrace : WordTrace (prefixWord ++ tailWord_366031) baseStart_366031 baseEnd_366031 := by
    simpa [prefixWord, tailWord_366031, baseEnd_366031] using wordTrace_append hprefix tailTrace_366031
  have hstable : (prefixWord ++ tailWord_366031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366031).length < 2 ^ (prefixWord ++ tailWord_366031).sum := by decide
  have hdescent : baseEnd_366031 < baseStart_366031 := by decide
  rcases family_descends (prefixWord ++ tailWord_366031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366041 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 2]
def baseStart_366041 : Nat := 118140960795 + 366041 * 2 ^ 59
def prefixEnd_366041 : Nat := 4983230072969 + 3 ^ 40 * 366041 * 2
def baseEnd_366041 : Nat := 167071086446673419203657

theorem tailTrace_366041 : CollatzResearch.WordTrace tailWord_366041 prefixEnd_366041 167071086446673419203657 := by
  unfold tailWord_366041
  simp only [CollatzResearch.WordTrace]
  refine ⟨13350612066903446670849977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8900408044602297780566651 13350612066903446670849977)
  ·
    refine ⟨10012959050177585003137483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13350612066903446670849977 10012959050177585003137483)
    ·
      refine ⟨15019438575266377504706225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10012959050177585003137483 15019438575266377504706225)
      ·
        refine ⟨11264578931449783128529669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15019438575266377504706225 11264578931449783128529669)
        ·
          refine ⟨2112108549646834336599313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11264578931449783128529669 2112108549646834336599313)
          ·
            refine ⟨1584081412235125752449485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112108549646834336599313 1584081412235125752449485)
            ·
              refine ⟨594030529588172157168557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1584081412235125752449485 594030529588172157168557)
              ·
                refine ⟨222761448595564558938209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594030529588172157168557 222761448595564558938209)
                ·
                  refine ⟨167071086446673419203657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222761448595564558938209 167071086446673419203657)
                  ·
                    rfl

theorem cell20_366041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_366041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366041 prefixEnd_366041 := by exact prefixLift 366041
  have htrace : WordTrace (prefixWord ++ tailWord_366041) baseStart_366041 baseEnd_366041 := by
    simpa [prefixWord, tailWord_366041, baseEnd_366041] using wordTrace_append hprefix tailTrace_366041
  have hstable : (prefixWord ++ tailWord_366041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366041).length < 2 ^ (prefixWord ++ tailWord_366041).sum := by decide
  have hdescent : baseEnd_366041 < baseStart_366041 := by decide
  rcases family_descends (prefixWord ++ tailWord_366041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366058 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_366058 : Nat := 118140960795 + 366058 * 2 ^ 59
def prefixEnd_366058 : Nat := 4983230072969 + 3 ^ 40 * 366058 * 2
def baseEnd_366058 : Nat := 167078845709896915636921

theorem tailTrace_366058 : CollatzResearch.WordTrace tailWord_366058 prefixEnd_366058 167078845709896915636921 := by
  unfold tailWord_366058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337808026960464643554707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8900821405227905716145885 3337808026960464643554707)
  ·
    refine ⟨5006712040440696965332061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3337808026960464643554707 5006712040440696965332061)
    ·
      refine ⟨1877517015165261361999523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5006712040440696965332061 1877517015165261361999523)
      ·
        refine ⟨2816275522747892042999285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877517015165261361999523 2816275522747892042999285)
        ·
          refine ⟨264025830257614879031183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2816275522747892042999285 264025830257614879031183)
          ·
            refine ⟨396038745386422318546775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264025830257614879031183 396038745386422318546775)
            ·
              refine ⟨594058118079633477820163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396038745386422318546775 594058118079633477820163)
              ·
                refine ⟨891087177119450216730245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594058118079633477820163 891087177119450216730245)
                ·
                  refine ⟨167078845709896915636921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891087177119450216730245 167078845709896915636921)
                  ·
                    rfl

theorem cell20_366058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_366058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366058 prefixEnd_366058 := by exact prefixLift 366058
  have htrace : WordTrace (prefixWord ++ tailWord_366058) baseStart_366058 baseEnd_366058 := by
    simpa [prefixWord, tailWord_366058, baseEnd_366058] using wordTrace_append hprefix tailTrace_366058
  have hstable : (prefixWord ++ tailWord_366058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366058).length < 2 ^ (prefixWord ++ tailWord_366058).sum := by decide
  have hdescent : baseEnd_366058 < baseStart_366058 := by decide
  rcases family_descends (prefixWord ++ tailWord_366058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366072 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_366072 : Nat := 118140960795 + 366072 * 2 ^ 59
def prefixEnd_366072 : Nat := 4983230072969 + 3 ^ 40 * 366072 * 2
def baseEnd_366072 : Nat := 167085235691375089170197

theorem tailTrace_366072 : CollatzResearch.WordTrace tailWord_366072 prefixEnd_366072 167085235691375089170197 := by
  unfold tailWord_366072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6675871364895569482614235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8901161819860759310152313 6675871364895569482614235)
  ·
    refine ⟨10013807047343354223921353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6675871364895569482614235 10013807047343354223921353)
    ·
      refine ⟨7510355285507515667941015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10013807047343354223921353 7510355285507515667941015)
      ·
        refine ⟨11265532928261273501911523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510355285507515667941015 11265532928261273501911523)
        ·
          refine ⟨16898299392391910252867285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265532928261273501911523 16898299392391910252867285)
          ·
            refine ⟨396053892009185396551577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16898299392391910252867285 396053892009185396551577)
            ·
              refine ⟨297040419006889047413683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396053892009185396551577 297040419006889047413683)
              ·
                refine ⟨445560628510333571120525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297040419006889047413683 445560628510333571120525)
                ·
                  refine ⟨167085235691375089170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445560628510333571120525 167085235691375089170197)
                  ·
                    rfl

theorem cell20_366072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_366072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366072 prefixEnd_366072 := by exact prefixLift 366072
  have htrace : WordTrace (prefixWord ++ tailWord_366072) baseStart_366072 baseEnd_366072 := by
    simpa [prefixWord, tailWord_366072, baseEnd_366072] using wordTrace_append hprefix tailTrace_366072
  have hstable : (prefixWord ++ tailWord_366072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366072).length < 2 ^ (prefixWord ++ tailWord_366072).sum := by decide
  have hdescent : baseEnd_366072 < baseStart_366072 := by decide
  rcases family_descends (prefixWord ++ tailWord_366072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366114 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_366114 : Nat := 118140960795 + 366114 * 2 ^ 59
def prefixEnd_366114 : Nat := 4983230072969 + 3 ^ 40 * 366114 * 2
def baseEnd_366114 : Nat := 167104405635809609770025

theorem tailTrace_366114 : CollatzResearch.WordTrace tailWord_366114 prefixEnd_366114 167104405635809609770025 := by
  unfold tailWord_366114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338318648909745034564349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8902183063759320092171597 3338318648909745034564349)
  ·
    refine ⟨1251869493341154387961631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3338318648909745034564349 1251869493341154387961631)
    ·
      refine ⟨1877804240011731581942447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251869493341154387961631 1877804240011731581942447)
      ·
        refine ⟨2816706360017597372913671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877804240011731581942447 2816706360017597372913671)
        ·
          refine ⟨4225059540026396059370507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816706360017597372913671 4225059540026396059370507)
          ·
            refine ⟨6337589310039594089055761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225059540026396059370507 6337589310039594089055761)
            ·
              refine ⟨4753191982529695566791821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6337589310039594089055761 4753191982529695566791821)
              ·
                refine ⟨1782446993448635837546933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4753191982529695566791821 1782446993448635837546933)
                ·
                  refine ⟨167104405635809609770025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782446993448635837546933 167104405635809609770025)
                  ·
                    rfl

theorem cell20_366114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_366114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366114 prefixEnd_366114 := by exact prefixLift 366114
  have htrace : WordTrace (prefixWord ++ tailWord_366114) baseStart_366114 baseEnd_366114 := by
    simpa [prefixWord, tailWord_366114, baseEnd_366114] using wordTrace_append hprefix tailTrace_366114
  have hstable : (prefixWord ++ tailWord_366114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366114).length < 2 ^ (prefixWord ++ tailWord_366114).sum := by decide
  have hdescent : baseEnd_366114 < baseStart_366114 := by decide
  rcases family_descends (prefixWord ++ tailWord_366114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366186 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_366186 : Nat := 118140960795 + 366186 * 2 ^ 59
def prefixEnd_366186 : Nat := 4983230072969 + 3 ^ 40 * 366186 * 2
def baseEnd_366186 : Nat := 167137268397697359369731

theorem tailTrace_366186 : CollatzResearch.WordTrace tailWord_366186 prefixEnd_366186 167137268397697359369731 := by
  unfold tailWord_366186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338975162844534108719603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8903933767585424289918941 3338975162844534108719603)
  ·
    refine ⟨5008462744266801163079405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338975162844534108719603 5008462744266801163079405)
    ·
      refine ⟨1878173529100050436154777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5008462744266801163079405 1878173529100050436154777)
      ·
        refine ⟨1408630146825037827116083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878173529100050436154777 1408630146825037827116083)
        ·
          refine ⟨2112945220237556740674125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408630146825037827116083 2112945220237556740674125)
          ·
            refine ⟨792354457589083777752797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2112945220237556740674125 792354457589083777752797)
            ·
              refine ⟨297132921595906416657299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 792354457589083777752797 297132921595906416657299)
              ·
                refine ⟨445699382393859624985949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297132921595906416657299 445699382393859624985949)
                ·
                  refine ⟨167137268397697359369731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445699382393859624985949 167137268397697359369731)
                  ·
                    rfl

theorem cell20_366186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_366186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366186 prefixEnd_366186 := by exact prefixLift 366186
  have htrace : WordTrace (prefixWord ++ tailWord_366186) baseStart_366186 baseEnd_366186 := by
    simpa [prefixWord, tailWord_366186, baseEnd_366186] using wordTrace_append hprefix tailTrace_366186
  have hstable : (prefixWord ++ tailWord_366186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366186).length < 2 ^ (prefixWord ++ tailWord_366186).sum := by decide
  have hdescent : baseEnd_366186 < baseStart_366186 := by decide
  rcases family_descends (prefixWord ++ tailWord_366186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366238 : List Nat := [4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_366238 : Nat := 118140960795 + 366238 * 2 ^ 59
def prefixEnd_366238 : Nat := 4983230072969 + 3 ^ 40 * 366238 * 2
def baseEnd_366238 : Nat := 55720334204872096545395

theorem tailTrace_366238 : CollatzResearch.WordTrace tailWord_366238 prefixEnd_366238 55720334204872096545395 := by
  unfold tailWord_366238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669724655898718664471421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8905198164793166210514245 1669724655898718664471421)
  ·
    refine ⟨626146745962019499176783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1669724655898718664471421 626146745962019499176783)
    ·
      refine ⟨939220118943029248765175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626146745962019499176783 939220118943029248765175)
      ·
        refine ⟨1408830178414543873147763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939220118943029248765175 1408830178414543873147763)
        ·
          refine ⟨2113245267621815809721645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408830178414543873147763 2113245267621815809721645)
          ·
            refine ⟨792466975358180928645617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2113245267621815809721645 792466975358180928645617)
            ·
              refine ⟨594350231518635696484213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792466975358180928645617 594350231518635696484213)
              ·
                refine ⟨55720334204872096545395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 594350231518635696484213 55720334204872096545395)
                ·
                  rfl

theorem cell20_366238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_366238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366238 prefixEnd_366238 := by exact prefixLift 366238
  have htrace : WordTrace (prefixWord ++ tailWord_366238) baseStart_366238 baseEnd_366238 := by
    simpa [prefixWord, tailWord_366238, baseEnd_366238] using wordTrace_append hprefix tailTrace_366238
  have hstable : (prefixWord ++ tailWord_366238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366238).length < 2 ^ (prefixWord ++ tailWord_366238).sum := by decide
  have hdescent : baseEnd_366238 < baseStart_366238 := by decide
  rcases family_descends (prefixWord ++ tailWord_366238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366245 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 3]
def baseStart_366245 : Nat := 118140960795 + 366245 * 2 ^ 59
def prefixEnd_366245 : Nat := 4983230072969 + 3 ^ 40 * 366245 * 2
def baseEnd_366245 : Nat := 167164197605355376402823

theorem tailTrace_366245 : CollatzResearch.WordTrace tailWord_366245 prefixEnd_366245 167164197605355376402823 := by
  unfold tailWord_366245
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358052558164389511276189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8905368372109593007517459 13358052558164389511276189)
  ·
    refine ⟨5009269709311646066728571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13358052558164389511276189 5009269709311646066728571)
    ·
      refine ⟨7513904563967469100092857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009269709311646066728571 7513904563967469100092857)
      ·
        refine ⟨5635428422975601825069643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7513904563967469100092857 5635428422975601825069643)
        ·
          refine ⟨8453142634463402737604465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635428422975601825069643 8453142634463402737604465)
          ·
            refine ⟨6339856975847552053203349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8453142634463402737604465 6339856975847552053203349)
            ·
              refine ⟨297180795742854002493907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6339856975847552053203349 297180795742854002493907)
              ·
                refine ⟨445771193614281003740861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297180795742854002493907 445771193614281003740861)
                ·
                  refine ⟨167164197605355376402823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445771193614281003740861 167164197605355376402823)
                  ·
                    rfl

theorem cell20_366245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_366245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366245 prefixEnd_366245 := by exact prefixLift 366245
  have htrace : WordTrace (prefixWord ++ tailWord_366245) baseStart_366245 baseEnd_366245 := by
    simpa [prefixWord, tailWord_366245, baseEnd_366245] using wordTrace_append hprefix tailTrace_366245
  have hstable : (prefixWord ++ tailWord_366245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366245).length < 2 ^ (prefixWord ++ tailWord_366245).sum := by decide
  have hdescent : baseEnd_366245 < baseStart_366245 := by decide
  rcases family_descends (prefixWord ++ tailWord_366245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366287 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_366287 : Nat := 118140960795 + 366287 * 2 ^ 59
def prefixEnd_366287 : Nat := 4983230072969 + 3 ^ 40 * 366287 * 2
def baseEnd_366287 : Nat := 167183367549789897002651

theorem tailTrace_366287 : CollatzResearch.WordTrace tailWord_366287 prefixEnd_366287 167183367549789897002651 := by
  unfold tailWord_366287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359584424012230684305115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8906389616008153789536743 13359584424012230684305115)
  ·
    refine ⟨20039376636018346026457673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359584424012230684305115 20039376636018346026457673)
    ·
      refine ⟨15029532477013759519843255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20039376636018346026457673 15029532477013759519843255)
      ·
        refine ⟨22544298715520639279764883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15029532477013759519843255 22544298715520639279764883)
        ·
          refine ⟨33816448073280958919647325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22544298715520639279764883 33816448073280958919647325)
          ·
            refine ⟨12681168027480359594867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33816448073280958919647325 12681168027480359594867747)
            ·
              refine ⟨19021752041220539392301621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12681168027480359594867747 19021752041220539392301621)
              ·
                refine ⟨1783289253864425568028277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19021752041220539392301621 1783289253864425568028277)
                ·
                  refine ⟨167183367549789897002651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1783289253864425568028277 167183367549789897002651)
                  ·
                    rfl

theorem cell20_366287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_366287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366287 prefixEnd_366287 := by exact prefixLift 366287
  have htrace : WordTrace (prefixWord ++ tailWord_366287) baseStart_366287 baseEnd_366287 := by
    simpa [prefixWord, tailWord_366287, baseEnd_366287] using wordTrace_append hprefix tailTrace_366287
  have hstable : (prefixWord ++ tailWord_366287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366287).length < 2 ^ (prefixWord ++ tailWord_366287).sum := by decide
  have hdescent : baseEnd_366287 < baseStart_366287 := by decide
  rcases family_descends (prefixWord ++ tailWord_366287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366297 : List Nat := [1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_366297 : Nat := 118140960795 + 366297 * 2 ^ 59
def prefixEnd_366297 : Nat := 4983230072969 + 3 ^ 40 * 366297 * 2
def baseEnd_366297 : Nat := 55729310607424768889759

theorem tailTrace_366297 : CollatzResearch.WordTrace tailWord_366297 prefixEnd_366297 55729310607424768889759 := by
  unfold tailWord_366297
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359949153976002392169145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8906632769317334928112763 13359949153976002392169145)
  ·
    refine ⟨10019961865482001794126859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13359949153976002392169145 10019961865482001794126859)
    ·
      refine ⟨15029942798223002691190289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10019961865482001794126859 15029942798223002691190289)
      ·
        refine ⟨11272457098667252018392717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15029942798223002691190289 11272457098667252018392717)
        ·
          refine ⟨4227171412000219506897269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11272457098667252018392717 4227171412000219506897269)
          ·
            refine ⟨396297319875020578771619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4227171412000219506897269 396297319875020578771619)
            ·
              refine ⟨594445979812530868157429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396297319875020578771619 594445979812530868157429)
              ·
                refine ⟨55729310607424768889759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 594445979812530868157429 55729310607424768889759)
                ·
                  rfl

theorem cell20_366297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_366297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366297 prefixEnd_366297 := by exact prefixLift 366297
  have htrace : WordTrace (prefixWord ++ tailWord_366297) baseStart_366297 baseEnd_366297 := by
    simpa [prefixWord, tailWord_366297, baseEnd_366297] using wordTrace_append hprefix tailTrace_366297
  have hstable : (prefixWord ++ tailWord_366297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366297).length < 2 ^ (prefixWord ++ tailWord_366297).sum := by decide
  have hdescent : baseEnd_366297 < baseStart_366297 := by decide
  rcases family_descends (prefixWord ++ tailWord_366297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366304 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_366304 : Nat := 118140960795 + 366304 * 2 ^ 59
def prefixEnd_366304 : Nat := 4983230072969 + 3 ^ 40 * 366304 * 2
def baseEnd_366304 : Nat := 167191126813013393435915

theorem tailTrace_366304 : CollatzResearch.WordTrace tailWord_366304 prefixEnd_366304 167191126813013393435915 := by
  unfold tailWord_366304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680102232475321293836983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8906802976633761725115977 6680102232475321293836983)
  ·
    refine ⟨10020153348712981940755475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680102232475321293836983 10020153348712981940755475)
    ·
      refine ⟨15030230023069472911133213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10020153348712981940755475 15030230023069472911133213)
      ·
        refine ⟨5636336258651052341674955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15030230023069472911133213 5636336258651052341674955)
        ·
          refine ⟨8454504387976578512512433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636336258651052341674955 8454504387976578512512433)
          ·
            refine ⟨6340878290982433884384325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8454504387976578512512433 6340878290982433884384325)
            ·
              refine ⟨1188914679559206353322061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6340878290982433884384325 1188914679559206353322061)
              ·
                refine ⟨445843004834702382495773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1188914679559206353322061 445843004834702382495773)
                ·
                  refine ⟨167191126813013393435915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445843004834702382495773 167191126813013393435915)
                  ·
                    rfl

theorem cell20_366304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_366304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366304 prefixEnd_366304 := by exact prefixLift 366304
  have htrace : WordTrace (prefixWord ++ tailWord_366304) baseStart_366304 baseEnd_366304 := by
    simpa [prefixWord, tailWord_366304, baseEnd_366304] using wordTrace_append hprefix tailTrace_366304
  have hstable : (prefixWord ++ tailWord_366304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366304).length < 2 ^ (prefixWord ++ tailWord_366304).sum := by decide
  have hdescent : baseEnd_366304 < baseStart_366304 := by decide
  rcases family_descends (prefixWord ++ tailWord_366304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366373 : List Nat := [1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_366373 : Nat := 118140960795 + 366373 * 2 ^ 59
def prefixEnd_366373 : Nat := 4983230072969 + 3 ^ 40 * 366373 * 2
def baseEnd_366373 : Nat := 55740873431051940045211

theorem tailTrace_366373 : CollatzResearch.WordTrace tailWord_366373 prefixEnd_366373 55740873431051940045211 := by
  unfold tailWord_366373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13362721101700667371935773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8908480734467111581290515 13362721101700667371935773)
  ·
    refine ⟨5011020413137750264475915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13362721101700667371935773 5011020413137750264475915)
    ·
      refine ⟨7516530619706625396713873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011020413137750264475915 7516530619706625396713873)
      ·
        refine ⟨5637397964779969047535405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7516530619706625396713873 5637397964779969047535405)
        ·
          refine ⟨2114024236792488392825777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5637397964779969047535405 2114024236792488392825777)
          ·
            refine ⟨1585518177594366294619333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114024236792488392825777 1585518177594366294619333)
            ·
              refine ⟨297284658298943680241125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1585518177594366294619333 297284658298943680241125)
              ·
                refine ⟨55740873431051940045211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297284658298943680241125 55740873431051940045211)
                ·
                  rfl

theorem cell20_366373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_366373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366373 prefixEnd_366373 := by exact prefixLift 366373
  have htrace : WordTrace (prefixWord ++ tailWord_366373) baseStart_366373 baseEnd_366373 := by
    simpa [prefixWord, tailWord_366373, baseEnd_366373] using wordTrace_append hprefix tailTrace_366373
  have hstable : (prefixWord ++ tailWord_366373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366373).length < 2 ^ (prefixWord ++ tailWord_366373).sum := by decide
  have hdescent : baseEnd_366373 < baseStart_366373 := by decide
  rcases family_descends (prefixWord ++ tailWord_366373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366390 : List Nat := [5, 1, 2, 2, 1, 3, 6]
def baseStart_366390 : Nat := 118140960795 + 366390 * 2 ^ 59
def prefixEnd_366390 : Nat := 4983230072969 + 3 ^ 40 * 366390 * 2
def baseEnd_366390 : Nat := 18581153284042146285433

theorem tailTrace_366390 : CollatzResearch.WordTrace tailWord_366390 prefixEnd_366390 18581153284042146285433 := by
  unfold tailWord_366390
  simp only [CollatzResearch.WordTrace]
  refine ⟨835208821414942454706539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8908894095092719516869749 835208821414942454706539)
  ·
    refine ⟨1252813232122413682059809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835208821414942454706539 1252813232122413682059809)
    ·
      refine ⟨939609924091810261544857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1252813232122413682059809 939609924091810261544857)
      ·
        refine ⟨704707443068857696158643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 939609924091810261544857 704707443068857696158643)
        ·
          refine ⟨1057061164603286544237965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704707443068857696158643 1057061164603286544237965)
          ·
            refine ⟨396397936726232454089237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1057061164603286544237965 396397936726232454089237)
            ·
              refine ⟨18581153284042146285433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 396397936726232454089237 18581153284042146285433)
              ·
                rfl

theorem cell20_366390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_366390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366390 prefixEnd_366390 := by exact prefixLift 366390
  have htrace : WordTrace (prefixWord ++ tailWord_366390) baseStart_366390 baseEnd_366390 := by
    simpa [prefixWord, tailWord_366390, baseEnd_366390] using wordTrace_append hprefix tailTrace_366390
  have hstable : (prefixWord ++ tailWord_366390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366390).length < 2 ^ (prefixWord ++ tailWord_366390).sum := by decide
  have hdescent : baseEnd_366390 < baseStart_366390 := by decide
  rcases family_descends (prefixWord ++ tailWord_366390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366394 : List Nat := [3, 1, 1, 1, 5, 1, 8]
def baseStart_366394 : Nat := 118140960795 + 366394 * 2 ^ 59
def prefixEnd_366394 : Nat := 4983230072969 + 3 ^ 40 * 366394 * 2
def baseEnd_366394 : Nat := 18581356140597008937283

theorem tailTrace_366394 : CollatzResearch.WordTrace tailWord_366394 prefixEnd_366394 18581356140597008937283 := by
  unfold tailWord_366394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3340871758656146989612559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8908991356416391972300157 3340871758656146989612559)
  ·
    refine ⟨5011307637984220484418839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3340871758656146989612559 5011307637984220484418839)
    ·
      refine ⟨7516961456976330726628259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011307637984220484418839 7516961456976330726628259)
      ·
        refine ⟨11275442185464496089942389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7516961456976330726628259 11275442185464496089942389)
        ·
          refine ⟨1057072704887296508432099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11275442185464496089942389 1057072704887296508432099)
          ·
            refine ⟨1585609057330944762648149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057072704887296508432099 1585609057330944762648149)
            ·
              refine ⟨18581356140597008937283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1585609057330944762648149 18581356140597008937283)
              ·
                rfl

theorem cell20_366394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_366394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366394 prefixEnd_366394 := by exact prefixLift 366394
  have htrace : WordTrace (prefixWord ++ tailWord_366394) baseStart_366394 baseEnd_366394 := by
    simpa [prefixWord, tailWord_366394, baseEnd_366394] using wordTrace_append hprefix tailTrace_366394
  have hstable : (prefixWord ++ tailWord_366394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366394).length < 2 ^ (prefixWord ++ tailWord_366394).sum := by decide
  have hdescent : baseEnd_366394 < baseStart_366394 := by decide
  rcases family_descends (prefixWord ++ tailWord_366394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366432 : List Nat := [2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_366432 : Nat := 118140960795 + 366432 * 2 ^ 59
def prefixEnd_366432 : Nat := 4983230072969 + 3 ^ 40 * 366432 * 2
def baseEnd_366432 : Nat := 55749849833604612389575

theorem tailTrace_366432 : CollatzResearch.WordTrace tailWord_366432 prefixEnd_366432 55749849833604612389575 := by
  unfold tailWord_366432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682436504243460224166775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8909915338991280298889033 6682436504243460224166775)
  ·
    refine ⟨10023654756365190336250163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6682436504243460224166775 10023654756365190336250163)
    ·
      refine ⟨15035482134547785504375245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10023654756365190336250163 15035482134547785504375245)
      ·
        refine ⟨5638305800455419564140717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15035482134547785504375245 5638305800455419564140717)
        ·
          refine ⟨2114364675170782336552769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5638305800455419564140717 2114364675170782336552769)
          ·
            refine ⟨1585773506378086752414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114364675170782336552769 1585773506378086752414577)
            ·
              refine ⟨1189330129783565064310933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585773506378086752414577 1189330129783565064310933)
              ·
                refine ⟨55749849833604612389575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1189330129783565064310933 55749849833604612389575)
                ·
                  rfl

theorem cell20_366432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_366432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366432 prefixEnd_366432 := by exact prefixLift 366432
  have htrace : WordTrace (prefixWord ++ tailWord_366432) baseStart_366432 baseEnd_366432 := by
    simpa [prefixWord, tailWord_366432, baseEnd_366432] using wordTrace_append hprefix tailTrace_366432
  have hstable : (prefixWord ++ tailWord_366432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366432).length < 2 ^ (prefixWord ++ tailWord_366432).sum := by decide
  have hdescent : baseEnd_366432 < baseStart_366432 := by decide
  rcases family_descends (prefixWord ++ tailWord_366432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366487 : List Nat := [1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_366487 : Nat := 118140960795 + 366487 * 2 ^ 59
def prefixEnd_366487 : Nat := 4983230072969 + 3 ^ 40 * 366487 * 2
def baseEnd_366487 : Nat := 55758217666492696778389

theorem tailTrace_366487 : CollatzResearch.WordTrace tailWord_366487 prefixEnd_366487 55758217666492696778389 := by
  unfold tailWord_366487
  simp only [CollatzResearch.WordTrace]
  refine ⟨13366879023287664841585715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8911252682191776561057143 13366879023287664841585715)
  ·
    refine ⟨20050318534931497262378573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13366879023287664841585715 20050318534931497262378573)
    ·
      refine ⟨7518869450599311473391965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20050318534931497262378573 7518869450599311473391965)
      ·
        refine ⟨2819576043974741802521987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7518869450599311473391965 2819576043974741802521987)
        ·
          refine ⟨4229364065962112703782981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819576043974741802521987 4229364065962112703782981)
          ·
            refine ⟨793005762367896131959309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4229364065962112703782981 793005762367896131959309)
            ·
              refine ⟨297377160887961049484741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 793005762367896131959309 297377160887961049484741)
              ·
                refine ⟨55758217666492696778389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297377160887961049484741 55758217666492696778389)
                ·
                  rfl

theorem cell20_366487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_366487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366487 prefixEnd_366487 := by exact prefixLift 366487
  have htrace : WordTrace (prefixWord ++ tailWord_366487) baseStart_366487 baseEnd_366487 := by
    simpa [prefixWord, tailWord_366487, baseEnd_366487] using wordTrace_append hprefix tailTrace_366487
  have hstable : (prefixWord ++ tailWord_366487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366487).length < 2 ^ (prefixWord ++ tailWord_366487).sum := by decide
  have hdescent : baseEnd_366487 < baseStart_366487 := by decide
  rcases family_descends (prefixWord ++ tailWord_366487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366504 : List Nat := [2, 1, 6, 2, 1, 1, 7]
def baseStart_366504 : Nat := 118140960795 + 366504 * 2 ^ 59
def prefixEnd_366504 : Nat := 4983230072969 + 3 ^ 40 * 366504 * 2
def baseEnd_366504 : Nat := 18586934695855731863159

theorem tailTrace_366504 : CollatzResearch.WordTrace tailWord_366504 prefixEnd_366504 18586934695855731863159 := by
  unfold tailWord_366504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683749532113038372477283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8911666042817384496636377 6683749532113038372477283)
  ·
    refine ⟨10025624298169557558715925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6683749532113038372477283 10025624298169557558715925)
    ·
      refine ⟨469951138976698010564809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10025624298169557558715925 469951138976698010564809)
      ·
        refine ⟨352463354232523507923607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469951138976698010564809 352463354232523507923607)
        ·
          refine ⟨528695031348785261885411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352463354232523507923607 528695031348785261885411)
          ·
            refine ⟨793042547023177892828117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528695031348785261885411 793042547023177892828117)
            ·
              refine ⟨18586934695855731863159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 793042547023177892828117 18586934695855731863159)
              ·
                rfl

theorem cell20_366504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_366504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366504 prefixEnd_366504 := by exact prefixLift 366504
  have htrace : WordTrace (prefixWord ++ tailWord_366504) baseStart_366504 baseEnd_366504 := by
    simpa [prefixWord, tailWord_366504, baseEnd_366504] using wordTrace_append hprefix tailTrace_366504
  have hstable : (prefixWord ++ tailWord_366504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366504).length < 2 ^ (prefixWord ++ tailWord_366504).sum := by decide
  have hdescent : baseEnd_366504 < baseStart_366504 := by decide
  rcases family_descends (prefixWord ++ tailWord_366504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366515 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_366515 : Nat := 118140960795 + 366515 * 2 ^ 59
def prefixEnd_366515 : Nat := 4983230072969 + 3 ^ 40 * 366515 * 2
def baseEnd_366515 : Nat := 167287432962434437401719

theorem tailTrace_366515 : CollatzResearch.WordTrace tailWord_366515 prefixEnd_366515 167287432962434437401719 := by
  unfold tailWord_366515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367900267186225623604999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8911933511457483749069999 13367900267186225623604999)
  ·
    refine ⟨20051850400779338435407499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13367900267186225623604999 20051850400779338435407499)
    ·
      refine ⟨30077775601169007653111249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20051850400779338435407499 30077775601169007653111249)
      ·
        refine ⟨22558331700876755739833437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30077775601169007653111249 22558331700876755739833437)
        ·
          refine ⟨8459374387828783402437539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22558331700876755739833437 8459374387828783402437539)
          ·
            refine ⟨12689061581743175103656309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8459374387828783402437539 12689061581743175103656309)
            ·
              refine ⟨1189599523288422665967779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12689061581743175103656309 1189599523288422665967779)
              ·
                refine ⟨1784399284932633998951669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189599523288422665967779 1784399284932633998951669)
                ·
                  refine ⟨167287432962434437401719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1784399284932633998951669 167287432962434437401719)
                  ·
                    rfl

theorem cell20_366515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_366515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366515 prefixEnd_366515 := by exact prefixLift 366515
  have htrace : WordTrace (prefixWord ++ tailWord_366515) baseStart_366515 baseEnd_366515 := by
    simpa [prefixWord, tailWord_366515, baseEnd_366515] using wordTrace_append hprefix tailTrace_366515
  have hstable : (prefixWord ++ tailWord_366515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366515).length < 2 ^ (prefixWord ++ tailWord_366515).sum := by decide
  have hdescent : baseEnd_366515 < baseStart_366515 := by decide
  rcases family_descends (prefixWord ++ tailWord_366515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366560 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_366560 : Nat := 118140960795 + 366560 * 2 ^ 59
def prefixEnd_366560 : Nat := 4983230072969 + 3 ^ 40 * 366560 * 2
def baseEnd_366560 : Nat := 167307972188614280901535

theorem tailTrace_366560 : CollatzResearch.WordTrace tailWord_366560 prefixEnd_366560 167307972188614280901535 := by
  unfold tailWord_366560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684770776011599154496567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8913027701348798872662089 6684770776011599154496567)
  ·
    refine ⟨10027156164017398731744851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6684770776011599154496567 10027156164017398731744851)
    ·
      refine ⟨15040734246026098097617277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10027156164017398731744851 15040734246026098097617277)
      ·
        refine ⟨5640275342259786786606479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15040734246026098097617277 5640275342259786786606479)
        ·
          refine ⟨8460413013389680179909719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640275342259786786606479 8460413013389680179909719)
          ·
            refine ⟨12690619520084520269864579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8460413013389680179909719 12690619520084520269864579)
            ·
              refine ⟨19035929280126780404796869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12690619520084520269864579 19035929280126780404796869)
              ·
                refine ⟨3569236740023771325899413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19035929280126780404796869 3569236740023771325899413)
                ·
                  refine ⟨167307972188614280901535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3569236740023771325899413 167307972188614280901535)
                  ·
                    rfl

theorem cell20_366560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_366560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366560 prefixEnd_366560 := by exact prefixLift 366560
  have htrace : WordTrace (prefixWord ++ tailWord_366560) baseStart_366560 baseEnd_366560 := by
    simpa [prefixWord, tailWord_366560, baseEnd_366560] using wordTrace_append hprefix tailTrace_366560
  have hstable : (prefixWord ++ tailWord_366560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366560).length < 2 ^ (prefixWord ++ tailWord_366560).sum := by decide
  have hdescent : baseEnd_366560 < baseStart_366560 := by decide
  rcases family_descends (prefixWord ++ tailWord_366560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366570 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_366570 : Nat := 118140960795 + 366570 * 2 ^ 59
def prefixEnd_366570 : Nat := 4983230072969 + 3 ^ 40 * 366570 * 2
def baseEnd_366570 : Nat := 167312536461098690568161

theorem tailTrace_366570 : CollatzResearch.WordTrace tailWord_366570 prefixEnd_366570 167312536461098690568161 := by
  unfold tailWord_366570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3342476570496742504214291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8913270854657980011238109 3342476570496742504214291)
  ·
    refine ⟨5013714855745113756321437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3342476570496742504214291 5013714855745113756321437)
    ·
      refine ⟨1880143070904417658620539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5013714855745113756321437 1880143070904417658620539)
      ·
        refine ⟨2820214606356626487930809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880143070904417658620539 2820214606356626487930809)
        ·
          refine ⟨2115160954767469865948107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820214606356626487930809 2115160954767469865948107)
          ·
            refine ⟨3172741432151204798922161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115160954767469865948107 3172741432151204798922161)
            ·
              refine ⟨2379556074113403599191621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172741432151204798922161 2379556074113403599191621)
              ·
                refine ⟨446166763896263174848429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2379556074113403599191621 446166763896263174848429)
                ·
                  refine ⟨167312536461098690568161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446166763896263174848429 167312536461098690568161)
                  ·
                    rfl

theorem cell20_366570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_366570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366570 prefixEnd_366570 := by exact prefixLift 366570
  have htrace : WordTrace (prefixWord ++ tailWord_366570) baseStart_366570 baseEnd_366570 := by
    simpa [prefixWord, tailWord_366570, baseEnd_366570] using wordTrace_append hprefix tailTrace_366570
  have hstable : (prefixWord ++ tailWord_366570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366570).length < 2 ^ (prefixWord ++ tailWord_366570).sum := by decide
  have hdescent : baseEnd_366570 < baseStart_366570 := by decide
  rcases family_descends (prefixWord ++ tailWord_366570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366625 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_366625 : Nat := 118140960795 + 366625 * 2 ^ 59
def prefixEnd_366625 : Nat := 4983230072969 + 3 ^ 40 * 366625 * 2
def baseEnd_366625 : Nat := 167337639959762943734603

theorem tailTrace_366625 : CollatzResearch.WordTrace tailWord_366625 prefixEnd_366625 167337639959762943734603 := by
  unfold tailWord_366625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371912296787714410109329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8914608197858476273406219 13371912296787714410109329)
  ·
    refine ⟨10028934222590785807581997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13371912296787714410109329 10028934222590785807581997)
    ·
      refine ⟨3760850333471544677843249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10028934222590785807581997 3760850333471544677843249)
      ·
        refine ⟨2820637750103658508382437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3760850333471544677843249 2820637750103658508382437)
        ·
          refine ⟨528869578144435970321707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2820637750103658508382437 528869578144435970321707)
          ·
            refine ⟨793304367216653955482561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528869578144435970321707 793304367216653955482561)
            ·
              refine ⟨594978275412490466611921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793304367216653955482561 594978275412490466611921)
              ·
                refine ⟨446233706559367849958941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594978275412490466611921 446233706559367849958941)
                ·
                  refine ⟨167337639959762943734603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446233706559367849958941 167337639959762943734603)
                  ·
                    rfl

theorem cell20_366625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_366625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366625 prefixEnd_366625 := by exact prefixLift 366625
  have htrace : WordTrace (prefixWord ++ tailWord_366625) baseStart_366625 baseEnd_366625 := by
    simpa [prefixWord, tailWord_366625, baseEnd_366625] using wordTrace_append hprefix tailTrace_366625
  have hstable : (prefixWord ++ tailWord_366625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366625).length < 2 ^ (prefixWord ++ tailWord_366625).sum := by decide
  have hdescent : baseEnd_366625 < baseStart_366625 := by decide
  rcases family_descends (prefixWord ++ tailWord_366625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366653 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_366653 : Nat := 118140960795 + 366653 * 2 ^ 59
def prefixEnd_366653 : Nat := 4983230072969 + 3 ^ 40 * 366653 * 2
def baseEnd_366653 : Nat := 167350419922719290801155

theorem tailTrace_366653 : CollatzResearch.WordTrace tailWord_366653 prefixEnd_366653 167350419922719290801155 := by
  unfold tailWord_366653
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372933540686275192128613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8915289027124183461419075 13372933540686275192128613)
  ·
    refine ⟨2507425038878676598524115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13372933540686275192128613 2507425038878676598524115)
    ·
      refine ⟨3761137558318014897786173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507425038878676598524115 3761137558318014897786173)
      ·
        refine ⟨1410426584369255586669815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3761137558318014897786173 1410426584369255586669815)
        ·
          refine ⟨2115639876553883380004723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410426584369255586669815 2115639876553883380004723)
          ·
            refine ⟨3173459814830825070007085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115639876553883380004723 3173459814830825070007085)
            ·
              refine ⟨1190047430561559401252657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3173459814830825070007085 1190047430561559401252657)
              ·
                refine ⟨892535572921169550939493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190047430561559401252657 892535572921169550939493)
                ·
                  refine ⟨167350419922719290801155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892535572921169550939493 167350419922719290801155)
                  ·
                    rfl

theorem cell20_366653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_366653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366653 prefixEnd_366653 := by exact prefixLift 366653
  have htrace : WordTrace (prefixWord ++ tailWord_366653) baseStart_366653 baseEnd_366653 := by
    simpa [prefixWord, tailWord_366653, baseEnd_366653] using wordTrace_append hprefix tailTrace_366653
  have hstable : (prefixWord ++ tailWord_366653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366653).length < 2 ^ (prefixWord ++ tailWord_366653).sum := by decide
  have hdescent : baseEnd_366653 < baseStart_366653 := by decide
  rcases family_descends (prefixWord ++ tailWord_366653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366670 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_366670 : Nat := 118140960795 + 366670 * 2 ^ 59
def prefixEnd_366670 : Nat := 4983230072969 + 3 ^ 40 * 366670 * 2
def baseEnd_366670 : Nat := 167358179185942787234419

theorem tailTrace_366670 : CollatzResearch.WordTrace tailWord_366670 prefixEnd_366670 167358179185942787234419 := by
  unfold tailWord_366670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671694197703085886937183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8915702387749791396998309 1671694197703085886937183)
  ·
    refine ⟨2507541296554628830405775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671694197703085886937183 2507541296554628830405775)
    ·
      refine ⟨3761311944831943245608663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507541296554628830405775 3761311944831943245608663)
      ·
        refine ⟨5641967917247914868412995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761311944831943245608663 5641967917247914868412995)
        ·
          refine ⟨8462951875871872302619493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641967917247914868412995 8462951875871872302619493)
          ·
            refine ⟨1586803476725976056741155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8462951875871872302619493 1586803476725976056741155)
            ·
              refine ⟨2380205215088964085111733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586803476725976056741155 2380205215088964085111733)
              ·
                refine ⟨223144238914590382979225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2380205215088964085111733 223144238914590382979225)
                ·
                  refine ⟨167358179185942787234419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223144238914590382979225 167358179185942787234419)
                  ·
                    rfl

theorem cell20_366670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_366670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366670 prefixEnd_366670 := by exact prefixLift 366670
  have htrace : WordTrace (prefixWord ++ tailWord_366670) baseStart_366670 baseEnd_366670 := by
    simpa [prefixWord, tailWord_366670, baseEnd_366670] using wordTrace_append hprefix tailTrace_366670
  have hstable : (prefixWord ++ tailWord_366670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366670).length < 2 ^ (prefixWord ++ tailWord_366670).sum := by decide
  have hdescent : baseEnd_366670 < baseStart_366670 := by decide
  rcases family_descends (prefixWord ++ tailWord_366670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366681 : List Nat := [1, 2, 1, 2, 2, 1, 11]
def baseStart_366681 : Nat := 118140960795 + 366681 * 2 ^ 59
def prefixEnd_366681 : Nat := 4983230072969 + 3 ^ 40 * 366681 * 2
def baseEnd_366681 : Nat := 18595911098408404207523

theorem tailTrace_366681 : CollatzResearch.WordTrace tailWord_366681 prefixEnd_366681 18595911098408404207523 := by
  unfold tailWord_366681
  simp only [CollatzResearch.WordTrace]
  refine ⟨13373954784584835974147897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8915969856389890649431931 13373954784584835974147897)
  ·
    refine ⟨10030466088438626980610923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13373954784584835974147897 10030466088438626980610923)
    ·
      refine ⟨15045699132657940470916385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10030466088438626980610923 15045699132657940470916385)
      ·
        refine ⟨11284274349493455353187289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15045699132657940470916385 11284274349493455353187289)
        ·
          refine ⟨8463205762120091514890467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11284274349493455353187289 8463205762120091514890467)
          ·
            refine ⟨12694808643180137272335701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463205762120091514890467 12694808643180137272335701)
            ·
              refine ⟨18595911098408404207523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12694808643180137272335701 18595911098408404207523)
              ·
                rfl

theorem cell20_366681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_366681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366681 prefixEnd_366681 := by exact prefixLift 366681
  have htrace : WordTrace (prefixWord ++ tailWord_366681) baseStart_366681 baseEnd_366681 := by
    simpa [prefixWord, tailWord_366681, baseEnd_366681] using wordTrace_append hprefix tailTrace_366681
  have hstable : (prefixWord ++ tailWord_366681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366681).length < 2 ^ (prefixWord ++ tailWord_366681).sum := by decide
  have hdescent : baseEnd_366681 < baseStart_366681 := by decide
  rcases family_descends (prefixWord ++ tailWord_366681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366684 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_366684 : Nat := 118140960795 + 366684 * 2 ^ 59
def prefixEnd_366684 : Nat := 4983230072969 + 3 ^ 40 * 366684 * 2
def baseEnd_366684 : Nat := 167364569167420960767695

theorem tailTrace_366684 : CollatzResearch.WordTrace tailWord_366684 prefixEnd_366684 167364569167420960767695 := by
  unfold tailWord_366684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687032101786983743253553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8916042802382644991004737 6687032101786983743253553)
  ·
    refine ⟨5015274076340237807440165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6687032101786983743253553 5015274076340237807440165)
    ·
      refine ⟨940363889313794588895031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5015274076340237807440165 940363889313794588895031)
      ·
        refine ⟨1410545833970691883342547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940363889313794588895031 1410545833970691883342547)
        ·
          refine ⟨2115818750956037825013821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410545833970691883342547 2115818750956037825013821)
          ·
            refine ⟨793432031608514184380183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2115818750956037825013821 793432031608514184380183)
            ·
              refine ⟨1190148047412771276570275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793432031608514184380183 1190148047412771276570275)
              ·
                refine ⟨1785222071119156914855413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190148047412771276570275 1785222071119156914855413)
                ·
                  refine ⟨167364569167420960767695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1785222071119156914855413 167364569167420960767695)
                  ·
                    rfl

theorem cell20_366684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_366684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366684 prefixEnd_366684 := by exact prefixLift 366684
  have htrace : WordTrace (prefixWord ++ tailWord_366684) baseStart_366684 baseEnd_366684 := by
    simpa [prefixWord, tailWord_366684, baseEnd_366684] using wordTrace_append hprefix tailTrace_366684
  have hstable : (prefixWord ++ tailWord_366684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366684).length < 2 ^ (prefixWord ++ tailWord_366684).sum := by decide
  have hdescent : baseEnd_366684 < baseStart_366684 := by decide
  rcases family_descends (prefixWord ++ tailWord_366684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366701 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 3]
def baseStart_366701 : Nat := 118140960795 + 366701 * 2 ^ 59
def prefixEnd_366701 : Nat := 4983230072969 + 3 ^ 40 * 366701 * 2
def baseEnd_366701 : Nat := 167372328430644457200959

theorem tailTrace_366701 : CollatzResearch.WordTrace tailWord_366701 prefixEnd_366701 167372328430644457200959 := by
  unfold tailWord_366701
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374684244512379389875957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8916456163008252926583971 13374684244512379389875957)
  ·
    refine ⟨1253876647923035567800871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13374684244512379389875957 1253876647923035567800871)
    ·
      refine ⟨1880814971884553351701307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253876647923035567800871 1880814971884553351701307)
      ·
        refine ⟨2821222457826830027551961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880814971884553351701307 2821222457826830027551961)
        ·
          refine ⟨2115916843370122520663971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821222457826830027551961 2115916843370122520663971)
          ·
            refine ⟨3173875265055183780995957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115916843370122520663971 3173875265055183780995957)
            ·
              refine ⟨297550806098923479468371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3173875265055183780995957 297550806098923479468371)
              ·
                refine ⟨446326209148385219202557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297550806098923479468371 446326209148385219202557)
                ·
                  refine ⟨167372328430644457200959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446326209148385219202557 167372328430644457200959)
                  ·
                    rfl

theorem cell20_366701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_366701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366701 prefixEnd_366701 := by exact prefixLift 366701
  have htrace : WordTrace (prefixWord ++ tailWord_366701) baseStart_366701 baseEnd_366701 := by
    simpa [prefixWord, tailWord_366701, baseEnd_366701] using wordTrace_append hprefix tailTrace_366701
  have hstable : (prefixWord ++ tailWord_366701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366701).length < 2 ^ (prefixWord ++ tailWord_366701).sum := by decide
  have hdescent : baseEnd_366701 < baseStart_366701 := by decide
  rcases family_descends (prefixWord ++ tailWord_366701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366725 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 2]
def baseStart_366725 : Nat := 118140960795 + 366725 * 2 ^ 59
def prefixEnd_366725 : Nat := 4983230072969 + 3 ^ 40 * 366725 * 2
def baseEnd_366725 : Nat := 167383282684607040400861

theorem tailTrace_366725 : CollatzResearch.WordTrace tailWord_366725 prefixEnd_366725 167383282684607040400861 := by
  unfold tailWord_366725
  simp only [CollatzResearch.WordTrace]
  refine ⟨13375559596425431488749629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8917039730950287659166419 13375559596425431488749629)
  ·
    refine ⟨5015834848659536808281111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13375559596425431488749629 5015834848659536808281111)
    ·
      refine ⟨7523752272989305212421667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015834848659536808281111 7523752272989305212421667)
      ·
        refine ⟨11285628409483957818632501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523752272989305212421667 11285628409483957818632501)
        ·
          refine ⟨1058027663389121045496797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11285628409483957818632501 1058027663389121045496797)
          ·
            refine ⟨396760373770920392061299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1058027663389121045496797 396760373770920392061299)
            ·
              refine ⟨595140560656380588091949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396760373770920392061299 595140560656380588091949)
              ·
                refine ⟨223177710246142720534481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595140560656380588091949 223177710246142720534481)
                ·
                  refine ⟨167383282684607040400861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223177710246142720534481 167383282684607040400861)
                  ·
                    rfl

theorem cell20_366725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_366725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366725 prefixEnd_366725 := by exact prefixLift 366725
  have htrace : WordTrace (prefixWord ++ tailWord_366725) baseStart_366725 baseEnd_366725 := by
    simpa [prefixWord, tailWord_366725, baseEnd_366725] using wordTrace_append hprefix tailTrace_366725
  have hstable : (prefixWord ++ tailWord_366725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366725).length < 2 ^ (prefixWord ++ tailWord_366725).sum := by decide
  have hdescent : baseEnd_366725 < baseStart_366725 := by decide
  rcases family_descends (prefixWord ++ tailWord_366725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366756 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_366756 : Nat := 118140960795 + 366756 * 2 ^ 59
def prefixEnd_366756 : Nat := 4983230072969 + 3 ^ 40 * 366756 * 2
def baseEnd_366756 : Nat := 167397431929308710367401

theorem tailTrace_366756 : CollatzResearch.WordTrace tailWord_366756 prefixEnd_366756 167397431929308710367401 := by
  unfold tailWord_366756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688345129656561891564061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8917793506208749188752081 6688345129656561891564061)
  ·
    refine ⟨2508129423621210709336523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6688345129656561891564061 2508129423621210709336523)
    ·
      refine ⟨3762194135431816064004785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508129423621210709336523 3762194135431816064004785)
      ·
        refine ⟨2821645601573862048003589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3762194135431816064004785 2821645601573862048003589)
        ·
          refine ⟨529058550295099134000673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2821645601573862048003589 529058550295099134000673)
          ·
            refine ⟨396793912721324350500505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529058550295099134000673 396793912721324350500505)
            ·
              refine ⟨297595434540993262875379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396793912721324350500505 297595434540993262875379)
              ·
                refine ⟨446393151811489894313069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297595434540993262875379 446393151811489894313069)
                ·
                  refine ⟨167397431929308710367401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446393151811489894313069 167397431929308710367401)
                  ·
                    rfl

theorem cell20_366756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_366756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366756 prefixEnd_366756 := by exact prefixLift 366756
  have htrace : WordTrace (prefixWord ++ tailWord_366756) baseStart_366756 baseEnd_366756 := by
    simpa [prefixWord, tailWord_366756, baseEnd_366756] using wordTrace_append hprefix tailTrace_366756
  have hstable : (prefixWord ++ tailWord_366756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366756).length < 2 ^ (prefixWord ++ tailWord_366756).sum := by decide
  have hdescent : baseEnd_366756 < baseStart_366756 := by decide
  rcases family_descends (prefixWord ++ tailWord_366756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366798 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_366798 : Nat := 118140960795 + 366798 * 2 ^ 59
def prefixEnd_366798 : Nat := 4983230072969 + 3 ^ 40 * 366798 * 2
def baseEnd_366798 : Nat := 167416601873743230967229

theorem tailTrace_366798 : CollatzResearch.WordTrace tailWord_366798 prefixEnd_366798 167416601873743230967229 := by
  unfold tailWord_366798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1672277765645120619519631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8918814750107309970771365 1672277765645120619519631)
  ·
    refine ⟨2508416648467680929279447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1672277765645120619519631 2508416648467680929279447)
    ·
      refine ⟨3762624972701521393919171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508416648467680929279447 3762624972701521393919171)
      ·
        refine ⟨5643937459052282090878757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762624972701521393919171 5643937459052282090878757)
        ·
          refine ⟨1058238273572302892039767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5643937459052282090878757 1058238273572302892039767)
          ·
            refine ⟨1587357410358454338059651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058238273572302892039767 1587357410358454338059651)
            ·
              refine ⟨2381036115537681507089477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587357410358454338059651 2381036115537681507089477)
              ·
                refine ⟨446444271663315282579277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2381036115537681507089477 446444271663315282579277)
                ·
                  refine ⟨167416601873743230967229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446444271663315282579277 167416601873743230967229)
                  ·
                    rfl

theorem cell20_366798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_366798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366798 prefixEnd_366798 := by exact prefixLift 366798
  have htrace : WordTrace (prefixWord ++ tailWord_366798) baseStart_366798 baseEnd_366798 := by
    simpa [prefixWord, tailWord_366798, baseEnd_366798] using wordTrace_append hprefix tailTrace_366798
  have hstable : (prefixWord ++ tailWord_366798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366798).length < 2 ^ (prefixWord ++ tailWord_366798).sum := by decide
  have hdescent : baseEnd_366798 < baseStart_366798 := by decide
  rcases family_descends (prefixWord ++ tailWord_366798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366818 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_366818 : Nat := 118140960795 + 366818 * 2 ^ 59
def prefixEnd_366818 : Nat := 4983230072969 + 3 ^ 40 * 366818 * 2
def baseEnd_366818 : Nat := 167425730418712050300481

theorem tailTrace_366818 : CollatzResearch.WordTrace tailWord_366818 prefixEnd_366818 167425730418712050300481 := by
  unfold tailWord_366818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344737896272127092971277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8919301056725672247923405 3344737896272127092971277)
  ·
    refine ⟨1254276711102047659864229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3344737896272127092971277 1254276711102047659864229)
    ·
      refine ⟨235176883331633936224543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1254276711102047659864229 235176883331633936224543)
      ·
        refine ⟨352765324997450904336815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235176883331633936224543 352765324997450904336815)
        ·
          refine ⟨529147987496176356505223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352765324997450904336815 529147987496176356505223)
          ·
            refine ⟨793721981244264534757835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529147987496176356505223 793721981244264534757835)
            ·
              refine ⟨1190582971866396802136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793721981244264534757835 1190582971866396802136753)
              ·
                refine ⟨892937228899797601602565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190582971866396802136753 892937228899797601602565)
                ·
                  refine ⟨167425730418712050300481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892937228899797601602565 167425730418712050300481)
                  ·
                    rfl

theorem cell20_366818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_366818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366818 prefixEnd_366818 := by exact prefixLift 366818
  have htrace : WordTrace (prefixWord ++ tailWord_366818) baseStart_366818 baseEnd_366818 := by
    simpa [prefixWord, tailWord_366818, baseEnd_366818] using wordTrace_append hprefix tailTrace_366818
  have hstable : (prefixWord ++ tailWord_366818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366818).length < 2 ^ (prefixWord ++ tailWord_366818).sum := by decide
  have hdescent : baseEnd_366818 < baseStart_366818 := by decide
  rcases family_descends (prefixWord ++ tailWord_366818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366833 : List Nat := [1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_366833 : Nat := 118140960795 + 366833 * 2 ^ 59
def prefixEnd_366833 : Nat := 4983230072969 + 3 ^ 40 * 366833 * 2
def baseEnd_366833 : Nat := 55810858942479554933473

theorem tailTrace_366833 : CollatzResearch.WordTrace tailWord_366833 prefixEnd_366833 55810858942479554933473 := by
  unfold tailWord_366833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379498680034165933681153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8919665786689443955787435 13379498680034165933681153)
  ·
    refine ⟨10034624010025624450260865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13379498680034165933681153 10034624010025624450260865)
    ·
      refine ⟨7525968007519218337695649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10034624010025624450260865 7525968007519218337695649)
      ·
        refine ⟨5644476005639413753271737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7525968007519218337695649 5644476005639413753271737)
        ·
          refine ⟨4233357004229560314953803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5644476005639413753271737 4233357004229560314953803)
          ·
            refine ⟨6350035506344340472430705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233357004229560314953803 6350035506344340472430705)
            ·
              refine ⟨4762526629758255354323029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350035506344340472430705 4762526629758255354323029)
              ·
                refine ⟨55810858942479554933473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4762526629758255354323029 55810858942479554933473)
                ·
                  rfl

theorem cell20_366833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_366833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366833 prefixEnd_366833 := by exact prefixLift 366833
  have htrace : WordTrace (prefixWord ++ tailWord_366833) baseStart_366833 baseEnd_366833 := by
    simpa [prefixWord, tailWord_366833, baseEnd_366833] using wordTrace_append hprefix tailTrace_366833
  have hstable : (prefixWord ++ tailWord_366833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366833).length < 2 ^ (prefixWord ++ tailWord_366833).sum := by decide
  have hdescent : baseEnd_366833 < baseStart_366833 := by decide
  rcases family_descends (prefixWord ++ tailWord_366833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366857 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_366857 : Nat := 118140960795 + 366857 * 2 ^ 59
def prefixEnd_366857 : Nat := 4983230072969 + 3 ^ 40 * 366857 * 2
def baseEnd_366857 : Nat := 167443531081401248000321

theorem tailTrace_366857 : CollatzResearch.WordTrace tailWord_366857 prefixEnd_366857 167443531081401248000321 := by
  unfold tailWord_366857
  simp only [CollatzResearch.WordTrace]
  refine ⟨13380374031947218032554825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8920249354631478688369883 13380374031947218032554825)
  ·
    refine ⟨10035280523960413524416119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13380374031947218032554825 10035280523960413524416119)
    ·
      refine ⟨15052920785940620286624179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10035280523960413524416119 15052920785940620286624179)
      ·
        refine ⟨22579381178910930429936269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15052920785940620286624179 22579381178910930429936269)
        ·
          refine ⟨8467267942091598911226101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22579381178910930429936269 8467267942091598911226101)
          ·
            refine ⟨793806369571087397927447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8467267942091598911226101 793806369571087397927447)
            ·
              refine ⟨1190709554356631096891171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793806369571087397927447 1190709554356631096891171)
              ·
                refine ⟨1786064331534946645336757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190709554356631096891171 1786064331534946645336757)
                ·
                  refine ⟨167443531081401248000321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1786064331534946645336757 167443531081401248000321)
                  ·
                    rfl

theorem cell20_366857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_366857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366857 prefixEnd_366857 := by exact prefixLift 366857
  have htrace : WordTrace (prefixWord ++ tailWord_366857) baseStart_366857 baseEnd_366857 := by
    simpa [prefixWord, tailWord_366857, baseEnd_366857] using wordTrace_append hprefix tailTrace_366857
  have hstable : (prefixWord ++ tailWord_366857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366857).length < 2 ^ (prefixWord ++ tailWord_366857).sum := by decide
  have hdescent : baseEnd_366857 < baseStart_366857 := by decide
  rcases family_descends (prefixWord ++ tailWord_366857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366929 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 3]
def baseStart_366929 : Nat := 118140960795 + 366929 * 2 ^ 59
def prefixEnd_366929 : Nat := 4983230072969 + 3 ^ 40 * 366929 * 2
def baseEnd_366929 : Nat := 167476393843288997600027

theorem tailTrace_366929 : CollatzResearch.WordTrace tailWord_366929 prefixEnd_366929 167476393843288997600027 := by
  unfold tailWord_366929
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383000087686374329175841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8922000058457582886117227 13383000087686374329175841)
  ·
    refine ⟨10037250065764780746881881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13383000087686374329175841 10037250065764780746881881)
    ·
      refine ⟨7527937549323585560161411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10037250065764780746881881 7527937549323585560161411)
      ·
        refine ⟨11291906323985378340242117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527937549323585560161411 11291906323985378340242117)
        ·
          refine ⟨2117232435747258438795397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11291906323985378340242117 2117232435747258438795397)
          ·
            refine ⟨396981081702610957274137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2117232435747258438795397 396981081702610957274137)
            ·
              refine ⟨297735811276958217955603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396981081702610957274137 297735811276958217955603)
              ·
                refine ⟨446603716915437326933405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297735811276958217955603 446603716915437326933405)
                ·
                  refine ⟨167476393843288997600027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446603716915437326933405 167476393843288997600027)
                  ·
                    rfl

theorem cell20_366929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_366929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366929 prefixEnd_366929 := by exact prefixLift 366929
  have htrace : WordTrace (prefixWord ++ tailWord_366929) baseStart_366929 baseEnd_366929 := by
    simpa [prefixWord, tailWord_366929, baseEnd_366929] using wordTrace_append hprefix tailTrace_366929
  have hstable : (prefixWord ++ tailWord_366929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366929).length < 2 ^ (prefixWord ++ tailWord_366929).sum := by decide
  have hdescent : baseEnd_366929 < baseStart_366929 := by decide
  rcases family_descends (prefixWord ++ tailWord_366929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366947 : List Nat := [1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_366947 : Nat := 118140960795 + 366947 * 2 ^ 59
def prefixEnd_366947 : Nat := 4983230072969 + 3 ^ 40 * 366947 * 2
def baseEnd_366947 : Nat := 55828203177920311666651

theorem tailTrace_366947 : CollatzResearch.WordTrace tailWord_366947 prefixEnd_366947 55828203177920311666651 := by
  unfold tailWord_366947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383656601621163403331095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8922437734414108935554063 13383656601621163403331095)
  ·
    refine ⟨20075484902431745104996643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13383656601621163403331095 20075484902431745104996643)
    ·
      refine ⟨30113227353647617657494965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20075484902431745104996643 30113227353647617657494965)
      ·
        refine ⟨2823115064404464155390153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30113227353647617657494965 2823115064404464155390153)
        ·
          refine ⟨2117336298303348116542615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2823115064404464155390153 2117336298303348116542615)
          ·
            refine ⟨3176004447455022174813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117336298303348116542615 3176004447455022174813923)
            ·
              refine ⟨4764006671182533262220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176004447455022174813923 4764006671182533262220885)
              ·
                refine ⟨55828203177920311666651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4764006671182533262220885 55828203177920311666651)
                ·
                  rfl

theorem cell20_366947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_366947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366947 prefixEnd_366947 := by exact prefixLift 366947
  have htrace : WordTrace (prefixWord ++ tailWord_366947) baseStart_366947 baseEnd_366947 := by
    simpa [prefixWord, tailWord_366947, baseEnd_366947] using wordTrace_append hprefix tailTrace_366947
  have hstable : (prefixWord ++ tailWord_366947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366947).length < 2 ^ (prefixWord ++ tailWord_366947).sum := by decide
  have hdescent : baseEnd_366947 < baseStart_366947 := by decide
  rcases family_descends (prefixWord ++ tailWord_366947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366966 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_366966 : Nat := 118140960795 + 366966 * 2 ^ 59
def prefixEnd_366966 : Nat := 4983230072969 + 3 ^ 40 * 366966 * 2
def baseEnd_366966 : Nat := 167493281651481313366543

theorem tailTrace_366966 : CollatzResearch.WordTrace tailWord_366966 prefixEnd_366966 167493281651481313366543 := by
  unfold tailWord_366966
  simp only [CollatzResearch.WordTrace]
  refine ⟨836521849284520603017047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8922899725701553098848501 836521849284520603017047)
  ·
    refine ⟨1254782773926780904525571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836521849284520603017047 1254782773926780904525571)
    ·
      refine ⟨1882174160890171356788357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254782773926780904525571 1882174160890171356788357)
      ·
        refine ⟨352907655166907129397817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1882174160890171356788357 352907655166907129397817)
        ·
          refine ⟨264680741375180347048363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352907655166907129397817 264680741375180347048363)
          ·
            refine ⟨397021112062770520572545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264680741375180347048363 397021112062770520572545)
            ·
              refine ⟨297765834047077890429409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397021112062770520572545 297765834047077890429409)
              ·
                refine ⟨223324375535308417822057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297765834047077890429409 223324375535308417822057)
                ·
                  refine ⟨167493281651481313366543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223324375535308417822057 167493281651481313366543)
                  ·
                    rfl

theorem cell20_366966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_366966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366966 prefixEnd_366966 := by exact prefixLift 366966
  have htrace : WordTrace (prefixWord ++ tailWord_366966) baseStart_366966 baseEnd_366966 := by
    simpa [prefixWord, tailWord_366966, baseEnd_366966] using wordTrace_append hprefix tailTrace_366966
  have hstable : (prefixWord ++ tailWord_366966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366966).length < 2 ^ (prefixWord ++ tailWord_366966).sum := by decide
  have hdescent : baseEnd_366966 < baseStart_366966 := by decide
  rcases family_descends (prefixWord ++ tailWord_366966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366971 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_366971 : Nat := 118140960795 + 366971 * 2 ^ 59
def prefixEnd_366971 : Nat := 4983230072969 + 3 ^ 40 * 366971 * 2
def baseEnd_366971 : Nat := 167495563787723518199855

theorem tailTrace_366971 : CollatzResearch.WordTrace tailWord_366971 prefixEnd_366971 167495563787723518199855 := by
  unfold tailWord_366971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13384531953534215502204767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8923021302356143668136511 13384531953534215502204767)
  ·
    refine ⟨20076797930301323253307151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13384531953534215502204767 20076797930301323253307151)
    ·
      refine ⟨30115196895451984879960727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20076797930301323253307151 30115196895451984879960727)
      ·
        refine ⟨45172795343177977319941091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30115196895451984879960727 45172795343177977319941091)
        ·
          refine ⟨67759193014766965979911637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45172795343177977319941091 67759193014766965979911637)
          ·
            refine ⟨1588106086283600765154179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67759193014766965979911637 1588106086283600765154179)
            ·
              refine ⟨2382159129425401147731269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588106086283600765154179 2382159129425401147731269)
              ·
                refine ⟨446654836767262715199613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2382159129425401147731269 446654836767262715199613)
                ·
                  refine ⟨167495563787723518199855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446654836767262715199613 167495563787723518199855)
                  ·
                    rfl

theorem cell20_366971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_366971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_366971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_366971 prefixEnd_366971 := by exact prefixLift 366971
  have htrace : WordTrace (prefixWord ++ tailWord_366971) baseStart_366971 baseEnd_366971 := by
    simpa [prefixWord, tailWord_366971, baseEnd_366971] using wordTrace_append hprefix tailTrace_366971
  have hstable : (prefixWord ++ tailWord_366971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366971).length < 2 ^ (prefixWord ++ tailWord_366971).sum := by decide
  have hdescent : baseEnd_366971 < baseStart_366971 := by decide
  rcases family_descends (prefixWord ++ tailWord_366971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367018 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_367018 : Nat := 118140960795 + 367018 * 2 ^ 59
def prefixEnd_367018 : Nat := 4983230072969 + 3 ^ 40 * 367018 * 2
def baseEnd_367018 : Nat := 167517015868400243632997

theorem tailTrace_367018 : CollatzResearch.WordTrace tailWord_367018 prefixEnd_367018 167517015868400243632997 := by
  unfold tailWord_367018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346561546090985632291427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8924164122909295019443805 3346561546090985632291427)
  ·
    refine ⟨5019842319136478448437141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346561546090985632291427 5019842319136478448437141)
    ·
      refine ⟨235305108709522427270491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5019842319136478448437141 235305108709522427270491)
      ·
        refine ⟨352957663064283640905737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235305108709522427270491 352957663064283640905737)
        ·
          refine ⟨264718247298212730679303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352957663064283640905737 264718247298212730679303)
          ·
            refine ⟨397077370947319096018955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264718247298212730679303 397077370947319096018955)
            ·
              refine ⟨595616056420978644028433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397077370947319096018955 595616056420978644028433)
              ·
                refine ⟨446712042315733983021325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595616056420978644028433 446712042315733983021325)
                ·
                  refine ⟨167517015868400243632997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446712042315733983021325 167517015868400243632997)
                  ·
                    rfl

theorem cell20_367018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_367018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367018 prefixEnd_367018 := by exact prefixLift 367018
  have htrace : WordTrace (prefixWord ++ tailWord_367018) baseStart_367018 baseEnd_367018 := by
    simpa [prefixWord, tailWord_367018, baseEnd_367018] using wordTrace_append hprefix tailTrace_367018
  have hstable : (prefixWord ++ tailWord_367018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367018).length < 2 ^ (prefixWord ++ tailWord_367018).sum := by decide
  have hdescent : baseEnd_367018 < baseStart_367018 := by decide
  rcases family_descends (prefixWord ++ tailWord_367018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367033 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_367033 : Nat := 118140960795 + 367033 * 2 ^ 59
def prefixEnd_367033 : Nat := 4983230072969 + 3 ^ 40 * 367033 * 2
def baseEnd_367033 : Nat := 167523862277126858132935

theorem tailTrace_367033 : CollatzResearch.WordTrace tailWord_367033 prefixEnd_367033 167523862277126858132935 := by
  unfold tailWord_367033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386793279309600090961753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8924528852873066727307835 13386793279309600090961753)
  ·
    refine ⟨10040094959482200068221315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386793279309600090961753 10040094959482200068221315)
    ·
      refine ⟨15060142439223300102331973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040094959482200068221315 15060142439223300102331973)
      ·
        refine ⟨2823776707354368769187245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15060142439223300102331973 2823776707354368769187245)
        ·
          refine ⟨1058916265257888288445217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2823776707354368769187245 1058916265257888288445217)
          ·
            refine ⟨794187198943416216333913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058916265257888288445217 794187198943416216333913)
            ·
              refine ⟨595640399207562162250435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794187198943416216333913 595640399207562162250435)
              ·
                refine ⟨893460598811343243375653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595640399207562162250435 893460598811343243375653)
                ·
                  refine ⟨167523862277126858132935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893460598811343243375653 167523862277126858132935)
                  ·
                    rfl

theorem cell20_367033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_367033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367033 prefixEnd_367033 := by exact prefixLift 367033
  have htrace : WordTrace (prefixWord ++ tailWord_367033) baseStart_367033 baseEnd_367033 := by
    simpa [prefixWord, tailWord_367033, baseEnd_367033] using wordTrace_append hprefix tailTrace_367033
  have hstable : (prefixWord ++ tailWord_367033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367033).length < 2 ^ (prefixWord ++ tailWord_367033).sum := by decide
  have hdescent : baseEnd_367033 < baseStart_367033 := by decide
  rcases family_descends (prefixWord ++ tailWord_367033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367074 : List Nat := [3, 3, 3, 2, 1, 2, 6]
def baseStart_367074 : Nat := 118140960795 + 367074 * 2 ^ 59
def prefixEnd_367074 : Nat := 4983230072969 + 3 ^ 40 * 367074 * 2
def baseEnd_367074 : Nat := 18615841754923659751789

theorem tailTrace_367074 : CollatzResearch.WordTrace tailWord_367074 prefixEnd_367074 18615841754923659751789 := by
  unfold tailWord_367074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347072168040266023301069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8925525781440709395469517 3347072168040266023301069)
  ·
    refine ⟨1255152063015099758737901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3347072168040266023301069 1255152063015099758737901)
    ·
      refine ⟨470682023630662409526713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1255152063015099758737901 470682023630662409526713)
      ·
        refine ⟨353011517722996807145035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470682023630662409526713 353011517722996807145035)
        ·
          refine ⟨529517276584495210717553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353011517722996807145035 529517276584495210717553)
          ·
            refine ⟨397137957438371408038165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529517276584495210717553 397137957438371408038165)
            ·
              refine ⟨18615841754923659751789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 397137957438371408038165 18615841754923659751789)
              ·
                rfl

theorem cell20_367074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_367074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367074 prefixEnd_367074 := by exact prefixLift 367074
  have htrace : WordTrace (prefixWord ++ tailWord_367074) baseStart_367074 baseEnd_367074 := by
    simpa [prefixWord, tailWord_367074, baseEnd_367074] using wordTrace_append hprefix tailTrace_367074
  have hstable : (prefixWord ++ tailWord_367074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367074).length < 2 ^ (prefixWord ++ tailWord_367074).sum := by decide
  have hdescent : baseEnd_367074 < baseStart_367074 := by decide
  rcases family_descends (prefixWord ++ tailWord_367074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367088 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_367088 : Nat := 118140960795 + 367088 * 2 ^ 59
def prefixEnd_367088 : Nat := 4983230072969 + 3 ^ 40 * 367088 * 2
def baseEnd_367088 : Nat := 167548965775791111299377

theorem tailTrace_367088 : CollatzResearch.WordTrace tailWord_367088 prefixEnd_367088 167548965775791111299377 := by
  unfold tailWord_367088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694399647055172242106959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8925866196073562989475945 6694399647055172242106959)
  ·
    refine ⟨10041599470582758363160439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6694399647055172242106959 10041599470582758363160439)
    ·
      refine ⟨15062399205874137544740659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10041599470582758363160439 15062399205874137544740659)
      ·
        refine ⟨22593598808811206317110989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15062399205874137544740659 22593598808811206317110989)
        ·
          refine ⟨8472599553304202368916621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22593598808811206317110989 8472599553304202368916621)
          ·
            refine ⟨3177224832489075888343733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8472599553304202368916621 3177224832489075888343733)
            ·
              refine ⟨297864828045850864532225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3177224832489075888343733 297864828045850864532225)
              ·
                refine ⟨223398621034388148399169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297864828045850864532225 223398621034388148399169)
                ·
                  refine ⟨167548965775791111299377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223398621034388148399169 167548965775791111299377)
                  ·
                    rfl

theorem cell20_367088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_367088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367088 prefixEnd_367088 := by exact prefixLift 367088
  have htrace : WordTrace (prefixWord ++ tailWord_367088) baseStart_367088 baseEnd_367088 := by
    simpa [prefixWord, tailWord_367088, baseEnd_367088] using wordTrace_append hprefix tailTrace_367088
  have hstable : (prefixWord ++ tailWord_367088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367088).length < 2 ^ (prefixWord ++ tailWord_367088).sum := by decide
  have hdescent : baseEnd_367088 < baseStart_367088 := by decide
  rcases family_descends (prefixWord ++ tailWord_367088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367150 : List Nat := [4, 1, 3, 1, 4, 1, 1, 5]
def baseStart_367150 : Nat := 118140960795 + 367150 * 2 ^ 59
def prefixEnd_367150 : Nat := 4983230072969 + 3 ^ 40 * 367150 * 2
def baseEnd_367150 : Nat := 55859088088398150410819

theorem tailTrace_367150 : CollatzResearch.WordTrace tailWord_367150 prefixEnd_367150 55859088088398150410819 := by
  unfold tailWord_367150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673882577485716134121363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8927373746590486048647269 1673882577485716134121363)
  ·
    refine ⟨2510823866228574201182045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673882577485716134121363 2510823866228574201182045)
    ·
      refine ⟨941558949835715325443267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2510823866228574201182045 941558949835715325443267)
      ·
        refine ⟨1412338424753572988164901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941558949835715325443267 1412338424753572988164901)
        ·
          refine ⟨264813454641294935280919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1412338424753572988164901 264813454641294935280919)
          ·
            refine ⟨397220181961942402921379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264813454641294935280919 397220181961942402921379)
            ·
              refine ⟨595830272942913604382069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397220181961942402921379 595830272942913604382069)
              ·
                refine ⟨55859088088398150410819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 595830272942913604382069 55859088088398150410819)
                ·
                  rfl

theorem cell20_367150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_367150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367150 prefixEnd_367150 := by exact prefixLift 367150
  have htrace : WordTrace (prefixWord ++ tailWord_367150) baseStart_367150 baseEnd_367150 := by
    simpa [prefixWord, tailWord_367150, baseEnd_367150] using wordTrace_append hprefix tailTrace_367150
  have hstable : (prefixWord ++ tailWord_367150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367150).length < 2 ^ (prefixWord ++ tailWord_367150).sum := by decide
  have hdescent : baseEnd_367150 < baseStart_367150 := by decide
  rcases family_descends (prefixWord ++ tailWord_367150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367151 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_367151 : Nat := 118140960795 + 367151 * 2 ^ 59
def prefixEnd_367151 : Nat := 4983230072969 + 3 ^ 40 * 367151 * 2
def baseEnd_367151 : Nat := 167577720692442892199119

theorem tailTrace_367151 : CollatzResearch.WordTrace tailWord_367151 prefixEnd_367151 167577720692442892199119 := by
  unfold tailWord_367151
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391097092882106243757307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8927398061921404162504871 13391097092882106243757307)
  ·
    refine ⟨20086645639323159365635961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13391097092882106243757307 20086645639323159365635961)
    ·
      refine ⟨15064984229492369524226971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086645639323159365635961 15064984229492369524226971)
      ·
        refine ⟨22597476344238554286340457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15064984229492369524226971 22597476344238554286340457)
        ·
          refine ⟨16948107258178915714755343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22597476344238554286340457 16948107258178915714755343)
          ·
            refine ⟨25422160887268373572133015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948107258178915714755343 25422160887268373572133015)
            ·
              refine ⟨38133241330902560358199523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25422160887268373572133015 38133241330902560358199523)
              ·
                refine ⟨57199861996353840537299285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38133241330902560358199523 57199861996353840537299285)
                ·
                  refine ⟨167577720692442892199119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57199861996353840537299285 167577720692442892199119)
                  ·
                    rfl

theorem cell20_367151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_367151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367151 prefixEnd_367151 := by exact prefixLift 367151
  have htrace : WordTrace (prefixWord ++ tailWord_367151) baseStart_367151 baseEnd_367151 := by
    simpa [prefixWord, tailWord_367151, baseEnd_367151] using wordTrace_append hprefix tailTrace_367151
  have hstable : (prefixWord ++ tailWord_367151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367151).length < 2 ^ (prefixWord ++ tailWord_367151).sum := by decide
  have hdescent : baseEnd_367151 < baseStart_367151 := by decide
  rcases family_descends (prefixWord ++ tailWord_367151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367161 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_367161 : Nat := 118140960795 + 367161 * 2 ^ 59
def prefixEnd_367161 : Nat := 4983230072969 + 3 ^ 40 * 367161 * 2
def baseEnd_367161 : Nat := 167582284964927301865745

theorem tailTrace_367161 : CollatzResearch.WordTrace tailWord_367161 prefixEnd_367161 167582284964927301865745 := by
  unfold tailWord_367161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391461822845877951621337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8927641215230585301080891 13391461822845877951621337)
  ·
    refine ⟨10043596367134408463716003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13391461822845877951621337 10043596367134408463716003)
    ·
      refine ⟨15065394550701612695574005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10043596367134408463716003 15065394550701612695574005)
      ·
        refine ⟨1412380739128276190210063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15065394550701612695574005 1412380739128276190210063)
        ·
          refine ⟨2118571108692414285315095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412380739128276190210063 2118571108692414285315095)
          ·
            refine ⟨3177856663038621427972643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118571108692414285315095 3177856663038621427972643)
            ·
              refine ⟨4766784994557932141958965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177856663038621427972643 4766784994557932141958965)
              ·
                refine ⟨446886093239806138308653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4766784994557932141958965 446886093239806138308653)
                ·
                  refine ⟨167582284964927301865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446886093239806138308653 167582284964927301865745)
                  ·
                    rfl

theorem cell20_367161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_367161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367161 prefixEnd_367161 := by exact prefixLift 367161
  have htrace : WordTrace (prefixWord ++ tailWord_367161) baseStart_367161 baseEnd_367161 := by
    simpa [prefixWord, tailWord_367161, baseEnd_367161] using wordTrace_append hprefix tailTrace_367161
  have hstable : (prefixWord ++ tailWord_367161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367161).length < 2 ^ (prefixWord ++ tailWord_367161).sum := by decide
  have hdescent : baseEnd_367161 < baseStart_367161 := by decide
  rcases family_descends (prefixWord ++ tailWord_367161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367181 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 2]
def baseStart_367181 : Nat := 118140960795 + 367181 * 2 ^ 59
def prefixEnd_367181 : Nat := 4983230072969 + 3 ^ 40 * 367181 * 2
def baseEnd_367181 : Nat := 167591413509896121198997

theorem tailTrace_367181 : CollatzResearch.WordTrace tailWord_367181 prefixEnd_367181 167591413509896121198997 := by
  unfold tailWord_367181
  simp only [CollatzResearch.WordTrace]
  refine ⟨13392191282773421367349397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8928127521848947578232931 13392191282773421367349397)
  ·
    refine ⟨627758966380004126594503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13392191282773421367349397 627758966380004126594503)
    ·
      refine ⟨941638449570006189891755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627758966380004126594503 941638449570006189891755)
      ·
        refine ⟨1412457674355009284837633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941638449570006189891755 1412457674355009284837633)
        ·
          refine ⟨1059343255766256963628225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412457674355009284837633 1059343255766256963628225)
          ·
            refine ⟨794507441824692722721169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059343255766256963628225 794507441824692722721169)
            ·
              refine ⟨595880581368519542040877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794507441824692722721169 595880581368519542040877)
              ·
                refine ⟨223455218013194828265329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595880581368519542040877 223455218013194828265329)
                ·
                  refine ⟨167591413509896121198997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223455218013194828265329 167591413509896121198997)
                  ·
                    rfl

theorem cell20_367181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_367181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367181 prefixEnd_367181 := by exact prefixLift 367181
  have htrace : WordTrace (prefixWord ++ tailWord_367181) baseStart_367181 baseEnd_367181 := by
    simpa [prefixWord, tailWord_367181, baseEnd_367181] using wordTrace_append hprefix tailTrace_367181
  have hstable : (prefixWord ++ tailWord_367181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367181).length < 2 ^ (prefixWord ++ tailWord_367181).sum := by decide
  have hdescent : baseEnd_367181 < baseStart_367181 := by decide
  rcases family_descends (prefixWord ++ tailWord_367181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367185 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 2]
def baseStart_367185 : Nat := 118140960795 + 367185 * 2 ^ 59
def prefixEnd_367185 : Nat := 4983230072969 + 3 ^ 40 * 367185 * 2
def baseEnd_367185 : Nat := 167593239218889885065647

theorem tailTrace_367185 : CollatzResearch.WordTrace tailWord_367185 prefixEnd_367185 167593239218889885065647 := by
  unfold tailWord_367185
  simp only [CollatzResearch.WordTrace]
  refine ⟨13392337174758930050495009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8928224783172620033663339 13392337174758930050495009)
  ·
    refine ⟨10044252881069197537871257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13392337174758930050495009 10044252881069197537871257)
    ·
      refine ⟨7533189660801898153403443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10044252881069197537871257 7533189660801898153403443)
      ·
        refine ⟨11299784491202847230105165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533189660801898153403443 11299784491202847230105165)
        ·
          refine ⟨4237419184201067711289437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11299784491202847230105165 4237419184201067711289437)
          ·
            refine ⟨1589032194075400391733539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4237419184201067711289437 1589032194075400391733539)
            ·
              refine ⟨2383548291113100587600309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589032194075400391733539 2383548291113100587600309)
              ·
                refine ⟨223457652291853180087529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2383548291113100587600309 223457652291853180087529)
                ·
                  refine ⟨167593239218889885065647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223457652291853180087529 167593239218889885065647)
                  ·
                    rfl

theorem cell20_367185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_367185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367185 prefixEnd_367185 := by exact prefixLift 367185
  have htrace : WordTrace (prefixWord ++ tailWord_367185) baseStart_367185 baseEnd_367185 := by
    simpa [prefixWord, tailWord_367185, baseEnd_367185] using wordTrace_append hprefix tailTrace_367185
  have hstable : (prefixWord ++ tailWord_367185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367185).length < 2 ^ (prefixWord ++ tailWord_367185).sum := by decide
  have hdescent : baseEnd_367185 < baseStart_367185 := by decide
  rcases family_descends (prefixWord ++ tailWord_367185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367198 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_367198 : Nat := 118140960795 + 367198 * 2 ^ 59
def prefixEnd_367198 : Nat := 4983230072969 + 3 ^ 40 * 367198 * 2
def baseEnd_367198 : Nat := 167599172773119617632261

theorem tailTrace_367198 : CollatzResearch.WordTrace tailWord_367198 prefixEnd_367198 167599172773119617632261 := by
  unfold tailWord_367198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674101415463979158839781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8928540882474555513812165 1674101415463979158839781)
  ·
    refine ⟨313894015399496092282459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1674101415463979158839781 313894015399496092282459)
    ·
      refine ⟨470841023099244138423689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313894015399496092282459 470841023099244138423689)
      ·
        refine ⟨353130767324433103817767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470841023099244138423689 353130767324433103817767)
        ·
          refine ⟨529696150986649655726651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353130767324433103817767 529696150986649655726651)
          ·
            refine ⟨794544226479974483589977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529696150986649655726651 794544226479974483589977)
            ·
              refine ⟨595908169859980862692483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794544226479974483589977 595908169859980862692483)
              ·
                refine ⟨893862254789971294038725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595908169859980862692483 893862254789971294038725)
                ·
                  refine ⟨167599172773119617632261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893862254789971294038725 167599172773119617632261)
                  ·
                    rfl

theorem cell20_367198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_367198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367198 prefixEnd_367198 := by exact prefixLift 367198
  have htrace : WordTrace (prefixWord ++ tailWord_367198) baseStart_367198 baseEnd_367198 := by
    simpa [prefixWord, tailWord_367198, baseEnd_367198] using wordTrace_append hprefix tailTrace_367198
  have hstable : (prefixWord ++ tailWord_367198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367198).length < 2 ^ (prefixWord ++ tailWord_367198).sum := by decide
  have hdescent : baseEnd_367198 < baseStart_367198 := by decide
  rcases family_descends (prefixWord ++ tailWord_367198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367227 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_367227 : Nat := 118140960795 + 367227 * 2 ^ 59
def prefixEnd_367227 : Nat := 4983230072969 + 3 ^ 40 * 367227 * 2
def baseEnd_367227 : Nat := 167612409163324405665475

theorem tailTrace_367227 : CollatzResearch.WordTrace tailWord_367227 prefixEnd_367227 167612409163324405665475 := by
  unfold tailWord_367227
  simp only [CollatzResearch.WordTrace]
  refine ⟨13393869040606771223523935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8929246027071180815682623 13393869040606771223523935)
  ·
    refine ⟨20090803560910156835285903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13393869040606771223523935 20090803560910156835285903)
    ·
      refine ⟨30136205341365235252928855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090803560910156835285903 30136205341365235252928855)
      ·
        refine ⟨45204308012047852879393283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30136205341365235252928855 45204308012047852879393283)
        ·
          refine ⟨67806462018071779319089925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45204308012047852879393283 67806462018071779319089925)
          ·
            refine ⟨12713711628388458622329361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67806462018071779319089925 12713711628388458622329361)
            ·
              refine ⟨9535283721291343966747021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12713711628388458622329361 9535283721291343966747021)
              ·
                refine ⟨3575731395484253987530133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9535283721291343966747021 3575731395484253987530133)
                ·
                  refine ⟨167612409163324405665475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3575731395484253987530133 167612409163324405665475)
                  ·
                    rfl

theorem cell20_367227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_367227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367227 prefixEnd_367227 := by exact prefixLift 367227
  have htrace : WordTrace (prefixWord ++ tailWord_367227) baseStart_367227 baseEnd_367227 := by
    simpa [prefixWord, tailWord_367227, baseEnd_367227] using wordTrace_append hprefix tailTrace_367227
  have hstable : (prefixWord ++ tailWord_367227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367227).length < 2 ^ (prefixWord ++ tailWord_367227).sum := by decide
  have hdescent : baseEnd_367227 < baseStart_367227 := by decide
  rcases family_descends (prefixWord ++ tailWord_367227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367261 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 2]
def baseStart_367261 : Nat := 118140960795 + 367261 * 2 ^ 59
def prefixEnd_367261 : Nat := 4983230072969 + 3 ^ 40 * 367261 * 2
def baseEnd_367261 : Nat := 167627927689771398532003

theorem tailTrace_367261 : CollatzResearch.WordTrace tailWord_367261 prefixEnd_367261 167627927689771398532003 := by
  unfold tailWord_367261
  simp only [CollatzResearch.WordTrace]
  refine ⟨13395109122483595030261637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8930072748322396686841091 13395109122483595030261637)
  ·
    refine ⟨2511582960465674068174057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13395109122483595030261637 2511582960465674068174057)
    ·
      refine ⟨1883687220349255551130543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2511582960465674068174057 1883687220349255551130543)
      ·
        refine ⟨2825530830523883326695815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883687220349255551130543 2825530830523883326695815)
        ·
          refine ⟨4238296245785824990043723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825530830523883326695815 4238296245785824990043723)
          ·
            refine ⟨6357444368678737485065585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238296245785824990043723 6357444368678737485065585)
            ·
              refine ⟨4768083276509053113799189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6357444368678737485065585 4768083276509053113799189)
              ·
                refine ⟨223503903586361864709337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4768083276509053113799189 223503903586361864709337)
                ·
                  refine ⟨167627927689771398532003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223503903586361864709337 167627927689771398532003)
                  ·
                    rfl

theorem cell20_367261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_367261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367261 prefixEnd_367261 := by exact prefixLift 367261
  have htrace : WordTrace (prefixWord ++ tailWord_367261) baseStart_367261 baseEnd_367261 := by
    simpa [prefixWord, tailWord_367261, baseEnd_367261] using wordTrace_append hprefix tailTrace_367261
  have hstable : (prefixWord ++ tailWord_367261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367261).length < 2 ^ (prefixWord ++ tailWord_367261).sum := by decide
  have hdescent : baseEnd_367261 < baseStart_367261 := by decide
  rcases family_descends (prefixWord ++ tailWord_367261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367271 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_367271 : Nat := 118140960795 + 367271 * 2 ^ 59
def prefixEnd_367271 : Nat := 4983230072969 + 3 ^ 40 * 367271 * 2
def baseEnd_367271 : Nat := 167632491962255808198629

theorem tailTrace_367271 : CollatzResearch.WordTrace tailWord_367271 prefixEnd_367271 167632491962255808198629 := by
  unfold tailWord_367271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13395473852447366738125667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8930315901631577825417111 13395473852447366738125667)
  ·
    refine ⟨20093210778671050107188501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13395473852447366738125667 20093210778671050107188501)
    ·
      refine ⟨941869255250205473774461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20093210778671050107188501 941869255250205473774461)
      ·
        refine ⟨353200970718827052665423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 941869255250205473774461 353200970718827052665423)
        ·
          refine ⟨529801456078240578998135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353200970718827052665423 529801456078240578998135)
          ·
            refine ⟨794702184117360868497203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529801456078240578998135 794702184117360868497203)
            ·
              refine ⟨1192053276176041302745805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794702184117360868497203 1192053276176041302745805)
              ·
                refine ⟨447019978566015488529677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192053276176041302745805 447019978566015488529677)
                ·
                  refine ⟨167632491962255808198629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447019978566015488529677 167632491962255808198629)
                  ·
                    rfl

theorem cell20_367271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_367271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367271 prefixEnd_367271 := by exact prefixLift 367271
  have htrace : WordTrace (prefixWord ++ tailWord_367271) baseStart_367271 baseEnd_367271 := by
    simpa [prefixWord, tailWord_367271, baseEnd_367271] using wordTrace_append hprefix tailTrace_367271
  have hstable : (prefixWord ++ tailWord_367271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367271).length < 2 ^ (prefixWord ++ tailWord_367271).sum := by decide
  have hdescent : baseEnd_367271 < baseStart_367271 := by decide
  rcases family_descends (prefixWord ++ tailWord_367271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367302 : List Nat := [6, 1, 2, 1, 3, 7]
def baseStart_367302 : Nat := 118140960795 + 367302 * 2 ^ 59
def prefixEnd_367302 : Nat := 4983230072969 + 3 ^ 40 * 367302 * 2
def baseEnd_367302 : Nat := 6209134859516943635747

theorem tailTrace_367302 : CollatzResearch.WordTrace tailWord_367302 prefixEnd_367302 6209134859516943635747 := by
  unfold tailWord_367302
  simp only [CollatzResearch.WordTrace]
  refine ⟨418643891104220594765755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8931069676890039355002773 418643891104220594765755)
  ·
    refine ⟨627965836656330892148633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 418643891104220594765755 627965836656330892148633)
    ·
      refine ⟨470974377492248169111475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627965836656330892148633 470974377492248169111475)
      ·
        refine ⟨706461566238372253667213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470974377492248169111475 706461566238372253667213)
        ·
          refine ⟨264923087339389595125205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 706461566238372253667213 264923087339389595125205)
          ·
            refine ⟨6209134859516943635747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 264923087339389595125205 6209134859516943635747)
            ·
              rfl

theorem cell20_367302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 7].length) (baseStart_367302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367302 prefixEnd_367302 := by exact prefixLift 367302
  have htrace : WordTrace (prefixWord ++ tailWord_367302) baseStart_367302 baseEnd_367302 := by
    simpa [prefixWord, tailWord_367302, baseEnd_367302] using wordTrace_append hprefix tailTrace_367302
  have hstable : (prefixWord ++ tailWord_367302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367302).length < 2 ^ (prefixWord ++ tailWord_367302).sum := by decide
  have hdescent : baseEnd_367302 < baseStart_367302 := by decide
  rcases family_descends (prefixWord ++ tailWord_367302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367303 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_367303 : Nat := 118140960795 + 367303 * 2 ^ 59
def prefixEnd_367303 : Nat := 4983230072969 + 3 ^ 40 * 367303 * 2
def baseEnd_367303 : Nat := 167647097634205919131831

theorem tailTrace_367303 : CollatzResearch.WordTrace tailWord_367303 prefixEnd_367303 167647097634205919131831 := by
  unfold tailWord_367303
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396640988331436203290563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8931093992220957468860375 13396640988331436203290563)
  ·
    refine ⟨20094961482497154304935845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13396640988331436203290563 20094961482497154304935845)
    ·
      refine ⟨3767805277968216432175471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20094961482497154304935845 3767805277968216432175471)
      ·
        refine ⟨5651707916952324648263207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3767805277968216432175471 5651707916952324648263207)
        ·
          refine ⟨8477561875428486972394811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5651707916952324648263207 8477561875428486972394811)
          ·
            refine ⟨12716342813142730458592217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477561875428486972394811 12716342813142730458592217)
            ·
              refine ⟨9537257109857047843944163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12716342813142730458592217 9537257109857047843944163)
              ·
                refine ⟨14305885664785571765916245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9537257109857047843944163 14305885664785571765916245)
                ·
                  refine ⟨167647097634205919131831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14305885664785571765916245 167647097634205919131831)
                  ·
                    rfl

theorem cell20_367303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_367303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367303 prefixEnd_367303 := by exact prefixLift 367303
  have htrace : WordTrace (prefixWord ++ tailWord_367303) baseStart_367303 baseEnd_367303 := by
    simpa [prefixWord, tailWord_367303, baseEnd_367303] using wordTrace_append hprefix tailTrace_367303
  have hstable : (prefixWord ++ tailWord_367303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367303).length < 2 ^ (prefixWord ++ tailWord_367303).sum := by decide
  have hdescent : baseEnd_367303 < baseStart_367303 := by decide
  rcases family_descends (prefixWord ++ tailWord_367303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367313 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_367313 : Nat := 118140960795 + 367313 * 2 ^ 59
def prefixEnd_367313 : Nat := 4983230072969 + 3 ^ 40 * 367313 * 2
def baseEnd_367313 : Nat := 167651661906690328798457

theorem tailTrace_367313 : CollatzResearch.WordTrace tailWord_367313 prefixEnd_367313 167651661906690328798457 := by
  unfold tailWord_367313
  simp only [CollatzResearch.WordTrace]
  refine ⟨13397005718295207911154593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8931337145530138607436395 13397005718295207911154593)
  ·
    refine ⟨10047754288721405933365945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13397005718295207911154593 10047754288721405933365945)
    ·
      refine ⟨7535815716541054450024459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10047754288721405933365945 7535815716541054450024459)
      ·
        refine ⟨11303723574811581675036689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7535815716541054450024459 11303723574811581675036689)
        ·
          refine ⟨8477792681108686256277517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303723574811581675036689 8477792681108686256277517)
          ·
            refine ⟨3179172255415757346104069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8477792681108686256277517 3179172255415757346104069)
            ·
              refine ⟨596094797890454502394513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3179172255415757346104069 596094797890454502394513)
              ·
                refine ⟨447071098417840876795885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596094797890454502394513 447071098417840876795885)
                ·
                  refine ⟨167651661906690328798457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447071098417840876795885 167651661906690328798457)
                  ·
                    rfl

theorem cell20_367313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_367313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367313 prefixEnd_367313 := by exact prefixLift 367313
  have htrace : WordTrace (prefixWord ++ tailWord_367313) baseStart_367313 baseEnd_367313 := by
    simpa [prefixWord, tailWord_367313, baseEnd_367313] using wordTrace_append hprefix tailTrace_367313
  have hstable : (prefixWord ++ tailWord_367313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367313).length < 2 ^ (prefixWord ++ tailWord_367313).sum := by decide
  have hdescent : baseEnd_367313 < baseStart_367313 := by decide
  rcases family_descends (prefixWord ++ tailWord_367313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367327 : List Nat := [1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_367327 : Nat := 118140960795 + 367327 * 2 ^ 59
def prefixEnd_367327 : Nat := 4983230072969 + 3 ^ 40 * 367327 * 2
def baseEnd_367327 : Nat := 55886017296056167443911

theorem tailTrace_367327 : CollatzResearch.WordTrace tailWord_367327 prefixEnd_367327 55886017296056167443911 := by
  unfold tailWord_367327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13397516340244488302164235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8931677560162992201442823 13397516340244488302164235)
  ·
    refine ⟨20096274510366732453246353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13397516340244488302164235 20096274510366732453246353)
    ·
      refine ⟨15072205882775049339934765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20096274510366732453246353 15072205882775049339934765)
      ·
        refine ⟨5652077206040643502475537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15072205882775049339934765 5652077206040643502475537)
        ·
          refine ⟨4239057904530482626856653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5652077206040643502475537 4239057904530482626856653)
          ·
            refine ⟨1589646714198930985071245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4239057904530482626856653 1589646714198930985071245)
            ·
              refine ⟨596117517824599119401717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1589646714198930985071245 596117517824599119401717)
              ·
                refine ⟨55886017296056167443911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596117517824599119401717 55886017296056167443911)
                ·
                  rfl

theorem cell20_367327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_367327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367327 prefixEnd_367327 := by exact prefixLift 367327
  have htrace : WordTrace (prefixWord ++ tailWord_367327) baseStart_367327 baseEnd_367327 := by
    simpa [prefixWord, tailWord_367327, baseEnd_367327] using wordTrace_append hprefix tailTrace_367327
  have hstable : (prefixWord ++ tailWord_367327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367327).length < 2 ^ (prefixWord ++ tailWord_367327).sum := by decide
  have hdescent : baseEnd_367327 < baseStart_367327 := by decide
  rcases family_descends (prefixWord ++ tailWord_367327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367368 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_367368 : Nat := 118140960795 + 367368 * 2 ^ 59
def prefixEnd_367368 : Nat := 4983230072969 + 3 ^ 40 * 367368 * 2
def baseEnd_367368 : Nat := 167676765405354581964899

theorem tailTrace_367368 : CollatzResearch.WordTrace tailWord_367368 prefixEnd_367368 167676765405354581964899 := by
  unfold tailWord_367368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699505866547976152203379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8932674488730634869604505 6699505866547976152203379)
  ·
    refine ⟨10049258799821964228305069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6699505866547976152203379 10049258799821964228305069)
    ·
      refine ⟨3768472049933236585614401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10049258799821964228305069 3768472049933236585614401)
      ·
        refine ⟨2826354037449927439210801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3768472049933236585614401 2826354037449927439210801)
        ·
          refine ⟨2119765528087445579408101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826354037449927439210801 2119765528087445579408101)
          ·
            refine ⟨397456036516396046139019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2119765528087445579408101 397456036516396046139019)
            ·
              refine ⟨596184054774594069208529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397456036516396046139019 596184054774594069208529)
              ·
                refine ⟨447138041080945551906397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596184054774594069208529 447138041080945551906397)
                ·
                  refine ⟨167676765405354581964899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447138041080945551906397 167676765405354581964899)
                  ·
                    rfl

theorem cell20_367368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_367368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367368 prefixEnd_367368 := by exact prefixLift 367368
  have htrace : WordTrace (prefixWord ++ tailWord_367368) baseStart_367368 baseEnd_367368 := by
    simpa [prefixWord, tailWord_367368, baseEnd_367368] using wordTrace_append hprefix tailTrace_367368
  have hstable : (prefixWord ++ tailWord_367368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367368).length < 2 ^ (prefixWord ++ tailWord_367368).sum := by decide
  have hdescent : baseEnd_367368 < baseStart_367368 := by decide
  rcases family_descends (prefixWord ++ tailWord_367368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367405 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 2]
def baseStart_367405 : Nat := 118140960795 + 367405 * 2 ^ 59
def prefixEnd_367405 : Nat := 4983230072969 + 3 ^ 40 * 367405 * 2
def baseEnd_367405 : Nat := 167693653213546897731415

theorem tailTrace_367405 : CollatzResearch.WordTrace tailWord_367405 prefixEnd_367405 167693653213546897731415 := by
  unfold tailWord_367405
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400361233961907623503669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8933574155974605082335779 13400361233961907623503669)
  ·
    refine ⟨1256283865683928839703469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13400361233961907623503669 1256283865683928839703469)
    ·
      refine ⟨471106449631473314888801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1256283865683928839703469 471106449631473314888801)
      ·
        refine ⟨353329837223604986166601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471106449631473314888801 353329837223604986166601)
        ·
          refine ⟨264997377917703739624951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353329837223604986166601 264997377917703739624951)
          ·
            refine ⟨397496066876555609437427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264997377917703739624951 397496066876555609437427)
            ·
              refine ⟨596244100314833414156141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397496066876555609437427 596244100314833414156141)
              ·
                refine ⟨223591537618062530308553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 596244100314833414156141 223591537618062530308553)
                ·
                  refine ⟨167693653213546897731415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223591537618062530308553 167693653213546897731415)
                  ·
                    rfl

theorem cell20_367405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_367405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367405 prefixEnd_367405 := by exact prefixLift 367405
  have htrace : WordTrace (prefixWord ++ tailWord_367405) baseStart_367405 baseEnd_367405 := by
    simpa [prefixWord, tailWord_367405, baseEnd_367405] using wordTrace_append hprefix tailTrace_367405
  have hstable : (prefixWord ++ tailWord_367405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367405).length < 2 ^ (prefixWord ++ tailWord_367405).sum := by decide
  have hdescent : baseEnd_367405 < baseStart_367405 := by decide
  rcases family_descends (prefixWord ++ tailWord_367405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367410 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_367410 : Nat := 118140960795 + 367410 * 2 ^ 59
def prefixEnd_367410 : Nat := 4983230072969 + 3 ^ 40 * 367410 * 2
def baseEnd_367410 : Nat := 167695935349789102564727

theorem tailTrace_367410 : CollatzResearch.WordTrace tailWord_367410 prefixEnd_367410 167695935349789102564727 := by
  unfold tailWord_367410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350135899735948369358921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8933695732629195651623789 3350135899735948369358921)
  ·
    refine ⟨2512601924801961277019191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3350135899735948369358921 2512601924801961277019191)
    ·
      refine ⟨3768902887202941915528787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2512601924801961277019191 3768902887202941915528787)
      ·
        refine ⟨5653354330804412873293181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768902887202941915528787 5653354330804412873293181)
        ·
          refine ⟨2120007874051654827484943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5653354330804412873293181 2120007874051654827484943)
          ·
            refine ⟨3180011811077482241227415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120007874051654827484943 3180011811077482241227415)
            ·
              refine ⟨4770017716616223361841123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180011811077482241227415 4770017716616223361841123)
              ·
                refine ⟨7155026574924335042761685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770017716616223361841123 7155026574924335042761685)
                ·
                  refine ⟨167695935349789102564727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7155026574924335042761685 167695935349789102564727)
                  ·
                    rfl

theorem cell20_367410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_367410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367410 prefixEnd_367410 := by exact prefixLift 367410
  have htrace : WordTrace (prefixWord ++ tailWord_367410) baseStart_367410 baseEnd_367410 := by
    simpa [prefixWord, tailWord_367410, baseEnd_367410] using wordTrace_append hprefix tailTrace_367410
  have hstable : (prefixWord ++ tailWord_367410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367410).length < 2 ^ (prefixWord ++ tailWord_367410).sum := by decide
  have hdescent : baseEnd_367410 < baseStart_367410 := by decide
  rcases family_descends (prefixWord ++ tailWord_367410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367437 : List Nat := [1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_367437 : Nat := 118140960795 + 367437 * 2 ^ 59
def prefixEnd_367437 : Nat := 4983230072969 + 3 ^ 40 * 367437 * 2
def baseEnd_367437 : Nat := 55902752961832336221539

theorem tailTrace_367437 : CollatzResearch.WordTrace tailWord_367437 prefixEnd_367437 55902752961832336221539 := by
  unfold tailWord_367437
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401528369845977088668565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8934352246563984725779043 13401528369845977088668565)
  ·
    refine ⟨628196642336530176031339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13401528369845977088668565 628196642336530176031339)
    ·
      refine ⟨942294963504795264047009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628196642336530176031339 942294963504795264047009)
      ·
        refine ⟨706721222628596448035257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942294963504795264047009 706721222628596448035257)
        ·
          refine ⟨530040916971447336026443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706721222628596448035257 530040916971447336026443)
          ·
            refine ⟨795061375457171004039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530040916971447336026443 795061375457171004039665)
            ·
              refine ⟨596296031592878253029749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795061375457171004039665 596296031592878253029749)
              ·
                refine ⟨55902752961832336221539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596296031592878253029749 55902752961832336221539)
                ·
                  rfl

theorem cell20_367437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_367437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367437 prefixEnd_367437 := by exact prefixLift 367437
  have htrace : WordTrace (prefixWord ++ tailWord_367437) baseStart_367437 baseEnd_367437 := by
    simpa [prefixWord, tailWord_367437, baseEnd_367437] using wordTrace_append hprefix tailTrace_367437
  have hstable : (prefixWord ++ tailWord_367437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367437).length < 2 ^ (prefixWord ++ tailWord_367437).sum := by decide
  have hdescent : baseEnd_367437 < baseStart_367437 := by decide
  rcases family_descends (prefixWord ++ tailWord_367437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367444 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_367444 : Nat := 118140960795 + 367444 * 2 ^ 59
def prefixEnd_367444 : Nat := 4983230072969 + 3 ^ 40 * 367444 * 2
def baseEnd_367444 : Nat := 167711453876236095431255

theorem tailTrace_367444 : CollatzResearch.WordTrace tailWord_367444 prefixEnd_367444 167711453876236095431255 := by
  unfold tailWord_367444
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700891840410308642086693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8934522453880411522782257 6700891840410308642086693)
  ·
    refine ⟨1256417220076932870391255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6700891840410308642086693 1256417220076932870391255)
    ·
      refine ⟨1884625830115399305586883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256417220076932870391255 1884625830115399305586883)
      ·
        refine ⟨2826938745173098958380325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884625830115399305586883 2826938745173098958380325)
        ·
          refine ⟨530051014719956054696311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2826938745173098958380325 530051014719956054696311)
          ·
            refine ⟨795076522079934082044467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530051014719956054696311 795076522079934082044467)
            ·
              refine ⟨1192614783119901123066701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795076522079934082044467 1192614783119901123066701)
              ·
                refine ⟨447230543669962921150013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192614783119901123066701 447230543669962921150013)
                ·
                  refine ⟨167711453876236095431255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447230543669962921150013 167711453876236095431255)
                  ·
                    rfl

theorem cell20_367444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_367444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367444 prefixEnd_367444 := by exact prefixLift 367444
  have htrace : WordTrace (prefixWord ++ tailWord_367444) baseStart_367444 baseEnd_367444 := by
    simpa [prefixWord, tailWord_367444, baseEnd_367444] using wordTrace_append hprefix tailTrace_367444
  have hstable : (prefixWord ++ tailWord_367444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367444).length < 2 ^ (prefixWord ++ tailWord_367444).sum := by decide
  have hdescent : baseEnd_367444 < baseStart_367444 := by decide
  rcases family_descends (prefixWord ++ tailWord_367444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367455 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_367455 : Nat := 118140960795 + 367455 * 2 ^ 59
def prefixEnd_367455 : Nat := 4983230072969 + 3 ^ 40 * 367455 * 2
def baseEnd_367455 : Nat := 167716474575968946064543

theorem tailTrace_367455 : CollatzResearch.WordTrace tailWord_367455 prefixEnd_367455 167716474575968946064543 := by
  unfold tailWord_367455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13402184883780766162823819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8934789922520510775215879 13402184883780766162823819)
  ·
    refine ⟨20103277325671149244235729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13402184883780766162823819 20103277325671149244235729)
    ·
      refine ⟨15077457994253361933176797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20103277325671149244235729 15077457994253361933176797)
      ·
        refine ⟨5654046747845010724941299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15077457994253361933176797 5654046747845010724941299)
        ·
          refine ⟨8481070121767516087411949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5654046747845010724941299 8481070121767516087411949)
          ·
            refine ⟨3180401295662818532779481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8481070121767516087411949 3180401295662818532779481)
            ·
              refine ⟨2385300971747113899584611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180401295662818532779481 2385300971747113899584611)
              ·
                refine ⟨3577951457620670849376917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385300971747113899584611 3577951457620670849376917)
                ·
                  refine ⟨167716474575968946064543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3577951457620670849376917 167716474575968946064543)
                  ·
                    rfl

theorem cell20_367455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_367455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367455 prefixEnd_367455 := by exact prefixLift 367455
  have htrace : WordTrace (prefixWord ++ tailWord_367455) baseStart_367455 baseEnd_367455 := by
    simpa [prefixWord, tailWord_367455, baseEnd_367455] using wordTrace_append hprefix tailTrace_367455
  have hstable : (prefixWord ++ tailWord_367455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367455).length < 2 ^ (prefixWord ++ tailWord_367455).sum := by decide
  have hdescent : baseEnd_367455 < baseStart_367455 := by decide
  rcases family_descends (prefixWord ++ tailWord_367455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367496 : List Nat := [2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_367496 : Nat := 118140960795 + 367496 * 2 ^ 59
def prefixEnd_367496 : Nat := 4983230072969 + 3 ^ 40 * 367496 * 2
def baseEnd_367496 : Nat := 55911729364385008565903

theorem tailTrace_367496 : CollatzResearch.WordTrace tailWord_367496 prefixEnd_367496 55911729364385008565903 := by
  unfold tailWord_367496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701840138316115082533171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8935786851088153443377561 6701840138316115082533171)
  ·
    refine ⟨10052760207474172623799757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701840138316115082533171 10052760207474172623799757)
    ·
      refine ⟨3769785077802814733924909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10052760207474172623799757 3769785077802814733924909)
      ·
        refine ⟨1413669404176055525221841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3769785077802814733924909 1413669404176055525221841)
        ·
          refine ⟨1060252053132041643916381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413669404176055525221841 1060252053132041643916381)
          ·
            refine ⟨397594519924515616468643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060252053132041643916381 397594519924515616468643)
            ·
              refine ⟨596391779886773424702965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397594519924515616468643 596391779886773424702965)
              ·
                refine ⟨55911729364385008565903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596391779886773424702965 55911729364385008565903)
                ·
                  rfl

theorem cell20_367496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_367496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367496 prefixEnd_367496 := by exact prefixLift 367496
  have htrace : WordTrace (prefixWord ++ tailWord_367496) baseStart_367496 baseEnd_367496 := by
    simpa [prefixWord, tailWord_367496, baseEnd_367496] using wordTrace_append hprefix tailTrace_367496
  have hstable : (prefixWord ++ tailWord_367496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367496).length < 2 ^ (prefixWord ++ tailWord_367496).sum := by decide
  have hdescent : baseEnd_367496 < baseStart_367496 := by decide
  rcases family_descends (prefixWord ++ tailWord_367496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367524 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_367524 : Nat := 118140960795 + 367524 * 2 ^ 59
def prefixEnd_367524 : Nat := 4983230072969 + 3 ^ 40 * 367524 * 2
def baseEnd_367524 : Nat := 167747968056111372764261

theorem tailTrace_367524 : CollatzResearch.WordTrace tailWord_367524 prefixEnd_367524 167747968056111372764261 := by
  unfold tailWord_367524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702350760265395473542813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8936467680353860631390417 6702350760265395473542813)
  ·
    refine ⟨2513381535099523302578555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6702350760265395473542813 2513381535099523302578555)
    ·
      refine ⟨3770072302649284953867833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2513381535099523302578555 3770072302649284953867833)
      ·
        refine ⟨2827554226986963715400875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3770072302649284953867833 2827554226986963715400875)
        ·
          refine ⟨4241331340480445573101313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827554226986963715400875 4241331340480445573101313)
          ·
            refine ⟨3180998505360334179825985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4241331340480445573101313 3180998505360334179825985)
            ·
              refine ⟨2385748879020250634869489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180998505360334179825985 2385748879020250634869489)
              ·
                refine ⟨1789311659265187976152117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2385748879020250634869489 1789311659265187976152117)
                ·
                  refine ⟨167747968056111372764261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789311659265187976152117 167747968056111372764261)
                  ·
                    rfl

theorem cell20_367524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_367524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367524 prefixEnd_367524 := by exact prefixLift 367524
  have htrace : WordTrace (prefixWord ++ tailWord_367524) baseStart_367524 baseEnd_367524 := by
    simpa [prefixWord, tailWord_367524, baseEnd_367524] using wordTrace_append hprefix tailTrace_367524
  have hstable : (prefixWord ++ tailWord_367524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367524).length < 2 ^ (prefixWord ++ tailWord_367524).sum := by decide
  have hdescent : baseEnd_367524 < baseStart_367524 := by decide
  rcases family_descends (prefixWord ++ tailWord_367524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367537 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 3]
def baseStart_367537 : Nat := 118140960795 + 367537 * 2 ^ 59
def prefixEnd_367537 : Nat := 4983230072969 + 3 ^ 40 * 367537 * 2
def baseEnd_367537 : Nat := 167753901610341105330875

theorem tailTrace_367537 : CollatzResearch.WordTrace tailWord_367537 prefixEnd_367537 167753901610341105330875 := by
  unfold tailWord_367537
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405175669483694167308865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8936783779655796111539243 13405175669483694167308865)
  ·
    refine ⟨10053881752112770625481649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13405175669483694167308865 10053881752112770625481649)
    ·
      refine ⟨7540411314084577969111237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10053881752112770625481649 7540411314084577969111237)
      ·
        refine ⟨1413827121390858369208357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7540411314084577969111237 1413827121390858369208357)
        ·
          refine ⟨265092585260785944226567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1413827121390858369208357 265092585260785944226567)
          ·
            refine ⟨397638877891178916339851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265092585260785944226567 397638877891178916339851)
            ·
              refine ⟨596458316836768374509777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397638877891178916339851 596458316836768374509777)
              ·
                refine ⟨447343737627576280882333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596458316836768374509777 447343737627576280882333)
                ·
                  refine ⟨167753901610341105330875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447343737627576280882333 167753901610341105330875)
                  ·
                    rfl

theorem cell20_367537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_367537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367537 prefixEnd_367537 := by exact prefixLift 367537
  have htrace : WordTrace (prefixWord ++ tailWord_367537) baseStart_367537 baseEnd_367537 := by
    simpa [prefixWord, tailWord_367537, baseEnd_367537] using wordTrace_append hprefix tailTrace_367537
  have hstable : (prefixWord ++ tailWord_367537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367537).length < 2 ^ (prefixWord ++ tailWord_367537).sum := by decide
  have hdescent : baseEnd_367537 < baseStart_367537 := by decide
  rcases family_descends (prefixWord ++ tailWord_367537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367569 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_367569 : Nat := 118140960795 + 367569 * 2 ^ 59
def prefixEnd_367569 : Nat := 4983230072969 + 3 ^ 40 * 367569 * 2
def baseEnd_367569 : Nat := 167768507282291216264077

theorem tailTrace_367569 : CollatzResearch.WordTrace tailWord_367569 prefixEnd_367569 167768507282291216264077 := by
  unfold tailWord_367569
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406342805367763632473761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8937561870245175754982507 13406342805367763632473761)
  ·
    refine ⟨10054757104025822724355321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13406342805367763632473761 10054757104025822724355321)
    ·
      refine ⟨7541067828019367043266491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10054757104025822724355321 7541067828019367043266491)
      ·
        refine ⟨11311601742029050564899737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7541067828019367043266491 11311601742029050564899737)
        ·
          refine ⟨8483701306521787923674803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11311601742029050564899737 8483701306521787923674803)
          ·
            refine ⟨12725551959782681885512205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483701306521787923674803 12725551959782681885512205)
            ·
              refine ⟨4772081984918505707067077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12725551959782681885512205 4772081984918505707067077)
              ·
                refine ⟨894765372172219820075077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4772081984918505707067077 894765372172219820075077)
                ·
                  refine ⟨167768507282291216264077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894765372172219820075077 167768507282291216264077)
                  ·
                    rfl

theorem cell20_367569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_367569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367569 prefixEnd_367569 := by exact prefixLift 367569
  have htrace : WordTrace (prefixWord ++ tailWord_367569) baseStart_367569 baseEnd_367569 := by
    simpa [prefixWord, tailWord_367569, baseEnd_367569] using wordTrace_append hprefix tailTrace_367569
  have hstable : (prefixWord ++ tailWord_367569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367569).length < 2 ^ (prefixWord ++ tailWord_367569).sum := by decide
  have hdescent : baseEnd_367569 < baseStart_367569 := by decide
  rcases family_descends (prefixWord ++ tailWord_367569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367572 : List Nat := [2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_367572 : Nat := 118140960795 + 367572 * 2 ^ 59
def prefixEnd_367572 : Nat := 4983230072969 + 3 ^ 40 * 367572 * 2
def baseEnd_367572 : Nat := 55923292188012179721355

theorem tailTrace_367572 : CollatzResearch.WordTrace tailWord_367572 prefixEnd_367572 55923292188012179721355 := by
  unfold tailWord_367572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703226112178447572416485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8937634816237930096555313 6703226112178447572416485)
  ·
    refine ⟨1256854896033458919828091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6703226112178447572416485 1256854896033458919828091)
    ·
      refine ⟨1885282344050188379742137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256854896033458919828091 1885282344050188379742137)
      ·
        refine ⟨1413961758037641284806603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1885282344050188379742137 1413961758037641284806603)
        ·
          refine ⟨2120942637056461927209905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413961758037641284806603 2120942637056461927209905)
          ·
            refine ⟨1590706977792346445407429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120942637056461927209905 1590706977792346445407429)
            ·
              refine ⟨298257558336064958513893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1590706977792346445407429 298257558336064958513893)
              ·
                refine ⟨55923292188012179721355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298257558336064958513893 55923292188012179721355)
                ·
                  rfl

theorem cell20_367572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_367572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367572 prefixEnd_367572 := by exact prefixLift 367572
  have htrace : WordTrace (prefixWord ++ tailWord_367572) baseStart_367572 baseEnd_367572 := by
    simpa [prefixWord, tailWord_367572, baseEnd_367572] using wordTrace_append hprefix tailTrace_367572
  have hstable : (prefixWord ++ tailWord_367572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367572).length < 2 ^ (prefixWord ++ tailWord_367572).sum := by decide
  have hdescent : baseEnd_367572 < baseStart_367572 := by decide
  rcases family_descends (prefixWord ++ tailWord_367572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367589 : List Nat := [1, 3, 1, 6, 2, 1, 6]
def baseStart_367589 : Nat := 118140960795 + 367589 * 2 ^ 59
def prefixEnd_367589 : Nat := 4983230072969 + 3 ^ 40 * 367589 * 2
def baseEnd_367589 : Nat := 18641959536362226177481

theorem tailTrace_367589 : CollatzResearch.WordTrace tailWord_367589 prefixEnd_367589 18641959536362226177481 := by
  unfold tailWord_367589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13407072265295307048201821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8938048176863538032134547 13407072265295307048201821)
  ·
    refine ⟨5027652099485740143075683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13407072265295307048201821 5027652099485740143075683)
    ·
      refine ⟨7541478149228610214613525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5027652099485740143075683 7541478149228610214613525)
      ·
        refine ⟨353506788245091103810009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7541478149228610214613525 353506788245091103810009)
        ·
          refine ⟨265130091183818327857507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353506788245091103810009 265130091183818327857507)
          ·
            refine ⟨397695136775727491786261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265130091183818327857507 397695136775727491786261)
            ·
              refine ⟨18641959536362226177481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 397695136775727491786261 18641959536362226177481)
              ·
                rfl

theorem cell20_367589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 6].length) (baseStart_367589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367589 prefixEnd_367589 := by exact prefixLift 367589
  have htrace : WordTrace (prefixWord ++ tailWord_367589) baseStart_367589 baseEnd_367589 := by
    simpa [prefixWord, tailWord_367589, baseEnd_367589] using wordTrace_append hprefix tailTrace_367589
  have hstable : (prefixWord ++ tailWord_367589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367589).length < 2 ^ (prefixWord ++ tailWord_367589).sum := by decide
  have hdescent : baseEnd_367589 < baseStart_367589 := by decide
  rcases family_descends (prefixWord ++ tailWord_367589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367600 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_367600 : Nat := 118140960795 + 367600 * 2 ^ 59
def prefixEnd_367600 : Nat := 4983230072969 + 3 ^ 40 * 367600 * 2
def baseEnd_367600 : Nat := 167782656526992886230617

theorem tailTrace_367600 : CollatzResearch.WordTrace tailWord_367600 prefixEnd_367600 167782656526992886230617 := by
  unfold tailWord_367600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703736734127727963426127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8938315645503637284568169 6703736734127727963426127)
  ·
    refine ⟨10055605101191591945139191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6703736734127727963426127 10055605101191591945139191)
    ·
      refine ⟨15083407651787387917708787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10055605101191591945139191 15083407651787387917708787)
      ·
        refine ⟨22625111477681081876563181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15083407651787387917708787 22625111477681081876563181)
        ·
          refine ⟨8484416804130405703711193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22625111477681081876563181 8484416804130405703711193)
          ·
            refine ⟨6363312603097804277783395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8484416804130405703711193 6363312603097804277783395)
            ·
              refine ⟨9544968904646706416675093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363312603097804277783395 9544968904646706416675093)
              ·
                refine ⟨447420417405314363281645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9544968904646706416675093 447420417405314363281645)
                ·
                  refine ⟨167782656526992886230617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447420417405314363281645 167782656526992886230617)
                  ·
                    rfl

theorem cell20_367600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_367600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367600 prefixEnd_367600 := by exact prefixLift 367600
  have htrace : WordTrace (prefixWord ++ tailWord_367600) baseStart_367600 baseEnd_367600 := by
    simpa [prefixWord, tailWord_367600, baseEnd_367600] using wordTrace_append hprefix tailTrace_367600
  have hstable : (prefixWord ++ tailWord_367600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367600).length < 2 ^ (prefixWord ++ tailWord_367600).sum := by decide
  have hdescent : baseEnd_367600 < baseStart_367600 := by decide
  rcases family_descends (prefixWord ++ tailWord_367600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367617 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_367617 : Nat := 118140960795 + 367617 * 2 ^ 59
def prefixEnd_367617 : Nat := 4983230072969 + 3 ^ 40 * 367617 * 2
def baseEnd_367617 : Nat := 167790415790216382663881

theorem tailTrace_367617 : CollatzResearch.WordTrace tailWord_367617 prefixEnd_367617 167790415790216382663881 := by
  unfold tailWord_367617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408093509193867830221105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8938729006129245220147403 13408093509193867830221105)
  ·
    refine ⟨10056070131895400872665829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13408093509193867830221105 10056070131895400872665829)
    ·
      refine ⟨1885513149730387663624843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10056070131895400872665829 1885513149730387663624843)
      ·
        refine ⟨2828269724595581495437265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885513149730387663624843 2828269724595581495437265)
        ·
          refine ⟨2121202293446686121577949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828269724595581495437265 2121202293446686121577949)
          ·
            refine ⟨795450860042507295591731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2121202293446686121577949 795450860042507295591731)
            ·
              refine ⟨1193176290063760943387597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795450860042507295591731 1193176290063760943387597)
              ·
                refine ⟨447441108773910353770349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193176290063760943387597 447441108773910353770349)
                ·
                  refine ⟨167790415790216382663881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447441108773910353770349 167790415790216382663881)
                  ·
                    rfl

theorem cell20_367617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_367617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367617 prefixEnd_367617 := by exact prefixLift 367617
  have htrace : WordTrace (prefixWord ++ tailWord_367617) baseStart_367617 baseEnd_367617 := by
    simpa [prefixWord, tailWord_367617, baseEnd_367617] using wordTrace_append hprefix tailTrace_367617
  have hstable : (prefixWord ++ tailWord_367617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367617).length < 2 ^ (prefixWord ++ tailWord_367617).sum := by decide
  have hdescent : baseEnd_367617 < baseStart_367617 := by decide
  rcases family_descends (prefixWord ++ tailWord_367617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367648 : List Nat := [2, 1, 1, 7, 2, 7]
def baseStart_367648 : Nat := 118140960795 + 367648 * 2 ^ 59
def prefixEnd_367648 : Nat := 4983230072969 + 3 ^ 40 * 367648 * 2
def baseEnd_367648 : Nat := 6214983890182150097423

theorem tailTrace_367648 : CollatzResearch.WordTrace tailWord_367648 prefixEnd_367648 6214983890182150097423 := by
  unfold tailWord_367648
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704612086040780062299799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8939482781387706749733065 6704612086040780062299799)
  ·
    refine ⟨10056918129061170093449699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704612086040780062299799 10056918129061170093449699)
    ·
      refine ⟨15085377193591755140174549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10056918129061170093449699 15085377193591755140174549)
      ·
        refine ⟨353563527974806761097841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15085377193591755140174549 353563527974806761097841)
        ·
          refine ⟨265172645981105070823381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353563527974806761097841 265172645981105070823381)
          ·
            refine ⟨6214983890182150097423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265172645981105070823381 6214983890182150097423)
            ·
              rfl

theorem cell20_367648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 7].length) (baseStart_367648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367648 prefixEnd_367648 := by exact prefixLift 367648
  have htrace : WordTrace (prefixWord ++ tailWord_367648) baseStart_367648 baseEnd_367648 := by
    simpa [prefixWord, tailWord_367648, baseEnd_367648] using wordTrace_append hprefix tailTrace_367648
  have hstable : (prefixWord ++ tailWord_367648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367648).length < 2 ^ (prefixWord ++ tailWord_367648).sum := by decide
  have hdescent : baseEnd_367648 < baseStart_367648 := by decide
  rcases family_descends (prefixWord ++ tailWord_367648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367658 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_367658 : Nat := 118140960795 + 367658 * 2 ^ 59
def prefixEnd_367658 : Nat := 4983230072969 + 3 ^ 40 * 367658 * 2
def baseEnd_367658 : Nat := 167809129307402462297047

theorem tailTrace_367658 : CollatzResearch.WordTrace tailWord_367658 prefixEnd_367658 167809129307402462297047 := by
  unfold tailWord_367658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352397225511332958115907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8939725934696887888309085 3352397225511332958115907)
  ·
    refine ⟨5028595838266999437173861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352397225511332958115907 5028595838266999437173861)
    ·
      refine ⟨942861719675062394470099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5028595838266999437173861 942861719675062394470099)
      ·
        refine ⟨1414292579512593591705149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942861719675062394470099 1414292579512593591705149)
        ·
          refine ⟨530359717317222596889431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1414292579512593591705149 530359717317222596889431)
          ·
            refine ⟨795539575975833895334147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530359717317222596889431 795539575975833895334147)
            ·
              refine ⟨1193309363963750843001221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795539575975833895334147 1193309363963750843001221)
              ·
                refine ⟨223745505743203283062729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1193309363963750843001221 223745505743203283062729)
                ·
                  refine ⟨167809129307402462297047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223745505743203283062729 167809129307402462297047)
                  ·
                    rfl

theorem cell20_367658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_367658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367658 prefixEnd_367658 := by exact prefixLift 367658
  have htrace : WordTrace (prefixWord ++ tailWord_367658) baseStart_367658 baseEnd_367658 := by
    simpa [prefixWord, tailWord_367658, baseEnd_367658] using wordTrace_append hprefix tailTrace_367658
  have hstable : (prefixWord ++ tailWord_367658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367658).length < 2 ^ (prefixWord ++ tailWord_367658).sum := by decide
  have hdescent : baseEnd_367658 < baseStart_367658 := by decide
  rcases family_descends (prefixWord ++ tailWord_367658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367662 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_367662 : Nat := 118140960795 + 367662 * 2 ^ 59
def prefixEnd_367662 : Nat := 4983230072969 + 3 ^ 40 * 367662 * 2
def baseEnd_367662 : Nat := 167810955016396226163697

theorem tailTrace_367662 : CollatzResearch.WordTrace tailWord_367662 prefixEnd_367662 167810955016396226163697 := by
  unfold tailWord_367662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676216849253855064451155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8939823196020560343739493 1676216849253855064451155)
  ·
    refine ⟨2514325273880782596676733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676216849253855064451155 2514325273880782596676733)
    ·
      refine ⟨942871977705293473753775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2514325273880782596676733 942871977705293473753775)
      ·
        refine ⟨1414307966557940210630663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942871977705293473753775 1414307966557940210630663)
        ·
          refine ⟨2121461949836910315945995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414307966557940210630663 2121461949836910315945995)
          ·
            refine ⟨3182192924755365473918993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121461949836910315945995 3182192924755365473918993)
            ·
              refine ⟨2386644693566524105439245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182192924755365473918993 2386644693566524105439245)
              ·
                refine ⟨894991760087446539539717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2386644693566524105439245 894991760087446539539717)
                ·
                  refine ⟨167810955016396226163697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894991760087446539539717 167810955016396226163697)
                  ·
                    rfl

theorem cell20_367662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_367662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367662 prefixEnd_367662 := by exact prefixLift 367662
  have htrace : WordTrace (prefixWord ++ tailWord_367662) baseStart_367662 baseEnd_367662 := by
    simpa [prefixWord, tailWord_367662, baseEnd_367662] using wordTrace_append hprefix tailTrace_367662
  have hstable : (prefixWord ++ tailWord_367662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367662).length < 2 ^ (prefixWord ++ tailWord_367662).sum := by decide
  have hdescent : baseEnd_367662 < baseStart_367662 := by decide
  rcases family_descends (prefixWord ++ tailWord_367662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367683 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_367683 : Nat := 118140960795 + 367683 * 2 ^ 59
def prefixEnd_367683 : Nat := 4983230072969 + 3 ^ 40 * 367683 * 2
def baseEnd_367683 : Nat := 167820539988613486463611

theorem tailTrace_367683 : CollatzResearch.WordTrace tailWord_367683 prefixEnd_367683 167820539988613486463611 := by
  unfold tailWord_367683
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410500726954761102123703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8940333817969840734749135 13410500726954761102123703)
  ·
    refine ⟨20115751090432141653185555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13410500726954761102123703 20115751090432141653185555)
    ·
      refine ⟨30173626635648212479778333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20115751090432141653185555 30173626635648212479778333)
      ·
        refine ⟨11315109988368079679916875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30173626635648212479778333 11315109988368079679916875)
        ·
          refine ⟨16972664982552119519875313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11315109988368079679916875 16972664982552119519875313)
          ·
            refine ⟨12729498736914089639906485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16972664982552119519875313 12729498736914089639906485)
            ·
              refine ⟨1193390506585695903741233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12729498736914089639906485 1193390506585695903741233)
              ·
                refine ⟨895042879939271927805925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193390506585695903741233 895042879939271927805925)
                ·
                  refine ⟨167820539988613486463611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895042879939271927805925 167820539988613486463611)
                  ·
                    rfl

theorem cell20_367683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_367683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367683 prefixEnd_367683 := by exact prefixLift 367683
  have htrace : WordTrace (prefixWord ++ tailWord_367683) baseStart_367683 baseEnd_367683 := by
    simpa [prefixWord, tailWord_367683, baseEnd_367683] using wordTrace_append hprefix tailTrace_367683
  have hstable : (prefixWord ++ tailWord_367683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367683).length < 2 ^ (prefixWord ++ tailWord_367683).sum := by decide
  have hdescent : baseEnd_367683 < baseStart_367683 := by decide
  rcases family_descends (prefixWord ++ tailWord_367683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367690 : List Nat := [3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_367690 : Nat := 118140960795 + 367690 * 2 ^ 59
def prefixEnd_367690 : Nat := 4983230072969 + 3 ^ 40 * 367690 * 2
def baseEnd_367690 : Nat := 55941244993117524410083

theorem tailTrace_367690 : CollatzResearch.WordTrace tailWord_367690 prefixEnd_367690 55941244993117524410083 := by
  unfold tailWord_367690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352689009482350324407131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8940504025286267531752349 3352689009482350324407131)
  ·
    refine ⟨5029033514223525486610697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352689009482350324407131 5029033514223525486610697)
    ·
      refine ⟨3771775135667644114958023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029033514223525486610697 3771775135667644114958023)
      ·
        refine ⟨5657662703501466172437035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771775135667644114958023 5657662703501466172437035)
        ·
          refine ⟨8486494055252199258655553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657662703501466172437035 8486494055252199258655553)
          ·
            refine ⟨6364870541439149443991665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8486494055252199258655553 6364870541439149443991665)
            ·
              refine ⟨4773652906079362082993749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364870541439149443991665 4773652906079362082993749)
              ·
                refine ⟨55941244993117524410083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4773652906079362082993749 55941244993117524410083)
                ·
                  rfl

theorem cell20_367690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_367690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367690 prefixEnd_367690 := by exact prefixLift 367690
  have htrace : WordTrace (prefixWord ++ tailWord_367690) baseStart_367690 baseEnd_367690 := by
    simpa [prefixWord, tailWord_367690, baseEnd_367690] using wordTrace_append hprefix tailTrace_367690
  have hstable : (prefixWord ++ tailWord_367690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367690).length < 2 ^ (prefixWord ++ tailWord_367690).sum := by decide
  have hdescent : baseEnd_367690 < baseStart_367690 := by decide
  rcases family_descends (prefixWord ++ tailWord_367690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367721 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_367721 : Nat := 118140960795 + 367721 * 2 ^ 59
def prefixEnd_367721 : Nat := 4983230072969 + 3 ^ 40 * 367721 * 2
def baseEnd_367721 : Nat := 167837884224054243196789

theorem tailTrace_367721 : CollatzResearch.WordTrace tailWord_367721 prefixEnd_367721 167837884224054243196789 := by
  unfold tailWord_367721
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411886700817093592007017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8941257800544729061338011 13411886700817093592007017)
  ·
    refine ⟨10058915025612820194005263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13411886700817093592007017 10058915025612820194005263)
    ·
      refine ⟨15088372538419230291007895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10058915025612820194005263 15088372538419230291007895)
      ·
        refine ⟨22632558807628845436511843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15088372538419230291007895 22632558807628845436511843)
        ·
          refine ⟨33948838211443268154767765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22632558807628845436511843 33948838211443268154767765)
          ·
            refine ⟨1591351791161403194754739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33948838211443268154767765 1591351791161403194754739)
            ·
              refine ⟨2387027686742104792132109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591351791161403194754739 2387027686742104792132109)
              ·
                refine ⟨895135382528289297049541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2387027686742104792132109 895135382528289297049541)
                ·
                  refine ⟨167837884224054243196789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895135382528289297049541 167837884224054243196789)
                  ·
                    rfl

theorem cell20_367721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_367721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367721 prefixEnd_367721 := by exact prefixLift 367721
  have htrace : WordTrace (prefixWord ++ tailWord_367721) baseStart_367721 baseEnd_367721 := by
    simpa [prefixWord, tailWord_367721, baseEnd_367721] using wordTrace_append hprefix tailTrace_367721
  have hstable : (prefixWord ++ tailWord_367721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367721).length < 2 ^ (prefixWord ++ tailWord_367721).sum := by decide
  have hdescent : baseEnd_367721 < baseStart_367721 := by decide
  rcases family_descends (prefixWord ++ tailWord_367721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367728 : List Nat := [2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_367728 : Nat := 118140960795 + 367728 * 2 ^ 59
def prefixEnd_367728 : Nat := 4983230072969 + 3 ^ 40 * 367728 * 2
def baseEnd_367728 : Nat := 55947026404931109987809

theorem tailTrace_367728 : CollatzResearch.WordTrace tailWord_367728 prefixEnd_367728 55947026404931109987809 := by
  unfold tailWord_367728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706071005895866893755919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8941428007861155858341225 6706071005895866893755919)
  ·
    refine ⟨10059106508843800340633879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6706071005895866893755919 10059106508843800340633879)
    ·
      refine ⟨15088659763265700510950819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10059106508843800340633879 15088659763265700510950819)
      ·
        refine ⟨22632989644898550766426229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15088659763265700510950819 22632989644898550766426229)
        ·
          refine ⟨2121842779209239134352459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22632989644898550766426229 2121842779209239134352459)
          ·
            refine ⟨3182764168813858701528689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121842779209239134352459 3182764168813858701528689)
            ·
              refine ⟨2387073126610394026146517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182764168813858701528689 2387073126610394026146517)
              ·
                refine ⟨55947026404931109987809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2387073126610394026146517 55947026404931109987809)
                ·
                  rfl

theorem cell20_367728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_367728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367728 prefixEnd_367728 := by exact prefixLift 367728
  have htrace : WordTrace (prefixWord ++ tailWord_367728) baseStart_367728 baseEnd_367728 := by
    simpa [prefixWord, tailWord_367728, baseEnd_367728] using wordTrace_append hprefix tailTrace_367728
  have hstable : (prefixWord ++ tailWord_367728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367728).length < 2 ^ (prefixWord ++ tailWord_367728).sum := by decide
  have hdescent : baseEnd_367728 < baseStart_367728 := by decide
  rcases family_descends (prefixWord ++ tailWord_367728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367745 : List Nat := [1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_367745 : Nat := 118140960795 + 367745 * 2 ^ 59
def prefixEnd_367745 : Nat := 4983230072969 + 3 ^ 40 * 367745 * 2
def baseEnd_367745 : Nat := 55949612826005608798897

theorem tailTrace_367745 : CollatzResearch.WordTrace tailWord_367745 prefixEnd_367745 55949612826005608798897 := by
  unfold tailWord_367745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412762052730145690880689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8941841368486763793920459 13412762052730145690880689)
  ·
    refine ⟨10059571539547609268160517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13412762052730145690880689 10059571539547609268160517)
    ·
      refine ⟨1886169663665176737780097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10059571539547609268160517 1886169663665176737780097)
      ·
        refine ⟨1414627247748882553335073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1886169663665176737780097 1414627247748882553335073)
        ·
          refine ⟨1060970435811661915001305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414627247748882553335073 1060970435811661915001305)
          ·
            refine ⟨795727826858746436250979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060970435811661915001305 795727826858746436250979)
            ·
              refine ⟨1193591740288119654376469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795727826858746436250979 1193591740288119654376469)
              ·
                refine ⟨55949612826005608798897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1193591740288119654376469 55949612826005608798897)
                ·
                  rfl

theorem cell20_367745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_367745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367745 prefixEnd_367745 := by exact prefixLift 367745
  have htrace : WordTrace (prefixWord ++ tailWord_367745) baseStart_367745 baseEnd_367745 := by
    simpa [prefixWord, tailWord_367745, baseEnd_367745] using wordTrace_append hprefix tailTrace_367745
  have hstable : (prefixWord ++ tailWord_367745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367745).length < 2 ^ (prefixWord ++ tailWord_367745).sum := by decide
  have hdescent : baseEnd_367745 < baseStart_367745 := by decide
  rcases family_descends (prefixWord ++ tailWord_367745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367772 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_367772 : Nat := 118140960795 + 367772 * 2 ^ 59
def prefixEnd_367772 : Nat := 4983230072969 + 3 ^ 40 * 367772 * 2
def baseEnd_367772 : Nat := 167861162013724732496581

theorem tailTrace_367772 : CollatzResearch.WordTrace tailWord_367772 prefixEnd_367772 167861162013724732496581 := by
  unfold tailWord_367772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706873411816164651056785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8942497882421552868075713 6706873411816164651056785)
  ·
    refine ⟨5030155058862123488292589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6706873411816164651056785 5030155058862123488292589)
    ·
      refine ⟨1886308147073296308109721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5030155058862123488292589 1886308147073296308109721)
      ·
        refine ⟨1414731110304972231082291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1886308147073296308109721 1414731110304972231082291)
        ·
          refine ⟨2122096665457458346623437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414731110304972231082291 2122096665457458346623437)
          ·
            refine ⟨795786249546546879983789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2122096665457458346623437 795786249546546879983789)
            ·
              refine ⟨298419843579955079993921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795786249546546879983789 298419843579955079993921)
              ·
                refine ⟨223814882684966309995441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298419843579955079993921 223814882684966309995441)
                ·
                  refine ⟨167861162013724732496581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223814882684966309995441 167861162013724732496581)
                  ·
                    rfl

theorem cell20_367772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_367772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367772 prefixEnd_367772 := by exact prefixLift 367772
  have htrace : WordTrace (prefixWord ++ tailWord_367772) baseStart_367772 baseEnd_367772 := by
    simpa [prefixWord, tailWord_367772, baseEnd_367772] using wordTrace_append hprefix tailTrace_367772
  have hstable : (prefixWord ++ tailWord_367772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367772).length < 2 ^ (prefixWord ++ tailWord_367772).sum := by decide
  have hdescent : baseEnd_367772 < baseStart_367772 := by decide
  rcases family_descends (prefixWord ++ tailWord_367772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367783 : List Nat := [1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_367783 : Nat := 118140960795 + 367783 * 2 ^ 59
def prefixEnd_367783 : Nat := 4983230072969 + 3 ^ 40 * 367783 * 2
def baseEnd_367783 : Nat := 55955394237819194376623

theorem tailTrace_367783 : CollatzResearch.WordTrace tailWord_367783 prefixEnd_367783 55955394237819194376623 := by
  unfold tailWord_367783
  simp only [CollatzResearch.WordTrace]
  refine ⟨13414148026592478180764003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8942765351061652120509335 13414148026592478180764003)
  ·
    refine ⟨20121222039888717271146005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13414148026592478180764003 20121222039888717271146005)
    ·
      refine ⟨943182283119783622084969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20121222039888717271146005 943182283119783622084969)
      ·
        refine ⟨707386712339837716563727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943182283119783622084969 707386712339837716563727)
        ·
          refine ⟨1061080068509756574845591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707386712339837716563727 1061080068509756574845591)
          ·
            refine ⟨1591620102764634862268387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061080068509756574845591 1591620102764634862268387)
            ·
              refine ⟨2387430154146952293402581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591620102764634862268387 2387430154146952293402581)
              ·
                refine ⟨55955394237819194376623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2387430154146952293402581 55955394237819194376623)
                ·
                  rfl

theorem cell20_367783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_367783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367783 prefixEnd_367783 := by exact prefixLift 367783
  have htrace : WordTrace (prefixWord ++ tailWord_367783) baseStart_367783 baseEnd_367783 := by
    simpa [prefixWord, tailWord_367783, baseEnd_367783] using wordTrace_append hprefix tailTrace_367783
  have hstable : (prefixWord ++ tailWord_367783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367783).length < 2 ^ (prefixWord ++ tailWord_367783).sum := by decide
  have hdescent : baseEnd_367783 < baseStart_367783 := by decide
  rcases family_descends (prefixWord ++ tailWord_367783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367786 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_367786 : Nat := 118140960795 + 367786 * 2 ^ 59
def prefixEnd_367786 : Nat := 4983230072969 + 3 ^ 40 * 367786 * 2
def baseEnd_367786 : Nat := 167867551995202906029857

theorem tailTrace_367786 : CollatzResearch.WordTrace tailWord_367786 prefixEnd_367786 167867551995202906029857 := by
  unfold tailWord_367786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353564361395402423280803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8942838297054406462082141 3353564361395402423280803)
  ·
    refine ⟨5030346542093103634921205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353564361395402423280803 5030346542093103634921205)
    ·
      refine ⟨471594988321228465773863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5030346542093103634921205 471594988321228465773863)
      ·
        refine ⟨707392482481842698660795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471594988321228465773863 707392482481842698660795)
        ·
          refine ⟨1061088723722764047991193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707392482481842698660795 1061088723722764047991193)
          ·
            refine ⟨795816542792073035993395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061088723722764047991193 795816542792073035993395)
            ·
              refine ⟨1193724814188109553990093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795816542792073035993395 1193724814188109553990093)
              ·
                refine ⟨447646805320541082746285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193724814188109553990093 447646805320541082746285)
                ·
                  refine ⟨167867551995202906029857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447646805320541082746285 167867551995202906029857)
                  ·
                    rfl

theorem cell20_367786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_367786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367786 prefixEnd_367786 := by exact prefixLift 367786
  have htrace : WordTrace (prefixWord ++ tailWord_367786) baseStart_367786 baseEnd_367786 := by
    simpa [prefixWord, tailWord_367786, baseEnd_367786] using wordTrace_append hprefix tailTrace_367786
  have hstable : (prefixWord ++ tailWord_367786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367786).length < 2 ^ (prefixWord ++ tailWord_367786).sum := by decide
  have hdescent : baseEnd_367786 < baseStart_367786 := by decide
  rcases family_descends (prefixWord ++ tailWord_367786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367811 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_367811 : Nat := 118140960795 + 367811 * 2 ^ 59
def prefixEnd_367811 : Nat := 4983230072969 + 3 ^ 40 * 367811 * 2
def baseEnd_367811 : Nat := 167878962676413930196421

theorem tailTrace_367811 : CollatzResearch.WordTrace tailWord_367811 prefixEnd_367811 167878962676413930196421 := by
  unfold tailWord_367811
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415169270491038962783287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8943446180327359308522191 13415169270491038962783287)
  ·
    refine ⟨20122753905736558444174931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13415169270491038962783287 20122753905736558444174931)
    ·
      refine ⟨30184130858604837666262397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20122753905736558444174931 30184130858604837666262397)
      ·
        refine ⟨11319049071976814124848399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30184130858604837666262397 11319049071976814124848399)
        ·
          refine ⟨16978573607965221187272599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11319049071976814124848399 16978573607965221187272599)
          ·
            refine ⟨25467860411947831780908899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16978573607965221187272599 25467860411947831780908899)
            ·
              refine ⟨38201790617921747671363349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25467860411947831780908899 38201790617921747671363349)
              ·
                refine ⟨1790708935215081922095157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38201790617921747671363349 1790708935215081922095157)
                ·
                  refine ⟨167878962676413930196421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1790708935215081922095157 167878962676413930196421)
                  ·
                    rfl

theorem cell20_367811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_367811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367811 prefixEnd_367811 := by exact prefixLift 367811
  have htrace : WordTrace (prefixWord ++ tailWord_367811) baseStart_367811 baseEnd_367811 := by
    simpa [prefixWord, tailWord_367811, baseEnd_367811] using wordTrace_append hprefix tailTrace_367811
  have hstable : (prefixWord ++ tailWord_367811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367811).length < 2 ^ (prefixWord ++ tailWord_367811).sum := by decide
  have hdescent : baseEnd_367811 < baseStart_367811 := by decide
  rcases family_descends (prefixWord ++ tailWord_367811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367831 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 2]
def baseStart_367831 : Nat := 118140960795 + 367831 * 2 ^ 59
def prefixEnd_367831 : Nat := 4983230072969 + 3 ^ 40 * 367831 * 2
def baseEnd_367831 : Nat := 167888091221382749529673

theorem tailTrace_367831 : CollatzResearch.WordTrace tailWord_367831 prefixEnd_367831 167888091221382749529673 := by
  unfold tailWord_367831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415898730418582378511347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8943932486945721585674231 13415898730418582378511347)
  ·
    refine ⟨20123848095627873567767021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13415898730418582378511347 20123848095627873567767021)
    ·
      refine ⟨7546443035860452587912633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20123848095627873567767021 7546443035860452587912633)
      ·
        refine ⟨5659832276895339440934475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546443035860452587912633 5659832276895339440934475)
        ·
          refine ⟨8489748415343009161401713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659832276895339440934475 8489748415343009161401713)
          ·
            refine ⟨6367311311507256871051285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8489748415343009161401713 6367311311507256871051285)
            ·
              refine ⟨298467717726902665830529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6367311311507256871051285 298467717726902665830529)
              ·
                refine ⟨223850788295176999372897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298467717726902665830529 223850788295176999372897)
                ·
                  refine ⟨167888091221382749529673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223850788295176999372897 167888091221382749529673)
                  ·
                    rfl

theorem cell20_367831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2].length) (baseStart_367831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367831 prefixEnd_367831 := by exact prefixLift 367831
  have htrace : WordTrace (prefixWord ++ tailWord_367831) baseStart_367831 baseEnd_367831 := by
    simpa [prefixWord, tailWord_367831, baseEnd_367831] using wordTrace_append hprefix tailTrace_367831
  have hstable : (prefixWord ++ tailWord_367831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367831).length < 2 ^ (prefixWord ++ tailWord_367831).sum := by decide
  have hdescent : baseEnd_367831 < baseStart_367831 := by decide
  rcases family_descends (prefixWord ++ tailWord_367831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367859 : List Nat := [1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_367859 : Nat := 118140960795 + 367859 * 2 ^ 59
def prefixEnd_367859 : Nat := 4983230072969 + 3 ^ 40 * 367859 * 2
def baseEnd_367859 : Nat := 55966957061446365532075

theorem tailTrace_367859 : CollatzResearch.WordTrace tailWord_367859 prefixEnd_367859 55966957061446365532075 := by
  unfold tailWord_367859
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416919974317143160530631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8944613316211428773687087 13416919974317143160530631)
  ·
    refine ⟨20125379961475714740795947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13416919974317143160530631 20125379961475714740795947)
    ·
      refine ⟨30188069942213572111193921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20125379961475714740795947 30188069942213572111193921)
      ·
        refine ⟨22641052456660179083395441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30188069942213572111193921 22641052456660179083395441)
        ·
          refine ⟨16980789342495134312546581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22641052456660179083395441 16980789342495134312546581)
          ·
            refine ⟨795974500429459420900621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16980789342495134312546581 795974500429459420900621)
            ·
              refine ⟨298490437661047282837733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795974500429459420900621 298490437661047282837733)
              ·
                refine ⟨55966957061446365532075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298490437661047282837733 55966957061446365532075)
                ·
                  rfl

theorem cell20_367859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_367859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367859 prefixEnd_367859 := by exact prefixLift 367859
  have htrace : WordTrace (prefixWord ++ tailWord_367859) baseStart_367859 baseEnd_367859 := by
    simpa [prefixWord, tailWord_367859, baseEnd_367859] using wordTrace_append hprefix tailTrace_367859
  have hstable : (prefixWord ++ tailWord_367859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367859).length < 2 ^ (prefixWord ++ tailWord_367859).sum := by decide
  have hdescent : baseEnd_367859 < baseStart_367859 := by decide
  rcases family_descends (prefixWord ++ tailWord_367859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367883 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_367883 : Nat := 118140960795 + 367883 * 2 ^ 59
def prefixEnd_367883 : Nat := 4983230072969 + 3 ^ 40 * 367883 * 2
def baseEnd_367883 : Nat := 167911825438301679796127

theorem tailTrace_367883 : CollatzResearch.WordTrace tailWord_367883 prefixEnd_367883 167911825438301679796127 := by
  unfold tailWord_367883
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417795326230195259404303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8945196884153463506269535 13417795326230195259404303)
  ·
    refine ⟨20126692989345292889106455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13417795326230195259404303 20126692989345292889106455)
    ·
      refine ⟨30190039484017939333659683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20126692989345292889106455 30190039484017939333659683)
      ·
        refine ⟨45285059226026909000489525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30190039484017939333659683 45285059226026909000489525)
        ·
          refine ⟨4245474302440022718795893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45285059226026909000489525 4245474302440022718795893)
          ·
            refine ⟨398013215853752129887115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4245474302440022718795893 398013215853752129887115)
            ·
              refine ⟨597019823780628194830673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398013215853752129887115 597019823780628194830673)
              ·
                refine ⟨447764867835471146123005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597019823780628194830673 447764867835471146123005)
                ·
                  refine ⟨167911825438301679796127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447764867835471146123005 167911825438301679796127)
                  ·
                    rfl

theorem cell20_367883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_367883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367883 prefixEnd_367883 := by exact prefixLift 367883
  have htrace : WordTrace (prefixWord ++ tailWord_367883) baseStart_367883 baseEnd_367883 := by
    simpa [prefixWord, tailWord_367883, baseEnd_367883] using wordTrace_append hprefix tailTrace_367883
  have hstable : (prefixWord ++ tailWord_367883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367883).length < 2 ^ (prefixWord ++ tailWord_367883).sum := by decide
  have hdescent : baseEnd_367883 < baseStart_367883 := by decide
  rcases family_descends (prefixWord ++ tailWord_367883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367914 : List Nat := [3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_367914 : Nat := 118140960795 + 367914 * 2 ^ 59
def prefixEnd_367914 : Nat := 4983230072969 + 3 ^ 40 * 367914 * 2
def baseEnd_367914 : Nat := 55975324894334449920889

theorem tailTrace_367914 : CollatzResearch.WordTrace tailWord_367914 prefixEnd_367914 55975324894334449920889 := by
  unfold tailWord_367914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354731497279471888445699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8945950659411925035855197 3354731497279471888445699)
  ·
    refine ⟨5032097245919207832668549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3354731497279471888445699 5032097245919207832668549)
    ·
      refine ⟨943518233609851468625353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5032097245919207832668549 943518233609851468625353)
      ·
        refine ⟨707638675207388601469015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943518233609851468625353 707638675207388601469015)
        ·
          refine ⟨1061458012811082902203523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707638675207388601469015 1061458012811082902203523)
          ·
            refine ⟨1592187019216624353305285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061458012811082902203523 1592187019216624353305285)
            ·
              refine ⟨298535066103117066244741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1592187019216624353305285 298535066103117066244741)
              ·
                refine ⟨55975324894334449920889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298535066103117066244741 55975324894334449920889)
                ·
                  rfl

theorem cell20_367914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_367914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367914 prefixEnd_367914 := by exact prefixLift 367914
  have htrace : WordTrace (prefixWord ++ tailWord_367914) baseStart_367914 baseEnd_367914 := by
    simpa [prefixWord, tailWord_367914, baseEnd_367914] using wordTrace_append hprefix tailTrace_367914
  have hstable : (prefixWord ++ tailWord_367914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367914).length < 2 ^ (prefixWord ++ tailWord_367914).sum := by decide
  have hdescent : baseEnd_367914 < baseStart_367914 := by decide
  rcases family_descends (prefixWord ++ tailWord_367914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367959 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 3]
def baseStart_367959 : Nat := 118140960795 + 367959 * 2 ^ 59
def prefixEnd_367959 : Nat := 4983230072969 + 3 ^ 40 * 367959 * 2
def baseEnd_367959 : Nat := 167946513909183193262483

theorem tailTrace_367959 : CollatzResearch.WordTrace tailWord_367959 prefixEnd_367959 167946513909183193262483 := by
  unfold tailWord_367959
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420567273954860239170931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8947044849303240159447287 13420567273954860239170931)
  ·
    refine ⟨20130850910932290358756397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13420567273954860239170931 20130850910932290358756397)
    ·
      refine ⟨7549069091599608884533649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20130850910932290358756397 7549069091599608884533649)
      ·
        refine ⟨5661801818699706663400237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7549069091599608884533649 5661801818699706663400237)
        ·
          refine ⟨2123175682012389998775089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5661801818699706663400237 2123175682012389998775089)
          ·
            refine ⟨1592381761509292499081317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2123175682012389998775089 1592381761509292499081317)
            ·
              refine ⟨298571580282992343577747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1592381761509292499081317 298571580282992343577747)
              ·
                refine ⟨447857370424488515366621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298571580282992343577747 447857370424488515366621)
                ·
                  refine ⟨167946513909183193262483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447857370424488515366621 167946513909183193262483)
                  ·
                    rfl

theorem cell20_367959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_367959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_367959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_367959 prefixEnd_367959 := by exact prefixLift 367959
  have htrace : WordTrace (prefixWord ++ tailWord_367959) baseStart_367959 baseEnd_367959 := by
    simpa [prefixWord, tailWord_367959, baseEnd_367959] using wordTrace_append hprefix tailTrace_367959
  have hstable : (prefixWord ++ tailWord_367959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367959).length < 2 ^ (prefixWord ++ tailWord_367959).sum := by decide
  have hdescent : baseEnd_367959 < baseStart_367959 := by decide
  rcases family_descends (prefixWord ++ tailWord_367959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368025 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_368025 : Nat := 118140960795 + 368025 * 2 ^ 59
def prefixEnd_368025 : Nat := 4983230072969 + 3 ^ 40 * 368025 * 2
def baseEnd_368025 : Nat := 167976638107580297062213

theorem tailTrace_368025 : CollatzResearch.WordTrace tailWord_368025 prefixEnd_368025 167976638107580297062213 := by
  unfold tailWord_368025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422974491715753511073529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8948649661143835674049019 13422974491715753511073529)
  ·
    refine ⟨10067230868786815133305147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13422974491715753511073529 10067230868786815133305147)
    ·
      refine ⟨15100846303180222699957721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067230868786815133305147 15100846303180222699957721)
      ·
        refine ⟨11325634727385167024968291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15100846303180222699957721 11325634727385167024968291)
        ·
          refine ⟨16988452091077750537452437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325634727385167024968291 16988452091077750537452437)
          ·
            refine ⟨796333691769269556443083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16988452091077750537452437 796333691769269556443083)
            ·
              refine ⟨1194500537653904334664625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796333691769269556443083 1194500537653904334664625)
              ·
                refine ⟨895875403240428250998469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194500537653904334664625 895875403240428250998469)
                ·
                  refine ⟨167976638107580297062213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895875403240428250998469 167976638107580297062213)
                  ·
                    rfl

theorem cell20_368025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_368025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368025 prefixEnd_368025 := by exact prefixLift 368025
  have htrace : WordTrace (prefixWord ++ tailWord_368025) baseStart_368025 baseEnd_368025 := by
    simpa [prefixWord, tailWord_368025, baseEnd_368025] using wordTrace_append hprefix tailTrace_368025
  have hstable : (prefixWord ++ tailWord_368025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368025).length < 2 ^ (prefixWord ++ tailWord_368025).sum := by decide
  have hdescent : baseEnd_368025 < baseStart_368025 := by decide
  rcases family_descends (prefixWord ++ tailWord_368025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368056 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_368056 : Nat := 118140960795 + 368056 * 2 ^ 59
def prefixEnd_368056 : Nat := 4983230072969 + 3 ^ 40 * 368056 * 2
def baseEnd_368056 : Nat := 167990787352281967028753

theorem tailTrace_368056 : CollatzResearch.WordTrace tailWord_368056 prefixEnd_368056 167990787352281967028753 := by
  unfold tailWord_368056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712052577301722902726011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8949403436402297203634681 6712052577301722902726011)
  ·
    refine ⟨10068078865952584354089017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6712052577301722902726011 10068078865952584354089017)
    ·
      refine ⟨7551059149464438265566763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10068078865952584354089017 7551059149464438265566763)
      ·
        refine ⟨11326588724196657398350145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551059149464438265566763 11326588724196657398350145)
        ·
          refine ⟨8494941543147493048762609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11326588724196657398350145 8494941543147493048762609)
          ·
            refine ⟨6371206157360619786571957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8494941543147493048762609 6371206157360619786571957)
            ·
              refine ⟨597300577252558104991121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6371206157360619786571957 597300577252558104991121)
              ·
                refine ⟨447975432939418578743341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597300577252558104991121 447975432939418578743341)
                ·
                  refine ⟨167990787352281967028753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447975432939418578743341 167990787352281967028753)
                  ·
                    rfl

theorem cell20_368056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_368056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368056 prefixEnd_368056 := by exact prefixLift 368056
  have htrace : WordTrace (prefixWord ++ tailWord_368056) baseStart_368056 baseEnd_368056 := by
    simpa [prefixWord, tailWord_368056, baseEnd_368056] using wordTrace_append hprefix tailTrace_368056
  have hstable : (prefixWord ++ tailWord_368056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368056).length < 2 ^ (prefixWord ++ tailWord_368056).sum := by decide
  have hdescent : baseEnd_368056 < baseStart_368056 := by decide
  rcases family_descends (prefixWord ++ tailWord_368056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368097 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 2]
def baseStart_368097 : Nat := 118140960795 + 368097 * 2 ^ 59
def prefixEnd_368097 : Nat := 4983230072969 + 3 ^ 40 * 368097 * 2
def baseEnd_368097 : Nat := 168009500869468046661919

theorem tailTrace_368097 : CollatzResearch.WordTrace tailWord_368097 prefixEnd_368097 168009500869468046661919 := by
  unfold tailWord_368097
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425600547454909807694545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8950400364969939871796363 13425600547454909807694545)
  ·
    refine ⟨10069200410591182355770909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13425600547454909807694545 10069200410591182355770909)
    ·
      refine ⟨3775950153971693383414091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10069200410591182355770909 3775950153971693383414091)
      ·
        refine ⟨5663925230957540075121137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775950153971693383414091 5663925230957540075121137)
        ·
          refine ⟨4247943923218155056340853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5663925230957540075121137 4247943923218155056340853)
          ·
            refine ⟨398244742801702036531955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4247943923218155056340853 398244742801702036531955)
            ·
              refine ⟨597367114202553054797933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398244742801702036531955 597367114202553054797933)
              ·
                refine ⟨224012667825957395549225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597367114202553054797933 224012667825957395549225)
                ·
                  refine ⟨168009500869468046661919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224012667825957395549225 168009500869468046661919)
                  ·
                    rfl

theorem cell20_368097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_368097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368097 prefixEnd_368097 := by exact prefixLift 368097
  have htrace : WordTrace (prefixWord ++ tailWord_368097) baseStart_368097 baseEnd_368097 := by
    simpa [prefixWord, tailWord_368097, baseEnd_368097] using wordTrace_append hprefix tailTrace_368097
  have hstable : (prefixWord ++ tailWord_368097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368097).length < 2 ^ (prefixWord ++ tailWord_368097).sum := by decide
  have hdescent : baseEnd_368097 < baseStart_368097 := by decide
  rcases family_descends (prefixWord ++ tailWord_368097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368114 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_368114 : Nat := 118140960795 + 368114 * 2 ^ 59
def prefixEnd_368114 : Nat := 4983230072969 + 3 ^ 40 * 368114 * 2
def baseEnd_368114 : Nat := 168017260132691543095183

theorem tailTrace_368114 : CollatzResearch.WordTrace tailWord_368114 prefixEnd_368114 168017260132691543095183 := by
  unfold tailWord_368114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356555147098330427765849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8950813725595547807375597 3356555147098330427765849)
  ·
    refine ⟨2517416360323747820824387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3356555147098330427765849 2517416360323747820824387)
    ·
      refine ⟨3776124540485621731236581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517416360323747820824387 3776124540485621731236581)
      ·
        refine ⟨708023351341054074606859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3776124540485621731236581 708023351341054074606859)
        ·
          refine ⟨1062035027011581111910289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708023351341054074606859 1062035027011581111910289)
          ·
            refine ⟨796526270258685833932717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062035027011581111910289 796526270258685833932717)
            ·
              refine ⟨298697351347007187724769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 796526270258685833932717 298697351347007187724769)
              ·
                refine ⟨224023013510255390793577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298697351347007187724769 224023013510255390793577)
                ·
                  refine ⟨168017260132691543095183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224023013510255390793577 168017260132691543095183)
                  ·
                    rfl

theorem cell20_368114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_368114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368114 prefixEnd_368114 := by exact prefixLift 368114
  have htrace : WordTrace (prefixWord ++ tailWord_368114) baseStart_368114 baseEnd_368114 := by
    simpa [prefixWord, tailWord_368114, baseEnd_368114] using wordTrace_append hprefix tailTrace_368114
  have hstable : (prefixWord ++ tailWord_368114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368114).length < 2 ^ (prefixWord ++ tailWord_368114).sum := by decide
  have hdescent : baseEnd_368114 < baseStart_368114 := by decide
  rcases family_descends (prefixWord ++ tailWord_368114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368118 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_368118 : Nat := 118140960795 + 368118 * 2 ^ 59
def prefixEnd_368118 : Nat := 4983230072969 + 3 ^ 40 * 368118 * 2
def baseEnd_368118 : Nat := 168019085841685306961833

theorem tailTrace_368118 : CollatzResearch.WordTrace tailWord_368118 prefixEnd_368118 168019085841685306961833 := by
  unfold tailWord_368118
  simp only [CollatzResearch.WordTrace]
  refine ⟨839147905023676899638063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8950910986919220262806005 839147905023676899638063)
  ·
    refine ⟨1258721857535515349457095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839147905023676899638063 1258721857535515349457095)
    ·
      refine ⟨1888082786303273024185643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258721857535515349457095 1888082786303273024185643)
      ·
        refine ⟨2832124179454909536278465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888082786303273024185643 2832124179454909536278465)
        ·
          refine ⟨2124093134591182152208849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832124179454909536278465 2124093134591182152208849)
          ·
            refine ⟨1593069850943386614156637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124093134591182152208849 1593069850943386614156637)
            ·
              refine ⟨597401194103769980308739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593069850943386614156637 597401194103769980308739)
              ·
                refine ⟨896101791155654970463109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597401194103769980308739 896101791155654970463109)
                ·
                  refine ⟨168019085841685306961833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896101791155654970463109 168019085841685306961833)
                  ·
                    rfl

theorem cell20_368118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_368118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368118 prefixEnd_368118 := by exact prefixLift 368118
  have htrace : WordTrace (prefixWord ++ tailWord_368118) baseStart_368118 baseEnd_368118 := by
    simpa [prefixWord, tailWord_368118, baseEnd_368118] using wordTrace_append hprefix tailTrace_368118
  have hstable : (prefixWord ++ tailWord_368118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368118).length < 2 ^ (prefixWord ++ tailWord_368118).sum := by decide
  have hdescent : baseEnd_368118 < baseStart_368118 := by decide
  rcases family_descends (prefixWord ++ tailWord_368118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368156 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_368156 : Nat := 118140960795 + 368156 * 2 ^ 59
def prefixEnd_368156 : Nat := 4983230072969 + 3 ^ 40 * 368156 * 2
def baseEnd_368156 : Nat := 168036430077126063695011

theorem tailTrace_368156 : CollatzResearch.WordTrace tailWord_368156 prefixEnd_368156 168036430077126063695011 := by
  unfold tailWord_368156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713876227120581442046161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8951834969494108589394881 6713876227120581442046161)
  ·
    refine ⟨5035407170340436081534621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6713876227120581442046161 5035407170340436081534621)
    ·
      refine ⟨1888277688877663530575483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5035407170340436081534621 1888277688877663530575483)
      ·
        refine ⟨2832416533316495295863225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888277688877663530575483 2832416533316495295863225)
        ·
          refine ⟨2124312399987371471897419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832416533316495295863225 2124312399987371471897419)
          ·
            refine ⟨3186468599981057207846129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124312399987371471897419 3186468599981057207846129)
            ·
              refine ⟨2389851449985792905884597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186468599981057207846129 2389851449985792905884597)
              ·
                refine ⟨224048573436168084926681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2389851449985792905884597 224048573436168084926681)
                ·
                  refine ⟨168036430077126063695011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224048573436168084926681 168036430077126063695011)
                  ·
                    rfl

theorem cell20_368156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_368156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368156 prefixEnd_368156 := by exact prefixLift 368156
  have htrace : WordTrace (prefixWord ++ tailWord_368156) baseStart_368156 baseEnd_368156 := by
    simpa [prefixWord, tailWord_368156, baseEnd_368156] using wordTrace_append hprefix tailTrace_368156
  have hstable : (prefixWord ++ tailWord_368156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368156).length < 2 ^ (prefixWord ++ tailWord_368156).sum := by decide
  have hdescent : baseEnd_368156 < baseStart_368156 := by decide
  rcases family_descends (prefixWord ++ tailWord_368156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368184 : List Nat := [2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_368184 : Nat := 118140960795 + 368184 * 2 ^ 59
def prefixEnd_368184 : Nat := 4983230072969 + 3 ^ 40 * 368184 * 2
def baseEnd_368184 : Nat := 56016403346694136920521

theorem tailTrace_368184 : CollatzResearch.WordTrace tailWord_368184 prefixEnd_368184 56016403346694136920521 := by
  unfold tailWord_368184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714386849069861833055803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8952515798759815777407737 6714386849069861833055803)
  ·
    refine ⟨10071580273604792749583705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714386849069861833055803 10071580273604792749583705)
    ·
      refine ⟨7553685205203594562187779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10071580273604792749583705 7553685205203594562187779)
      ·
        refine ⟨11330527807805391843281669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7553685205203594562187779 11330527807805391843281669)
        ·
          refine ⟨2124473963963510970615313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11330527807805391843281669 2124473963963510970615313)
          ·
            refine ⟨1593355472972633227961485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124473963963510970615313 1593355472972633227961485)
            ·
              refine ⟨597508302364737460485557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593355472972633227961485 597508302364737460485557)
              ·
                refine ⟨56016403346694136920521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 597508302364737460485557 56016403346694136920521)
                ·
                  rfl

theorem cell20_368184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_368184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368184 prefixEnd_368184 := by exact prefixLift 368184
  have htrace : WordTrace (prefixWord ++ tailWord_368184) baseStart_368184 baseEnd_368184 := by
    simpa [prefixWord, tailWord_368184, baseEnd_368184] using wordTrace_append hprefix tailTrace_368184
  have hstable : (prefixWord ++ tailWord_368184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368184).length < 2 ^ (prefixWord ++ tailWord_368184).sum := by decide
  have hdescent : baseEnd_368184 < baseStart_368184 := by decide
  rcases family_descends (prefixWord ++ tailWord_368184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368221 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_368221 : Nat := 118140960795 + 368221 * 2 ^ 59
def prefixEnd_368221 : Nat := 4983230072969 + 3 ^ 40 * 368221 * 2
def baseEnd_368221 : Nat := 168066097848274726528079

theorem tailTrace_368221 : CollatzResearch.WordTrace tailWord_368221 prefixEnd_368221 168066097848274726528079 := by
  unfold tailWord_368221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13430123199005678985208517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8953415466003785990139011 13430123199005678985208517)
  ·
    refine ⟨2518148099813564809726597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13430123199005678985208517 2518148099813564809726597)
    ·
      refine ⟨472152768715043401823737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2518148099813564809726597 472152768715043401823737)
      ·
        refine ⟨354114576536282551367803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472152768715043401823737 354114576536282551367803)
        ·
          refine ⟨531171864804423827051705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354114576536282551367803 531171864804423827051705)
          ·
            refine ⟨398378898603317870288779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531171864804423827051705 398378898603317870288779)
            ·
              refine ⟨597568347904976805433169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398378898603317870288779 597568347904976805433169)
              ·
                refine ⟨448176260928732604074877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597568347904976805433169 448176260928732604074877)
                ·
                  refine ⟨168066097848274726528079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448176260928732604074877 168066097848274726528079)
                  ·
                    rfl

theorem cell20_368221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_368221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368221 prefixEnd_368221 := by exact prefixLift 368221
  have htrace : WordTrace (prefixWord ++ tailWord_368221) baseStart_368221 baseEnd_368221 := by
    simpa [prefixWord, tailWord_368221, baseEnd_368221] using wordTrace_append hprefix tailTrace_368221
  have hstable : (prefixWord ++ tailWord_368221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368221).length < 2 ^ (prefixWord ++ tailWord_368221).sum := by decide
  have hdescent : baseEnd_368221 < baseStart_368221 := by decide
  rcases family_descends (prefixWord ++ tailWord_368221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368232 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_368232 : Nat := 118140960795 + 368232 * 2 ^ 59
def prefixEnd_368232 : Nat := 4983230072969 + 3 ^ 40 * 368232 * 2
def baseEnd_368232 : Nat := 168071118548007577161367

theorem tailTrace_368232 : CollatzResearch.WordTrace tailWord_368232 prefixEnd_368232 168071118548007577161367 := by
  unfold tailWord_368232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715262200982913931929475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8953682934643885242572633 6715262200982913931929475)
  ·
    refine ⟨10072893301474370897894213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6715262200982913931929475 10072893301474370897894213)
    ·
      refine ⟨1888667494026444543355165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10072893301474370897894213 1888667494026444543355165)
      ·
        refine ⟨708250310259916703758187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1888667494026444543355165 708250310259916703758187)
        ·
          refine ⟨1062375465389875055637281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708250310259916703758187 1062375465389875055637281)
          ·
            refine ⟨796781599042406291727961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062375465389875055637281 796781599042406291727961)
            ·
              refine ⟨597586199281804718795971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796781599042406291727961 597586199281804718795971)
              ·
                refine ⟨896379298922707078193957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597586199281804718795971 896379298922707078193957)
                ·
                  refine ⟨168071118548007577161367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896379298922707078193957 168071118548007577161367)
                  ·
                    rfl

theorem cell20_368232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_368232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368232 prefixEnd_368232 := by exact prefixLift 368232
  have htrace : WordTrace (prefixWord ++ tailWord_368232) baseStart_368232 baseEnd_368232 := by
    simpa [prefixWord, tailWord_368232, baseEnd_368232] using wordTrace_append hprefix tailTrace_368232
  have hstable : (prefixWord ++ tailWord_368232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368232).length < 2 ^ (prefixWord ++ tailWord_368232).sum := by decide
  have hdescent : baseEnd_368232 < baseStart_368232 := by decide
  rcases family_descends (prefixWord ++ tailWord_368232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368253 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_368253 : Nat := 118140960795 + 368253 * 2 ^ 59
def prefixEnd_368253 : Nat := 4983230072969 + 3 ^ 40 * 368253 * 2
def baseEnd_368253 : Nat := 168080703520224837461281

theorem tailTrace_368253 : CollatzResearch.WordTrace tailWord_368253 prefixEnd_368253 168080703520224837461281 := by
  unfold tailWord_368253
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431290334889748450373413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8954193556593165633582275 13431290334889748450373413)
  ·
    refine ⟨2518366937791827834445015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13431290334889748450373413 2518366937791827834445015)
    ·
      refine ⟨3777550406687741751667523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518366937791827834445015 3777550406687741751667523)
      ·
        refine ⟨5666325610031612627501285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777550406687741751667523 5666325610031612627501285)
        ·
          refine ⟨1062436051880927367656491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5666325610031612627501285 1062436051880927367656491)
          ·
            refine ⟨1593654077821391051484737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062436051880927367656491 1593654077821391051484737)
            ·
              refine ⟨1195240558366043288613553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593654077821391051484737 1195240558366043288613553)
              ·
                refine ⟨896430418774532466460165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195240558366043288613553 896430418774532466460165)
                ·
                  refine ⟨168080703520224837461281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896430418774532466460165 168080703520224837461281)
                  ·
                    rfl

theorem cell20_368253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_368253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368253 prefixEnd_368253 := by exact prefixLift 368253
  have htrace : WordTrace (prefixWord ++ tailWord_368253) baseStart_368253 baseEnd_368253 := by
    simpa [prefixWord, tailWord_368253, baseEnd_368253] using wordTrace_append hprefix tailTrace_368253
  have hstable : (prefixWord ++ tailWord_368253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368253).length < 2 ^ (prefixWord ++ tailWord_368253).sum := by decide
  have hdescent : baseEnd_368253 < baseStart_368253 := by decide
  rcases family_descends (prefixWord ++ tailWord_368253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368287 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_368287 : Nat := 118140960795 + 368287 * 2 ^ 59
def prefixEnd_368287 : Nat := 4983230072969 + 3 ^ 40 * 368287 * 2
def baseEnd_368287 : Nat := 168096222046671830327809

theorem tailTrace_368287 : CollatzResearch.WordTrace tailWord_368287 prefixEnd_368287 168096222046671830327809 := by
  unfold tailWord_368287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432530416766572257111115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8955020277844381504740743 13432530416766572257111115)
  ·
    refine ⟨20148795625149858385666673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13432530416766572257111115 20148795625149858385666673)
    ·
      refine ⟨15111596718862393789250005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20148795625149858385666673 15111596718862393789250005)
      ·
        refine ⟨354178048098337354435547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15111596718862393789250005 354178048098337354435547)
        ·
          refine ⟨531267072147506031653321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354178048098337354435547 531267072147506031653321)
          ·
            refine ⟨398450304110629523739991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531267072147506031653321 398450304110629523739991)
            ·
              refine ⟨597675456165944285609987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398450304110629523739991 597675456165944285609987)
              ·
                refine ⟨896513184248916428414981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597675456165944285609987 896513184248916428414981)
                ·
                  refine ⟨168096222046671830327809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896513184248916428414981 168096222046671830327809)
                  ·
                    rfl

theorem cell20_368287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_368287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368287 prefixEnd_368287 := by exact prefixLift 368287
  have htrace : WordTrace (prefixWord ++ tailWord_368287) baseStart_368287 baseEnd_368287 := by
    simpa [prefixWord, tailWord_368287, baseEnd_368287] using wordTrace_append hprefix tailTrace_368287
  have hstable : (prefixWord ++ tailWord_368287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368287).length < 2 ^ (prefixWord ++ tailWord_368287).sum := by decide
  have hdescent : baseEnd_368287 < baseStart_368287 := by decide
  rcases family_descends (prefixWord ++ tailWord_368287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368312 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_368312 : Nat := 118140960795 + 368312 * 2 ^ 59
def prefixEnd_368312 : Nat := 4983230072969 + 3 ^ 40 * 368312 * 2
def baseEnd_368312 : Nat := 168107632727882854494373

theorem tailTrace_368312 : CollatzResearch.WordTrace tailWord_368312 prefixEnd_368312 168107632727882854494373 := by
  unfold tailWord_368312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716721120838000763385595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8955628161117334351180793 6716721120838000763385595)
  ·
    refine ⟨10075081681257001145078393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716721120838000763385595 10075081681257001145078393)
    ·
      refine ⟨7556311260942750858808795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10075081681257001145078393 7556311260942750858808795)
      ·
        refine ⟨11334466891414126288213193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7556311260942750858808795 11334466891414126288213193)
        ·
          refine ⟨8500850168560594716159895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11334466891414126288213193 8500850168560594716159895)
          ·
            refine ⟨12751275252840892074239843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8500850168560594716159895 12751275252840892074239843)
            ·
              refine ⟨19126912879261338111359765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12751275252840892074239843 19126912879261338111359765)
              ·
                refine ⟨896574041215375223969989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19126912879261338111359765 896574041215375223969989)
                ·
                  refine ⟨168107632727882854494373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896574041215375223969989 168107632727882854494373)
                  ·
                    rfl

theorem cell20_368312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_368312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368312 prefixEnd_368312 := by exact prefixLift 368312
  have htrace : WordTrace (prefixWord ++ tailWord_368312) baseStart_368312 baseEnd_368312 := by
    simpa [prefixWord, tailWord_368312, baseEnd_368312] using wordTrace_append hprefix tailTrace_368312
  have hstable : (prefixWord ++ tailWord_368312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368312).length < 2 ^ (prefixWord ++ tailWord_368312).sum := by decide
  have hdescent : baseEnd_368312 < baseStart_368312 := by decide
  rcases family_descends (prefixWord ++ tailWord_368312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368319 : List Nat := [1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_368319 : Nat := 118140960795 + 368319 * 2 ^ 59
def prefixEnd_368319 : Nat := 4983230072969 + 3 ^ 40 * 368319 * 2
def baseEnd_368319 : Nat := 56036942572873980420337

theorem tailTrace_368319 : CollatzResearch.WordTrace tailWord_368319 prefixEnd_368319 56036942572873980420337 := by
  unfold tailWord_368319
  simp only [CollatzResearch.WordTrace]
  refine ⟨13433697552650641722276011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8955798368433761148184007 13433697552650641722276011)
  ·
    refine ⟨20150546328975962583414017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13433697552650641722276011 20150546328975962583414017)
    ·
      refine ⟨15112909746731971937560513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20150546328975962583414017 15112909746731971937560513)
      ·
        refine ⟨11334682310048978953170385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15112909746731971937560513 11334682310048978953170385)
        ·
          refine ⟨8501011732536734214877789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11334682310048978953170385 8501011732536734214877789)
          ·
            refine ⟨3187879399701275330579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8501011732536734214877789 3187879399701275330579171)
            ·
              refine ⟨4781819099551912995868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187879399701275330579171 4781819099551912995868757)
              ·
                refine ⟨56036942572873980420337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4781819099551912995868757 56036942572873980420337)
                ·
                  rfl

theorem cell20_368319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_368319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368319 prefixEnd_368319 := by exact prefixLift 368319
  have htrace : WordTrace (prefixWord ++ tailWord_368319) baseStart_368319 baseEnd_368319 := by
    simpa [prefixWord, tailWord_368319, baseEnd_368319] using wordTrace_append hprefix tailTrace_368319
  have hstable : (prefixWord ++ tailWord_368319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368319).length < 2 ^ (prefixWord ++ tailWord_368319).sum := by decide
  have hdescent : baseEnd_368319 < baseStart_368319 := by decide
  rcases family_descends (prefixWord ++ tailWord_368319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368346 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_368346 : Nat := 118140960795 + 368346 * 2 ^ 59
def prefixEnd_368346 : Nat := 4983230072969 + 3 ^ 40 * 368346 * 2
def baseEnd_368346 : Nat := 168123151254329847360901

theorem tailTrace_368346 : CollatzResearch.WordTrace tailWord_368346 prefixEnd_368346 168123151254329847360901 := by
  unfold tailWord_368346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358670580888206333377223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8956454882368550222339261 3358670580888206333377223)
  ·
    refine ⟨5038005871332309500065835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3358670580888206333377223 5038005871332309500065835)
    ·
      refine ⟨7557008806998464250098753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5038005871332309500065835 7557008806998464250098753)
      ·
        refine ⟨5667756605248848187574065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7557008806998464250098753 5667756605248848187574065)
        ·
          refine ⟨4250817453936636140680549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5667756605248848187574065 4250817453936636140680549)
          ·
            refine ⟨797028272613119276377603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4250817453936636140680549 797028272613119276377603)
            ·
              refine ⟨1195542408919678914566405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797028272613119276377603 1195542408919678914566405)
              ·
                refine ⟨224164201672439796481201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1195542408919678914566405 224164201672439796481201)
                ·
                  refine ⟨168123151254329847360901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224164201672439796481201 168123151254329847360901)
                  ·
                    rfl

theorem cell20_368346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_368346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368346 prefixEnd_368346 := by exact prefixLift 368346
  have htrace : WordTrace (prefixWord ++ tailWord_368346) baseStart_368346 baseEnd_368346 := by
    simpa [prefixWord, tailWord_368346, baseEnd_368346] using wordTrace_append hprefix tailTrace_368346
  have hstable : (prefixWord ++ tailWord_368346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368346).length < 2 ^ (prefixWord ++ tailWord_368346).sum := by decide
  have hdescent : baseEnd_368346 < baseStart_368346 := by decide
  rcases family_descends (prefixWord ++ tailWord_368346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368349 : List Nat := [1, 4, 3, 3, 2, 1, 1, 5]
def baseStart_368349 : Nat := 118140960795 + 368349 * 2 ^ 59
def prefixEnd_368349 : Nat := 4983230072969 + 3 ^ 40 * 368349 * 2
def baseEnd_368349 : Nat := 56041506845358390086963

theorem tailTrace_368349 : CollatzResearch.WordTrace tailWord_368349 prefixEnd_368349 56041506845358390086963 := by
  unfold tailWord_368349
  simp only [CollatzResearch.WordTrace]
  refine ⟨13434791742541956845868101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8956527828361304563912067 13434791742541956845868101)
  ·
    refine ⟨2519023451726616908600269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13434791742541956845868101 2519023451726616908600269)
    ·
      refine ⟨944633794397481340725101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2519023451726616908600269 944633794397481340725101)
      ·
        refine ⟨354237672899055502771913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 944633794397481340725101 354237672899055502771913)
        ·
          refine ⟨265678254674291627078935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354237672899055502771913 265678254674291627078935)
          ·
            refine ⟨398517382011437440618403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265678254674291627078935 398517382011437440618403)
            ·
              refine ⟨597776073017156160927605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398517382011437440618403 597776073017156160927605)
              ·
                refine ⟨56041506845358390086963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 597776073017156160927605 56041506845358390086963)
                ·
                  rfl

theorem cell20_368349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_368349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368349 prefixEnd_368349 := by exact prefixLift 368349
  have htrace : WordTrace (prefixWord ++ tailWord_368349) baseStart_368349 baseEnd_368349 := by
    simpa [prefixWord, tailWord_368349, baseEnd_368349] using wordTrace_append hprefix tailTrace_368349
  have hstable : (prefixWord ++ tailWord_368349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368349).length < 2 ^ (prefixWord ++ tailWord_368349).sum := by decide
  have hdescent : baseEnd_368349 < baseStart_368349 := by decide
  rcases family_descends (prefixWord ++ tailWord_368349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368353 : List Nat := [1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_368353 : Nat := 118140960795 + 368353 * 2 ^ 59
def prefixEnd_368353 : Nat := 4983230072969 + 3 ^ 40 * 368353 * 2
def baseEnd_368353 : Nat := 56042115415022978042513

theorem tailTrace_368353 : CollatzResearch.WordTrace tailWord_368353 prefixEnd_368353 56042115415022978042513 := by
  unfold tailWord_368353
  simp only [CollatzResearch.WordTrace]
  refine ⟨13434937634527465529013713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8956625089684977019342475 13434937634527465529013713)
  ·
    refine ⟨10076203225895599146760285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13434937634527465529013713 10076203225895599146760285)
    ·
      refine ⟨3778576209710849680035107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10076203225895599146760285 3778576209710849680035107)
      ·
        refine ⟨5667864314566274520052661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778576209710849680035107 5667864314566274520052661)
        ·
          refine ⟨531362279490588236254937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5667864314566274520052661 531362279490588236254937)
          ·
            refine ⟨398521709617941177191203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531362279490588236254937 398521709617941177191203)
            ·
              refine ⟨597782564426911765786805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398521709617941177191203 597782564426911765786805)
              ·
                refine ⟨56042115415022978042513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 597782564426911765786805 56042115415022978042513)
                ·
                  rfl

theorem cell20_368353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_368353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368353 prefixEnd_368353 := by exact prefixLift 368353
  have htrace : WordTrace (prefixWord ++ tailWord_368353) baseStart_368353 baseEnd_368353 := by
    simpa [prefixWord, tailWord_368353, baseEnd_368353] using wordTrace_append hprefix tailTrace_368353
  have hstable : (prefixWord ++ tailWord_368353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368353).length < 2 ^ (prefixWord ++ tailWord_368353).sum := by decide
  have hdescent : baseEnd_368353 < baseStart_368353 := by decide
  rcases family_descends (prefixWord ++ tailWord_368353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368360 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_368360 : Nat := 118140960795 + 368360 * 2 ^ 59
def prefixEnd_368360 : Nat := 4983230072969 + 3 ^ 40 * 368360 * 2
def baseEnd_368360 : Nat := 168129541235808020894177

theorem tailTrace_368360 : CollatzResearch.WordTrace tailWord_368360 prefixEnd_368360 168129541235808020894177 := by
  unfold tailWord_368360
  simp only [CollatzResearch.WordTrace]
  refine ⟨6717596472751052862259267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8956795297001403816345689 6717596472751052862259267)
  ·
    refine ⟨10076394709126579293388901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6717596472751052862259267 10076394709126579293388901)
    ·
      refine ⟨1889324007961233617510419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10076394709126579293388901 1889324007961233617510419)
      ·
        refine ⟨2833986011941850426265629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889324007961233617510419 2833986011941850426265629)
        ·
          refine ⟨1062744754478193909849611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2833986011941850426265629 1062744754478193909849611)
          ·
            refine ⟨1594117131717290864774417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062744754478193909849611 1594117131717290864774417)
            ·
              refine ⟨1195587848787968148580813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594117131717290864774417 1195587848787968148580813)
              ·
                refine ⟨448345443295488055717805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195587848787968148580813 448345443295488055717805)
                ·
                  refine ⟨168129541235808020894177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448345443295488055717805 168129541235808020894177)
                  ·
                    rfl

theorem cell20_368360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_368360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368360 prefixEnd_368360 := by exact prefixLift 368360
  have htrace : WordTrace (prefixWord ++ tailWord_368360) baseStart_368360 baseEnd_368360 := by
    simpa [prefixWord, tailWord_368360, baseEnd_368360] using wordTrace_append hprefix tailTrace_368360
  have hstable : (prefixWord ++ tailWord_368360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368360).length < 2 ^ (prefixWord ++ tailWord_368360).sum := by decide
  have hdescent : baseEnd_368360 < baseStart_368360 := by decide
  rcases family_descends (prefixWord ++ tailWord_368360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368390 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_368390 : Nat := 118140960795 + 368390 * 2 ^ 59
def prefixEnd_368390 : Nat := 4983230072969 + 3 ^ 40 * 368390 * 2
def baseEnd_368390 : Nat := 168143234053261249894055

theorem tailTrace_368390 : CollatzResearch.WordTrace tailWord_368390 prefixEnd_368390 168143234053261249894055 := by
  unfold tailWord_368390
  simp only [CollatzResearch.WordTrace]
  refine ⟨419883972981044401503457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8957524756928947232073749 419883972981044401503457)
  ·
    refine ⟨314912979735783301127593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 419883972981044401503457 314912979735783301127593)
    ·
      refine ⟨236184734801837475845695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314912979735783301127593 236184734801837475845695)
      ·
        refine ⟨354277102202756213768543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236184734801837475845695 354277102202756213768543)
        ·
          refine ⟨531415653304134320652815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354277102202756213768543 531415653304134320652815)
          ·
            refine ⟨797123479956201480979223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531415653304134320652815 797123479956201480979223)
            ·
              refine ⟨1195685219934302221468835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797123479956201480979223 1195685219934302221468835)
              ·
                refine ⟨1793527829901453332203253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195685219934302221468835 1793527829901453332203253)
                ·
                  refine ⟨168143234053261249894055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1793527829901453332203253 168143234053261249894055)
                  ·
                    rfl

theorem cell20_368390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_368390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368390 prefixEnd_368390 := by exact prefixLift 368390
  have htrace : WordTrace (prefixWord ++ tailWord_368390) baseStart_368390 baseEnd_368390 := by
    simpa [prefixWord, tailWord_368390, baseEnd_368390] using wordTrace_append hprefix tailTrace_368390
  have hstable : (prefixWord ++ tailWord_368390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368390).length < 2 ^ (prefixWord ++ tailWord_368390).sum := by decide
  have hdescent : baseEnd_368390 < baseStart_368390 := by decide
  rcases family_descends (prefixWord ++ tailWord_368390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368397 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 4]
def baseStart_368397 : Nat := 118140960795 + 368397 * 2 ^ 59
def prefixEnd_368397 : Nat := 4983230072969 + 3 ^ 40 * 368397 * 2
def baseEnd_368397 : Nat := 168146429044000336660693

theorem tailTrace_368397 : CollatzResearch.WordTrace tailWord_368397 prefixEnd_368397 168146429044000336660693 := by
  unfold tailWord_368397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436542446368061043615445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8957694964245374029076963 13436542446368061043615445)
  ·
    refine ⟨314918963586751430709737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13436542446368061043615445 314918963586751430709737)
    ·
      refine ⟨236189222690063573032303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314918963586751430709737 236189222690063573032303)
      ·
        refine ⟨354283834035095359548455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236189222690063573032303 354283834035095359548455)
        ·
          refine ⟨531425751052643039322683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354283834035095359548455 531425751052643039322683)
          ·
            refine ⟨797138626578964558984025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531425751052643039322683 797138626578964558984025)
            ·
              refine ⟨597853969934223419238019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797138626578964558984025 597853969934223419238019)
              ·
                refine ⟨896780954901335128857029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597853969934223419238019 896780954901335128857029)
                ·
                  refine ⟨168146429044000336660693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896780954901335128857029 168146429044000336660693)
                  ·
                    rfl

theorem cell20_368397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_368397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368397 prefixEnd_368397 := by exact prefixLift 368397
  have htrace : WordTrace (prefixWord ++ tailWord_368397) baseStart_368397 baseEnd_368397 := by
    simpa [prefixWord, tailWord_368397, baseEnd_368397] using wordTrace_append hprefix tailTrace_368397
  have hstable : (prefixWord ++ tailWord_368397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368397).length < 2 ^ (prefixWord ++ tailWord_368397).sum := by decide
  have hdescent : baseEnd_368397 < baseStart_368397 := by decide
  rcases family_descends (prefixWord ++ tailWord_368397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368398 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_368398 : Nat := 118140960795 + 368398 * 2 ^ 59
def prefixEnd_368398 : Nat := 4983230072969 + 3 ^ 40 * 368398 * 2
def baseEnd_368398 : Nat := 168146885471248777627355

theorem tailTrace_368398 : CollatzResearch.WordTrace tailWord_368398 prefixEnd_368398 168146885471248777627355 := by
  unfold tailWord_368398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679572364920554776800231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8957719279576292142934565 1679572364920554776800231)
  ·
    refine ⟨2519358547380832165200347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679572364920554776800231 2519358547380832165200347)
    ·
      refine ⟨3779037821071248247800521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519358547380832165200347 3779037821071248247800521)
      ·
        refine ⟨2834278365803436185850391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779037821071248247800521 2834278365803436185850391)
        ·
          refine ⟨4251417548705154278775587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834278365803436185850391 4251417548705154278775587)
          ·
            refine ⟨6377126323057731418163381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251417548705154278775587 6377126323057731418163381)
            ·
              refine ⟨597855592786662320452817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6377126323057731418163381 597855592786662320452817)
              ·
                refine ⟨448391694589996740339613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597855592786662320452817 448391694589996740339613)
                ·
                  refine ⟨168146885471248777627355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448391694589996740339613 168146885471248777627355)
                  ·
                    rfl

theorem cell20_368398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_368398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368398 prefixEnd_368398 := by exact prefixLift 368398
  have htrace : WordTrace (prefixWord ++ tailWord_368398) baseStart_368398 baseEnd_368398 := by
    simpa [prefixWord, tailWord_368398, baseEnd_368398] using wordTrace_append hprefix tailTrace_368398
  have hstable : (prefixWord ++ tailWord_368398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368398).length < 2 ^ (prefixWord ++ tailWord_368398).sum := by decide
  have hdescent : baseEnd_368398 < baseStart_368398 := by decide
  rcases family_descends (prefixWord ++ tailWord_368398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368405 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_368405 : Nat := 118140960795 + 368405 * 2 ^ 59
def prefixEnd_368405 : Nat := 4983230072969 + 3 ^ 40 * 368405 * 2
def baseEnd_368405 : Nat := 168150080461987864393993

theorem tailTrace_368405 : CollatzResearch.WordTrace tailWord_368405 prefixEnd_368405 168150080461987864393993 := by
  unfold tailWord_368405
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436834230339078409906669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8957889486892718939937779 13436834230339078409906669)
  ·
    refine ⟨5038812836377154403715001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13436834230339078409906669 5038812836377154403715001)
    ·
      refine ⟨3779109627282865802786251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5038812836377154403715001 3779109627282865802786251)
      ·
        refine ⟨5668664440924298704179377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779109627282865802786251 5668664440924298704179377)
        ·
          refine ⟨4251498330693224028134533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668664440924298704179377 4251498330693224028134533)
          ·
            refine ⟨797155937004979505275225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4251498330693224028134533 797155937004979505275225)
            ·
              refine ⟨597866952753734628956419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797155937004979505275225 597866952753734628956419)
              ·
                refine ⟨896800429130601943434629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597866952753734628956419 896800429130601943434629)
                ·
                  refine ⟨168150080461987864393993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896800429130601943434629 168150080461987864393993)
                  ·
                    rfl

theorem cell20_368405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_368405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368405 prefixEnd_368405 := by exact prefixLift 368405
  have htrace : WordTrace (prefixWord ++ tailWord_368405) baseStart_368405 baseEnd_368405 := by
    simpa [prefixWord, tailWord_368405, baseEnd_368405] using wordTrace_append hprefix tailTrace_368405
  have hstable : (prefixWord ++ tailWord_368405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368405).length < 2 ^ (prefixWord ++ tailWord_368405).sum := by decide
  have hdescent : baseEnd_368405 < baseStart_368405 := by decide
  rcases family_descends (prefixWord ++ tailWord_368405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368419 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_368419 : Nat := 118140960795 + 368419 * 2 ^ 59
def prefixEnd_368419 : Nat := 4983230072969 + 3 ^ 40 * 368419 * 2
def baseEnd_368419 : Nat := 168156470443466037927269

theorem tailTrace_368419 : CollatzResearch.WordTrace tailWord_368419 prefixEnd_368419 168156470443466037927269 := by
  unfold tailWord_368419
  simp only [CollatzResearch.WordTrace]
  refine ⟨13437344852288358800916311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8958229901525572533944207 13437344852288358800916311)
  ·
    refine ⟨20156017278432538201374467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13437344852288358800916311 20156017278432538201374467)
    ·
      refine ⟨30234025917648807302061701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20156017278432538201374467 30234025917648807302061701)
      ·
        refine ⟨5668879859559151369136569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30234025917648807302061701 5668879859559151369136569)
        ·
          refine ⟨4251659894669363526852427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668879859559151369136569 4251659894669363526852427)
          ·
            refine ⟨6377489842004045290278641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251659894669363526852427 6377489842004045290278641)
            ·
              refine ⟨4783117381503033967708981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6377489842004045290278641 4783117381503033967708981)
              ·
                refine ⟨448417254515909434472717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4783117381503033967708981 448417254515909434472717)
                ·
                  refine ⟨168156470443466037927269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448417254515909434472717 168156470443466037927269)
                  ·
                    rfl

theorem cell20_368419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_368419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368419 prefixEnd_368419 := by exact prefixLift 368419
  have htrace : WordTrace (prefixWord ++ tailWord_368419) baseStart_368419 baseEnd_368419 := by
    simpa [prefixWord, tailWord_368419, baseEnd_368419] using wordTrace_append hprefix tailTrace_368419
  have hstable : (prefixWord ++ tailWord_368419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368419).length < 2 ^ (prefixWord ++ tailWord_368419).sum := by decide
  have hdescent : baseEnd_368419 < baseStart_368419 := by decide
  rcases family_descends (prefixWord ++ tailWord_368419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368436 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_368436 : Nat := 118140960795 + 368436 * 2 ^ 59
def prefixEnd_368436 : Nat := 4983230072969 + 3 ^ 40 * 368436 * 2
def baseEnd_368436 : Nat := 168164229706689534360533

theorem tailTrace_368436 : CollatzResearch.WordTrace tailWord_368436 prefixEnd_368436 168164229706689534360533 := by
  unfold tailWord_368436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718982446613385352142581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8958643262151180469523441 6718982446613385352142581)
  ·
    refine ⟨629904604370004876763367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6718982446613385352142581 629904604370004876763367)
    ·
      refine ⟨944856906555007315145051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629904604370004876763367 944856906555007315145051)
      ·
        refine ⟨1417285359832510972717577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944856906555007315145051 1417285359832510972717577)
        ·
          refine ⟨1062964019874383229538183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1417285359832510972717577 1062964019874383229538183)
          ·
            refine ⟨1594446029811574844307275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062964019874383229538183 1594446029811574844307275)
            ·
              refine ⟨2391669044717362266460913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594446029811574844307275 2391669044717362266460913)
              ·
                refine ⟨1793751783538021699845685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391669044717362266460913 1793751783538021699845685)
                ·
                  refine ⟨168164229706689534360533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1793751783538021699845685 168164229706689534360533)
                  ·
                    rfl

theorem cell20_368436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_368436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368436 prefixEnd_368436 := by exact prefixLift 368436
  have htrace : WordTrace (prefixWord ++ tailWord_368436) baseStart_368436 baseEnd_368436 := by
    simpa [prefixWord, tailWord_368436, baseEnd_368436] using wordTrace_append hprefix tailTrace_368436
  have hstable : (prefixWord ++ tailWord_368436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368436).length < 2 ^ (prefixWord ++ tailWord_368436).sum := by decide
  have hdescent : baseEnd_368436 < baseStart_368436 := by decide
  rcases family_descends (prefixWord ++ tailWord_368436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368457 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_368457 : Nat := 118140960795 + 368457 * 2 ^ 59
def prefixEnd_368457 : Nat := 4983230072969 + 3 ^ 40 * 368457 * 2
def baseEnd_368457 : Nat := 168173814678906794660447

theorem tailTrace_368457 : CollatzResearch.WordTrace tailWord_368457 prefixEnd_368457 168173814678906794660447 := by
  unfold tailWord_368457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438730826150691290799625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8959153884100460860533083 13438730826150691290799625)
  ·
    refine ⟨10079048119613018468099719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13438730826150691290799625 10079048119613018468099719)
    ·
      refine ⟨15118572179419527702149579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10079048119613018468099719 15118572179419527702149579)
      ·
        refine ⟨22677858269129291553224369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118572179419527702149579 22677858269129291553224369)
        ·
          refine ⟨17008393701846968664918277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22677858269129291553224369 17008393701846968664918277)
          ·
            refine ⟨3189073819096306624672177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17008393701846968664918277 3189073819096306624672177)
            ·
              refine ⟨2391805364322229968504133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189073819096306624672177 2391805364322229968504133)
              ·
                refine ⟨448463505810418119094525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2391805364322229968504133 448463505810418119094525)
                ·
                  refine ⟨168173814678906794660447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448463505810418119094525 168173814678906794660447)
                  ·
                    rfl

theorem cell20_368457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_368457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368457 prefixEnd_368457 := by exact prefixLift 368457
  have htrace : WordTrace (prefixWord ++ tailWord_368457) baseStart_368457 baseEnd_368457 := by
    simpa [prefixWord, tailWord_368457, baseEnd_368457] using wordTrace_append hprefix tailTrace_368457
  have hstable : (prefixWord ++ tailWord_368457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368457).length < 2 ^ (prefixWord ++ tailWord_368457).sum := by decide
  have hdescent : baseEnd_368457 < baseStart_368457 := by decide
  rcases family_descends (prefixWord ++ tailWord_368457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368460 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_368460 : Nat := 118140960795 + 368460 * 2 ^ 59
def prefixEnd_368460 : Nat := 4983230072969 + 3 ^ 40 * 368460 * 2
def baseEnd_368460 : Nat := 168175183960652117560435

theorem tailTrace_368460 : CollatzResearch.WordTrace tailWord_368460 prefixEnd_368460 168175183960652117560435 := by
  unfold tailWord_368460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719420122569911401579417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8959226830093215202105889 6719420122569911401579417)
  ·
    refine ⟨5039565091927433551184563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6719420122569911401579417 5039565091927433551184563)
    ·
      refine ⟨7559347637891150326776845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039565091927433551184563 7559347637891150326776845)
      ·
        refine ⟨2834755364209181372541317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7559347637891150326776845 2834755364209181372541317)
        ·
          refine ⟨531516630789221507351497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2834755364209181372541317 531516630789221507351497)
          ·
            refine ⟨398637473091916130513623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531516630789221507351497 398637473091916130513623)
            ·
              refine ⟨597956209637874195770435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398637473091916130513623 597956209637874195770435)
              ·
                refine ⟨896934314456811293655653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597956209637874195770435 896934314456811293655653)
                ·
                  refine ⟨168175183960652117560435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896934314456811293655653 168175183960652117560435)
                  ·
                    rfl

theorem cell20_368460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_368460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368460 prefixEnd_368460 := by exact prefixLift 368460
  have htrace : WordTrace (prefixWord ++ tailWord_368460) baseStart_368460 baseEnd_368460 := by
    simpa [prefixWord, tailWord_368460, baseEnd_368460] using wordTrace_append hprefix tailTrace_368460
  have hstable : (prefixWord ++ tailWord_368460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368460).length < 2 ^ (prefixWord ++ tailWord_368460).sum := by decide
  have hdescent : baseEnd_368460 < baseStart_368460 := by decide
  rcases family_descends (prefixWord ++ tailWord_368460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368515 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 2]
def baseStart_368515 : Nat := 118140960795 + 368515 * 2 ^ 59
def prefixEnd_368515 : Nat := 4983230072969 + 3 ^ 40 * 368515 * 2
def baseEnd_368515 : Nat := 168200287459316370726877

theorem tailTrace_368515 : CollatzResearch.WordTrace tailWord_368515 prefixEnd_368515 168200287459316370726877 := by
  unfold tailWord_368515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440846259940567196410999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8960564173293711464273999 13440846259940567196410999)
  ·
    refine ⟨20161269389910850794616499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13440846259940567196410999 20161269389910850794616499)
    ·
      refine ⟨30241904084866276191924749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20161269389910850794616499 30241904084866276191924749)
      ·
        refine ⟨11340714031824853571971781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30241904084866276191924749 11340714031824853571971781)
        ·
          refine ⟨2126383880967160044744709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11340714031824853571971781 2126383880967160044744709)
          ·
            refine ⟨398696977681342508389633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2126383880967160044744709 398696977681342508389633)
            ·
              refine ⟨299022733261006881292225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398696977681342508389633 299022733261006881292225)
              ·
                refine ⟨224267049945755160969169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299022733261006881292225 224267049945755160969169)
                ·
                  refine ⟨168200287459316370726877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224267049945755160969169 168200287459316370726877)
                  ·
                    rfl

theorem cell20_368515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2].length) (baseStart_368515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368515 prefixEnd_368515 := by exact prefixLift 368515
  have htrace : WordTrace (prefixWord ++ tailWord_368515) baseStart_368515 baseEnd_368515 := by
    simpa [prefixWord, tailWord_368515, baseEnd_368515] using wordTrace_append hprefix tailTrace_368515
  have hstable : (prefixWord ++ tailWord_368515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368515).length < 2 ^ (prefixWord ++ tailWord_368515).sum := by decide
  have hdescent : baseEnd_368515 < baseStart_368515 := by decide
  rcases family_descends (prefixWord ++ tailWord_368515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368522 : List Nat := [3, 1, 2, 4, 3, 1, 1, 5]
def baseStart_368522 : Nat := 118140960795 + 368522 * 2 ^ 59
def prefixEnd_368522 : Nat := 4983230072969 + 3 ^ 40 * 368522 * 2
def baseEnd_368522 : Nat := 56067827483351819164505

theorem tailTrace_368522 : CollatzResearch.WordTrace tailWord_368522 prefixEnd_368522 56067827483351819164505 := by
  unfold tailWord_368522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360275392728801847978955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8960734380610138261277213 3360275392728801847978955)
  ·
    refine ⟨5040413089093202771968433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3360275392728801847978955 5040413089093202771968433)
    ·
      refine ⟨3780309816819902078976325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5040413089093202771968433 3780309816819902078976325)
      ·
        refine ⟨708808090653731639808061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3780309816819902078976325 708808090653731639808061)
        ·
          refine ⟨265803033995149364928023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708808090653731639808061 265803033995149364928023)
          ·
            refine ⟨398704550992724047392035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265803033995149364928023 398704550992724047392035)
            ·
              refine ⟨598056826489086071088053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398704550992724047392035 598056826489086071088053)
              ·
                refine ⟨56067827483351819164505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 598056826489086071088053 56067827483351819164505)
                ·
                  rfl

theorem cell20_368522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_368522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368522 prefixEnd_368522 := by exact prefixLift 368522
  have htrace : WordTrace (prefixWord ++ tailWord_368522) baseStart_368522 baseEnd_368522 := by
    simpa [prefixWord, tailWord_368522, baseEnd_368522] using wordTrace_append hprefix tailTrace_368522
  have hstable : (prefixWord ++ tailWord_368522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368522).length < 2 ^ (prefixWord ++ tailWord_368522).sum := by decide
  have hdescent : baseEnd_368522 < baseStart_368522 := by decide
  rcases family_descends (prefixWord ++ tailWord_368522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368533 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_368533 : Nat := 118140960795 + 368533 * 2 ^ 59
def prefixEnd_368533 : Nat := 4983230072969 + 3 ^ 40 * 368533 * 2
def baseEnd_368533 : Nat := 168208503149788308126803

theorem tailTrace_368533 : CollatzResearch.WordTrace tailWord_368533 prefixEnd_368533 168208503149788308126803 := by
  unfold tailWord_368533
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441502773875356270566253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8961001849250237513710835 13441502773875356270566253)
  ·
    refine ⟨5040563540203258601462345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13441502773875356270566253 5040563540203258601462345)
    ·
      refine ⟨3780422655152443951096759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5040563540203258601462345 3780422655152443951096759)
      ·
        refine ⟨5670633982728665926645139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780422655152443951096759 5670633982728665926645139)
        ·
          refine ⟨8505950974092998889967709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670633982728665926645139 8505950974092998889967709)
          ·
            refine ⟨3189731615284874583737891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8505950974092998889967709 3189731615284874583737891)
            ·
              refine ⟨4784597422927311875606837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189731615284874583737891 4784597422927311875606837)
              ·
                refine ⟨448556008399435488338141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4784597422927311875606837 448556008399435488338141)
                ·
                  refine ⟨168208503149788308126803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448556008399435488338141 168208503149788308126803)
                  ·
                    rfl

theorem cell20_368533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_368533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368533 prefixEnd_368533 := by exact prefixLift 368533
  have htrace : WordTrace (prefixWord ++ tailWord_368533) baseStart_368533 baseEnd_368533 := by
    simpa [prefixWord, tailWord_368533, baseEnd_368533] using wordTrace_append hprefix tailTrace_368533
  have hstable : (prefixWord ++ tailWord_368533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368533).length < 2 ^ (prefixWord ++ tailWord_368533).sum := by decide
  have hdescent : baseEnd_368533 < baseStart_368533 := by decide
  rcases family_descends (prefixWord ++ tailWord_368533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368536 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_368536 : Nat := 118140960795 + 368536 * 2 ^ 59
def prefixEnd_368536 : Nat := 4983230072969 + 3 ^ 40 * 368536 * 2
def baseEnd_368536 : Nat := 168209872431533631026791

theorem tailTrace_368536 : CollatzResearch.WordTrace tailWord_368536 prefixEnd_368536 168209872431533631026791 := by
  unfold tailWord_368536
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720806096432243891462731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8961074795242991855283641 6720806096432243891462731)
  ·
    refine ⟨10081209144648365837194097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6720806096432243891462731 10081209144648365837194097)
    ·
      refine ⟨7560906858486274377895573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10081209144648365837194097 7560906858486274377895573)
      ·
        refine ⟨354417508991544111463855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7560906858486274377895573 354417508991544111463855)
        ·
          refine ⟨531626263487316167195783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354417508991544111463855 531626263487316167195783)
          ·
            refine ⟨797439395230974250793675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531626263487316167195783 797439395230974250793675)
            ·
              refine ⟨1196159092846461376190513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797439395230974250793675 1196159092846461376190513)
              ·
                refine ⟨897119319634846032142885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196159092846461376190513 897119319634846032142885)
                ·
                  refine ⟨168209872431533631026791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897119319634846032142885 168209872431533631026791)
                  ·
                    rfl

theorem cell20_368536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_368536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368536 prefixEnd_368536 := by exact prefixLift 368536
  have htrace : WordTrace (prefixWord ++ tailWord_368536) baseStart_368536 baseEnd_368536 := by
    simpa [prefixWord, tailWord_368536, baseEnd_368536] using wordTrace_append hprefix tailTrace_368536
  have hstable : (prefixWord ++ tailWord_368536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368536).length < 2 ^ (prefixWord ++ tailWord_368536).sum := by decide
  have hdescent : baseEnd_368536 < baseStart_368536 := by decide
  rcases family_descends (prefixWord ++ tailWord_368536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368543 : List Nat := [1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_368543 : Nat := 118140960795 + 368543 * 2 ^ 59
def prefixEnd_368543 : Nat := 4983230072969 + 3 ^ 40 * 368543 * 2
def baseEnd_368543 : Nat := 56071022474090905931143

theorem tailTrace_368543 : CollatzResearch.WordTrace tailWord_368543 prefixEnd_368543 56071022474090905931143 := by
  unfold tailWord_368543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441867503839127978430283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8961245002559418652286855 13441867503839127978430283)
  ·
    refine ⟨20162801255758691967645425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13441867503839127978430283 20162801255758691967645425)
    ·
      refine ⟨15122100941819018975734069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20162801255758691967645425 15122100941819018975734069)
      ·
        refine ⟨1417696963295533028975069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15122100941819018975734069 1417696963295533028975069)
        ·
          refine ⟨531636361235824885865651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1417696963295533028975069 531636361235824885865651)
          ·
            refine ⟨797454541853737328798477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531636361235824885865651 797454541853737328798477)
            ·
              refine ⟨299045453195151498299429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 797454541853737328798477 299045453195151498299429)
              ·
                refine ⟨56071022474090905931143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299045453195151498299429 56071022474090905931143)
                ·
                  rfl

theorem cell20_368543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_368543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368543 prefixEnd_368543 := by exact prefixLift 368543
  have htrace : WordTrace (prefixWord ++ tailWord_368543) baseStart_368543 baseEnd_368543 := by
    simpa [prefixWord, tailWord_368543, baseEnd_368543] using wordTrace_append hprefix tailTrace_368543
  have hstable : (prefixWord ++ tailWord_368543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368543).length < 2 ^ (prefixWord ++ tailWord_368543).sum := by decide
  have hdescent : baseEnd_368543 < baseStart_368543 := by decide
  rcases family_descends (prefixWord ++ tailWord_368543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368574 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_368574 : Nat := 118140960795 + 368574 * 2 ^ 59
def prefixEnd_368574 : Nat := 4983230072969 + 3 ^ 40 * 368574 * 2
def baseEnd_368574 : Nat := 168227216666974387759969

theorem tailTrace_368574 : CollatzResearch.WordTrace tailWord_368574 prefixEnd_368574 168227216666974387759969 := by
  unfold tailWord_368574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680374770840852534101097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8961998777817880181872517 1680374770840852534101097)
  ·
    refine ⟨1260281078130639400575823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1680374770840852534101097 1260281078130639400575823)
    ·
      refine ⟨1890421617195959100863735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260281078130639400575823 1890421617195959100863735)
      ·
        refine ⟨2835632425793938651295603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890421617195959100863735 2835632425793938651295603)
        ·
          refine ⟨4253448638690907976943405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835632425793938651295603 4253448638690907976943405)
          ·
            refine ⟨1595043239509090491353777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4253448638690907976943405 1595043239509090491353777)
            ·
              refine ⟨1196282429631817868515333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595043239509090491353777 1196282429631817868515333)
              ·
                refine ⟨224302955555965850346625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1196282429631817868515333 224302955555965850346625)
                ·
                  refine ⟨168227216666974387759969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224302955555965850346625 168227216666974387759969)
                  ·
                    rfl

theorem cell20_368574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_368574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368574 prefixEnd_368574 := by exact prefixLift 368574
  have htrace : WordTrace (prefixWord ++ tailWord_368574) baseStart_368574 baseEnd_368574 := by
    simpa [prefixWord, tailWord_368574, baseEnd_368574] using wordTrace_append hprefix tailTrace_368574
  have hstable : (prefixWord ++ tailWord_368574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368574).length < 2 ^ (prefixWord ++ tailWord_368574).sum := by decide
  have hdescent : baseEnd_368574 < baseStart_368574 := by decide
  rcases family_descends (prefixWord ++ tailWord_368574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368602 : List Nat := [3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_368602 : Nat := 118140960795 + 368602 * 2 ^ 59
def prefixEnd_368602 : Nat := 4983230072969 + 3 ^ 40 * 368602 * 2
def baseEnd_368602 : Nat := 56079998876643578275507

theorem tailTrace_368602 : CollatzResearch.WordTrace tailWord_368602 prefixEnd_368602 56079998876643578275507 := by
  unfold tailWord_368602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361004852656345263707015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8962679607083587369885373 3361004852656345263707015)
  ·
    refine ⟨5041507278984517895560523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3361004852656345263707015 5041507278984517895560523)
    ·
      refine ⟨7562260918476776843340785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041507278984517895560523 7562260918476776843340785)
      ·
        refine ⟨5671695688857582632505589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7562260918476776843340785 5671695688857582632505589)
        ·
          refine ⟨531721470830398371797399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5671695688857582632505589 531721470830398371797399)
          ·
            refine ⟨797582206245597557696099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531721470830398371797399 797582206245597557696099)
            ·
              refine ⟨1196373309368396336544149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797582206245597557696099 1196373309368396336544149)
              ·
                refine ⟨56079998876643578275507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1196373309368396336544149 56079998876643578275507)
                ·
                  rfl

theorem cell20_368602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_368602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368602 prefixEnd_368602 := by exact prefixLift 368602
  have htrace : WordTrace (prefixWord ++ tailWord_368602) baseStart_368602 baseEnd_368602 := by
    simpa [prefixWord, tailWord_368602, baseEnd_368602] using wordTrace_append hprefix tailTrace_368602
  have hstable : (prefixWord ++ tailWord_368602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368602).length < 2 ^ (prefixWord ++ tailWord_368602).sum := by decide
  have hdescent : baseEnd_368602 < baseStart_368602 := by decide
  rcases family_descends (prefixWord ++ tailWord_368602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368604 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_368604 : Nat := 118140960795 + 368604 * 2 ^ 59
def prefixEnd_368604 : Nat := 4983230072969 + 3 ^ 40 * 368604 * 2
def baseEnd_368604 : Nat := 168240909484427616759847

theorem tailTrace_368604 : CollatzResearch.WordTrace tailWord_368604 prefixEnd_368604 168240909484427616759847 := by
  unfold tailWord_368604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722046178309067698200433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8962728237745423597600577 6722046178309067698200433)
  ·
    refine ⟨5041534633731800773650325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6722046178309067698200433 5041534633731800773650325)
    ·
      refine ⟨236321935956178161264859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5041534633731800773650325 236321935956178161264859)
      ·
        refine ⟨354482903934267241897289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236321935956178161264859 354482903934267241897289)
        ·
          refine ⟨265862177950700431422967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354482903934267241897289 265862177950700431422967)
          ·
            refine ⟨398793266926050647134451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265862177950700431422967 398793266926050647134451)
            ·
              refine ⟨598189900389075970701677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398793266926050647134451 598189900389075970701677)
              ·
                refine ⟨224321212645903489013129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598189900389075970701677 224321212645903489013129)
                ·
                  refine ⟨168240909484427616759847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224321212645903489013129 168240909484427616759847)
                  ·
                    rfl

theorem cell20_368604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_368604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368604 prefixEnd_368604 := by exact prefixLift 368604
  have htrace : WordTrace (prefixWord ++ tailWord_368604) baseStart_368604 baseEnd_368604 := by
    simpa [prefixWord, tailWord_368604, baseEnd_368604] using wordTrace_append hprefix tailTrace_368604
  have hstable : (prefixWord ++ tailWord_368604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368604).length < 2 ^ (prefixWord ++ tailWord_368604).sum := by decide
  have hdescent : baseEnd_368604 < baseStart_368604 := by decide
  rcases family_descends (prefixWord ++ tailWord_368604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368633 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_368633 : Nat := 118140960795 + 368633 * 2 ^ 59
def prefixEnd_368633 : Nat := 4983230072969 + 3 ^ 40 * 368633 * 2
def baseEnd_368633 : Nat := 168254145874632404793061

theorem tailTrace_368633 : CollatzResearch.WordTrace tailWord_368633 prefixEnd_368633 168254145874632404793061 := by
  unfold tailWord_368633
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445150073513073349206553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8963433382342048899471035 13445150073513073349206553)
  ·
    refine ⟨10083862555134805011904915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13445150073513073349206553 10083862555134805011904915)
    ·
      refine ⟨15125793832702207517857373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083862555134805011904915 15125793832702207517857373)
      ·
        refine ⟨5672172687263327819196515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15125793832702207517857373 5672172687263327819196515)
        ·
          refine ⟨8508259030894991728794773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5672172687263327819196515 8508259030894991728794773)
          ·
            refine ⟨398824642073202737287255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8508259030894991728794773 398824642073202737287255)
            ·
              refine ⟨598236963109804105930883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398824642073202737287255 598236963109804105930883)
              ·
                refine ⟨897355444664706158896325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598236963109804105930883 897355444664706158896325)
                ·
                  refine ⟨168254145874632404793061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897355444664706158896325 168254145874632404793061)
                  ·
                    rfl

theorem cell20_368633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_368633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368633 prefixEnd_368633 := by exact prefixLift 368633
  have htrace : WordTrace (prefixWord ++ tailWord_368633) baseStart_368633 baseEnd_368633 := by
    simpa [prefixWord, tailWord_368633, baseEnd_368633] using wordTrace_append hprefix tailTrace_368633
  have hstable : (prefixWord ++ tailWord_368633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368633).length < 2 ^ (prefixWord ++ tailWord_368633).sum := by decide
  have hdescent : baseEnd_368633 < baseStart_368633 := by decide
  rcases family_descends (prefixWord ++ tailWord_368633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368654 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_368654 : Nat := 118140960795 + 368654 * 2 ^ 59
def prefixEnd_368654 : Nat := 4983230072969 + 3 ^ 40 * 368654 * 2
def baseEnd_368654 : Nat := 168263730846849665092975

theorem tailTrace_368654 : CollatzResearch.WordTrace tailWord_368654 prefixEnd_368654 168263730846849665092975 := by
  unfold tailWord_368654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680739500804624241965127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8963944004291329290480677 1680739500804624241965127)
  ·
    refine ⟨2521109251206936362947691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1680739500804624241965127 2521109251206936362947691)
    ·
      refine ⟨3781663876810404544421537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2521109251206936362947691 3781663876810404544421537)
      ·
        refine ⟨2836247907607803408316153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3781663876810404544421537 2836247907607803408316153)
        ·
          refine ⟨2127185930705852556237115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836247907607803408316153 2127185930705852556237115)
          ·
            refine ⟨3190778896058778834355673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127185930705852556237115 3190778896058778834355673)
            ·
              refine ⟨2393084172044084125766755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190778896058778834355673 2393084172044084125766755)
              ·
                refine ⟨3589626258066126188650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393084172044084125766755 3589626258066126188650133)
                ·
                  refine ⟨168263730846849665092975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3589626258066126188650133 168263730846849665092975)
                  ·
                    rfl

theorem cell20_368654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_368654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368654 prefixEnd_368654 := by exact prefixLift 368654
  have htrace : WordTrace (prefixWord ++ tailWord_368654) baseStart_368654 baseEnd_368654 := by
    simpa [prefixWord, tailWord_368654, baseEnd_368654] using wordTrace_append hprefix tailTrace_368654
  have hstable : (prefixWord ++ tailWord_368654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368654).length < 2 ^ (prefixWord ++ tailWord_368654).sum := by decide
  have hdescent : baseEnd_368654 < baseStart_368654 := by decide
  rcases family_descends (prefixWord ++ tailWord_368654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368671 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 2]
def baseStart_368671 : Nat := 118140960795 + 368671 * 2 ^ 59
def prefixEnd_368671 : Nat := 4983230072969 + 3 ^ 40 * 368671 * 2
def baseEnd_368671 : Nat := 168271490110073161526239

theorem tailTrace_368671 : CollatzResearch.WordTrace tailWord_368671 prefixEnd_368671 168271490110073161526239 := by
  unfold tailWord_368671
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446536047375405839089867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8964357364916937226059911 13446536047375405839089867)
  ·
    refine ⟨20169804071063108758634801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13446536047375405839089867 20169804071063108758634801)
    ·
      refine ⟨15127353053297331568976101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20169804071063108758634801 15127353053297331568976101)
      ·
        refine ⟨2836378697493249669183019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15127353053297331568976101 2836378697493249669183019)
        ·
          refine ⟨4254568046239874503774529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836378697493249669183019 4254568046239874503774529)
          ·
            refine ⟨3190926034679905877830897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4254568046239874503774529 3190926034679905877830897)
            ·
              refine ⟨2393194526009929408373173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190926034679905877830897 2393194526009929408373173)
              ·
                refine ⟨224361986813430882034985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2393194526009929408373173 224361986813430882034985)
                ·
                  refine ⟨168271490110073161526239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224361986813430882034985 168271490110073161526239)
                  ·
                    rfl

theorem cell20_368671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2].length) (baseStart_368671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368671 prefixEnd_368671 := by exact prefixLift 368671
  have htrace : WordTrace (prefixWord ++ tailWord_368671) baseStart_368671 baseEnd_368671 := by
    simpa [prefixWord, tailWord_368671, baseEnd_368671] using wordTrace_append hprefix tailTrace_368671
  have hstable : (prefixWord ++ tailWord_368671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368671).length < 2 ^ (prefixWord ++ tailWord_368671).sum := by decide
  have hdescent : baseEnd_368671 < baseStart_368671 := by decide
  rcases family_descends (prefixWord ++ tailWord_368671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368688 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_368688 : Nat := 118140960795 + 368688 * 2 ^ 59
def prefixEnd_368688 : Nat := 4983230072969 + 3 ^ 40 * 368688 * 2
def baseEnd_368688 : Nat := 168279249373296657959503

theorem tailTrace_368688 : CollatzResearch.WordTrace tailWord_368688 prefixEnd_368688 168279249373296657959503 := by
  unfold tailWord_368688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723578044156908871229359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8964770725542545161639145 6723578044156908871229359)
  ·
    refine ⟨10085367066235363306844039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723578044156908871229359 10085367066235363306844039)
    ·
      refine ⟨15128050599353044960266059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085367066235363306844039 15128050599353044960266059)
      ·
        refine ⟨22692075899029567440399089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128050599353044960266059 22692075899029567440399089)
        ·
          refine ⟨17019056924272175580299317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22692075899029567440399089 17019056924272175580299317)
          ·
            refine ⟨1595536586650516460653061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17019056924272175580299317 1595536586650516460653061)
            ·
              refine ⟨299163109996971836372449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1595536586650516460653061 299163109996971836372449)
              ·
                refine ⟨224372332497728877279337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299163109996971836372449 224372332497728877279337)
                ·
                  refine ⟨168279249373296657959503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224372332497728877279337 168279249373296657959503)
                  ·
                    rfl

theorem cell20_368688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_368688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368688 prefixEnd_368688 := by exact prefixLift 368688
  have htrace : WordTrace (prefixWord ++ tailWord_368688) baseStart_368688 baseEnd_368688 := by
    simpa [prefixWord, tailWord_368688, baseEnd_368688] using wordTrace_append hprefix tailTrace_368688
  have hstable : (prefixWord ++ tailWord_368688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368688).length < 2 ^ (prefixWord ++ tailWord_368688).sum := by decide
  have hdescent : baseEnd_368688 < baseStart_368688 := by decide
  rcases family_descends (prefixWord ++ tailWord_368688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368788 : List Nat := [2, 4, 2, 3, 2, 1, 6]
def baseStart_368788 : Nat := 118140960795 + 368788 * 2 ^ 59
def prefixEnd_368788 : Nat := 4983230072969 + 3 ^ 40 * 368788 * 2
def baseEnd_368788 : Nat := 18702765788682306069529

theorem tailTrace_368788 : CollatzResearch.WordTrace tailWord_368788 prefixEnd_368788 18702765788682306069529 := by
  unfold tailWord_368788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725401693975767410549509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8967202258634356547399345 6725401693975767410549509)
  ·
    refine ⟨1261012817620456389478033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6725401693975767410549509 1261012817620456389478033)
    ·
      refine ⟨945759613215342292108525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1261012817620456389478033 945759613215342292108525)
      ·
        refine ⟨354659854955753359540697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 945759613215342292108525 354659854955753359540697)
        ·
          refine ⟨265994891216815019655523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354659854955753359540697 265994891216815019655523)
          ·
            refine ⟨398992336825222529483285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265994891216815019655523 398992336825222529483285)
            ·
              refine ⟨18702765788682306069529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 398992336825222529483285 18702765788682306069529)
              ·
                rfl

theorem cell20_368788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 6].length) (baseStart_368788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368788 prefixEnd_368788 := by exact prefixLift 368788
  have htrace : WordTrace (prefixWord ++ tailWord_368788) baseStart_368788 baseEnd_368788 := by
    simpa [prefixWord, tailWord_368788, baseEnd_368788] using wordTrace_append hprefix tailTrace_368788
  have hstable : (prefixWord ++ tailWord_368788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368788).length < 2 ^ (prefixWord ++ tailWord_368788).sum := by decide
  have hdescent : baseEnd_368788 < baseStart_368788 := by decide
  rcases family_descends (prefixWord ++ tailWord_368788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368792 : List Nat := [2, 1, 2, 4, 3, 2, 6]
def baseStart_368792 : Nat := 118140960795 + 368792 * 2 ^ 59
def prefixEnd_368792 : Nat := 4983230072969 + 3 ^ 40 * 368792 * 2
def baseEnd_368792 : Nat := 18702968645237168721379

theorem tailTrace_368792 : CollatzResearch.WordTrace tailWord_368792 prefixEnd_368792 18702968645237168721379 := by
  unfold tailWord_368792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725474639968521752122315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8967299519958029002829753 6725474639968521752122315)
  ·
    refine ⟨10088211959952782628183473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725474639968521752122315 10088211959952782628183473)
    ·
      refine ⟨7566158969964586971137605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10088211959952782628183473 7566158969964586971137605)
      ·
        refine ⟨1418654806868360057088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7566158969964586971137605 1418654806868360057088301)
        ·
          refine ⟨531995552575635021408113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1418654806868360057088301 531995552575635021408113)
          ·
            refine ⟨398996664431726266056085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531995552575635021408113 398996664431726266056085)
            ·
              refine ⟨18702968645237168721379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 398996664431726266056085 18702968645237168721379)
              ·
                rfl

theorem cell20_368792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_368792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368792 prefixEnd_368792 := by exact prefixLift 368792
  have htrace : WordTrace (prefixWord ++ tailWord_368792) baseStart_368792 baseEnd_368792 := by
    simpa [prefixWord, tailWord_368792, baseEnd_368792] using wordTrace_append hprefix tailTrace_368792
  have hstable : (prefixWord ++ tailWord_368792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368792).length < 2 ^ (prefixWord ++ tailWord_368792).sum := by decide
  have hdescent : baseEnd_368792 < baseStart_368792 := by decide
  rcases family_descends (prefixWord ++ tailWord_368792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368798 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_368798 : Nat := 118140960795 + 368798 * 2 ^ 59
def prefixEnd_368798 : Nat := 4983230072969 + 3 ^ 40 * 368798 * 2
def baseEnd_368798 : Nat := 168329456370625164292387

theorem tailTrace_368798 : CollatzResearch.WordTrace tailWord_368798 prefixEnd_368798 168329456370625164292387 := by
  unfold tailWord_368798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681396014739413316120381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8967445411943537685975365 1681396014739413316120381)
  ·
    refine ⟨630523505527279993545143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1681396014739413316120381 630523505527279993545143)
    ·
      refine ⟨945785258290919990317715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630523505527279993545143 945785258290919990317715)
      ·
        refine ⟨1418677887436379985476573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945785258290919990317715 1418677887436379985476573)
        ·
          refine ⟨532004207788642494553715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1418677887436379985476573 532004207788642494553715)
          ·
            refine ⟨798006311682963741830573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532004207788642494553715 798006311682963741830573)
            ·
              refine ⟨299252366881111403186465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798006311682963741830573 299252366881111403186465)
              ·
                refine ⟨224439275160833552389849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299252366881111403186465 224439275160833552389849)
                ·
                  refine ⟨168329456370625164292387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224439275160833552389849 168329456370625164292387)
                  ·
                    rfl

theorem cell20_368798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_368798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368798 prefixEnd_368798 := by exact prefixLift 368798
  have htrace : WordTrace (prefixWord ++ tailWord_368798) baseStart_368798 baseEnd_368798 := by
    simpa [prefixWord, tailWord_368798, baseEnd_368798] using wordTrace_append hprefix tailTrace_368798
  have hstable : (prefixWord ++ tailWord_368798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368798).length < 2 ^ (prefixWord ++ tailWord_368798).sum := by decide
  have hdescent : baseEnd_368798 < baseStart_368798 := by decide
  rcases family_descends (prefixWord ++ tailWord_368798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368799 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_368799 : Nat := 118140960795 + 368799 * 2 ^ 59
def prefixEnd_368799 : Nat := 4983230072969 + 3 ^ 40 * 368799 * 2
def baseEnd_368799 : Nat := 168329912797873605259049

theorem tailTrace_368799 : CollatzResearch.WordTrace tailWord_368799 prefixEnd_368799 168329912797873605259049 := by
  unfold tailWord_368799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13451204590911683699749451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8967469727274455799832967 13451204590911683699749451)
  ·
    refine ⟨20176806886367525549624177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13451204590911683699749451 20176806886367525549624177)
    ·
      refine ⟨15132605164775644162218133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20176806886367525549624177 15132605164775644162218133)
      ·
        refine ⟨709340867098858320103975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15132605164775644162218133 709340867098858320103975)
        ·
          refine ⟨1064011300648287480155963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709340867098858320103975 1064011300648287480155963)
          ·
            refine ⟨1596016950972431220233945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064011300648287480155963 1596016950972431220233945)
            ·
              refine ⟨1197012713229323415175459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596016950972431220233945 1197012713229323415175459)
              ·
                refine ⟨1795519069843985122763189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197012713229323415175459 1795519069843985122763189)
                ·
                  refine ⟨168329912797873605259049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795519069843985122763189 168329912797873605259049)
                  ·
                    rfl

theorem cell20_368799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_368799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368799 prefixEnd_368799 := by exact prefixLift 368799
  have htrace : WordTrace (prefixWord ++ tailWord_368799) baseStart_368799 baseEnd_368799 := by
    simpa [prefixWord, tailWord_368799, baseEnd_368799] using wordTrace_append hprefix tailTrace_368799
  have hstable : (prefixWord ++ tailWord_368799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368799).length < 2 ^ (prefixWord ++ tailWord_368799).sum := by decide
  have hdescent : baseEnd_368799 < baseStart_368799 := by decide
  rcases family_descends (prefixWord ++ tailWord_368799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368802 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_368802 : Nat := 118140960795 + 368802 * 2 ^ 59
def prefixEnd_368802 : Nat := 4983230072969 + 3 ^ 40 * 368802 * 2
def baseEnd_368802 : Nat := 168331282079618928159037

theorem tailTrace_368802 : CollatzResearch.WordTrace tailWord_368802 prefixEnd_368802 168331282079618928159037 := by
  unfold tailWord_368802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362828502475203803027165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8967542673267210141405773 3362828502475203803027165)
  ·
    refine ⟨1261060688428201426135187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3362828502475203803027165 1261060688428201426135187)
    ·
      refine ⟨1891591032642302139202781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261060688428201426135187 1891591032642302139202781)
      ·
        refine ⟨709346637240863302201043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1891591032642302139202781 709346637240863302201043)
        ·
          refine ⟨1064019955861294953301565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709346637240863302201043 1064019955861294953301565)
          ·
            refine ⟨399007483447985607488087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1064019955861294953301565 399007483447985607488087)
            ·
              refine ⟨598511225171978411232131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399007483447985607488087 598511225171978411232131)
              ·
                refine ⟨897766837757967616848197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598511225171978411232131 897766837757967616848197)
                ·
                  refine ⟨168331282079618928159037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897766837757967616848197 168331282079618928159037)
                  ·
                    rfl

theorem cell20_368802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_368802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368802 prefixEnd_368802 := by exact prefixLift 368802
  have htrace : WordTrace (prefixWord ++ tailWord_368802) baseStart_368802 baseEnd_368802 := by
    simpa [prefixWord, tailWord_368802, baseEnd_368802] using wordTrace_append hprefix tailTrace_368802
  have hstable : (prefixWord ++ tailWord_368802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368802).length < 2 ^ (prefixWord ++ tailWord_368802).sum := by decide
  have hdescent : baseEnd_368802 < baseStart_368802 := by decide
  rcases family_descends (prefixWord ++ tailWord_368802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368827 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_368827 : Nat := 118140960795 + 368827 * 2 ^ 59
def prefixEnd_368827 : Nat := 4983230072969 + 3 ^ 40 * 368827 * 2
def baseEnd_368827 : Nat := 168342692760829952325601

theorem tailTrace_368827 : CollatzResearch.WordTrace tailWord_368827 prefixEnd_368827 168342692760829952325601 := by
  unfold tailWord_368827
  simp only [CollatzResearch.WordTrace]
  refine ⟨13452225834810244481768735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8968150556540162987845823 13452225834810244481768735)
  ·
    refine ⟨20178338752215366722653103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13452225834810244481768735 20178338752215366722653103)
    ·
      refine ⟨30267508128323050083979655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20178338752215366722653103 30267508128323050083979655)
      ·
        refine ⟨45401262192484575125969483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30267508128323050083979655 45401262192484575125969483)
        ·
          refine ⟨68101893288726862688954225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45401262192484575125969483 68101893288726862688954225)
          ·
            refine ⟨51076419966545147016715669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68101893288726862688954225 51076419966545147016715669)
            ·
              refine ⟨2394207185931803766408547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51076419966545147016715669 2394207185931803766408547)
              ·
                refine ⟨3591310778897705649612821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394207185931803766408547 3591310778897705649612821)
                ·
                  refine ⟨168342692760829952325601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3591310778897705649612821 168342692760829952325601)
                  ·
                    rfl

theorem cell20_368827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_368827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368827 prefixEnd_368827 := by exact prefixLift 368827
  have htrace : WordTrace (prefixWord ++ tailWord_368827) baseStart_368827 baseEnd_368827 := by
    simpa [prefixWord, tailWord_368827, baseEnd_368827] using wordTrace_append hprefix tailTrace_368827
  have hstable : (prefixWord ++ tailWord_368827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368827).length < 2 ^ (prefixWord ++ tailWord_368827).sum := by decide
  have hdescent : baseEnd_368827 < baseStart_368827 := by decide
  rcases family_descends (prefixWord ++ tailWord_368827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368858 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_368858 : Nat := 118140960795 + 368858 * 2 ^ 59
def prefixEnd_368858 : Nat := 4983230072969 + 3 ^ 40 * 368858 * 2
def baseEnd_368858 : Nat := 168356842005531622292141

theorem tailTrace_368858 : CollatzResearch.WordTrace tailWord_368858 prefixEnd_368858 168356842005531622292141 := by
  unfold tailWord_368858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363339124424484194036807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8968904331798624517431485 3363339124424484194036807)
  ·
    refine ⟨5045008686636726291055211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3363339124424484194036807 5045008686636726291055211)
    ·
      refine ⟨7567513029955089436582817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5045008686636726291055211 7567513029955089436582817)
      ·
        refine ⟨5675634772466317077437113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7567513029955089436582817 5675634772466317077437113)
        ·
          refine ⟨4256726079349737808077835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5675634772466317077437113 4256726079349737808077835)
          ·
            refine ⟨6385089119024606712116753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256726079349737808077835 6385089119024606712116753)
            ·
              refine ⟨4788816839268455034087565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385089119024606712116753 4788816839268455034087565)
              ·
                refine ⟨1795806314725670637782837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4788816839268455034087565 1795806314725670637782837)
                ·
                  refine ⟨168356842005531622292141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795806314725670637782837 168356842005531622292141)
                  ·
                    rfl

theorem cell20_368858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_368858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368858 prefixEnd_368858 := by exact prefixLift 368858
  have htrace : WordTrace (prefixWord ++ tailWord_368858) baseStart_368858 baseEnd_368858 := by
    simpa [prefixWord, tailWord_368858, baseEnd_368858] using wordTrace_append hprefix tailTrace_368858
  have hstable : (prefixWord ++ tailWord_368858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368858).length < 2 ^ (prefixWord ++ tailWord_368858).sum := by decide
  have hdescent : baseEnd_368858 < baseStart_368858 := by decide
  rcases family_descends (prefixWord ++ tailWord_368858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368882 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_368882 : Nat := 118140960795 + 368882 * 2 ^ 59
def prefixEnd_368882 : Nat := 4983230072969 + 3 ^ 40 * 368882 * 2
def baseEnd_368882 : Nat := 168367796259494205492043

theorem tailTrace_368882 : CollatzResearch.WordTrace tailWord_368882 prefixEnd_368882 168367796259494205492043 := by
  unfold tailWord_368882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363557962402747218755225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8969487899740659250013933 3363557962402747218755225)
  ·
    refine ⟨2522668471802060414066419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3363557962402747218755225 2522668471802060414066419)
    ·
      refine ⟨3784002707703090621099629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522668471802060414066419 3784002707703090621099629)
      ·
        refine ⟨1419001015388658982912361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3784002707703090621099629 1419001015388658982912361)
        ·
          refine ⟨1064250761541494237184271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419001015388658982912361 1064250761541494237184271)
          ·
            refine ⟨1596376142312241355776407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064250761541494237184271 1596376142312241355776407)
            ·
              refine ⟨2394564213468362033664611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596376142312241355776407 2394564213468362033664611)
              ·
                refine ⟨3591846320202543050496917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394564213468362033664611 3591846320202543050496917)
                ·
                  refine ⟨168367796259494205492043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3591846320202543050496917 168367796259494205492043)
                  ·
                    rfl

theorem cell20_368882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_368882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368882 prefixEnd_368882 := by exact prefixLift 368882
  have htrace : WordTrace (prefixWord ++ tailWord_368882) baseStart_368882 baseEnd_368882 := by
    simpa [prefixWord, tailWord_368882, baseEnd_368882] using wordTrace_append hprefix tailTrace_368882
  have hstable : (prefixWord ++ tailWord_368882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368882).length < 2 ^ (prefixWord ++ tailWord_368882).sum := by decide
  have hdescent : baseEnd_368882 < baseStart_368882 := by decide
  rcases family_descends (prefixWord ++ tailWord_368882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368899 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 2]
def baseStart_368899 : Nat := 118140960795 + 368899 * 2 ^ 59
def prefixEnd_368899 : Nat := 4983230072969 + 3 ^ 40 * 368899 * 2
def baseEnd_368899 : Nat := 168375555522717701925307

theorem tailTrace_368899 : CollatzResearch.WordTrace tailWord_368899 prefixEnd_368899 168375555522717701925307 := by
  unfold tailWord_368899
  simp only [CollatzResearch.WordTrace]
  refine ⟨13454851890549400778389751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8969901260366267185593167 13454851890549400778389751)
  ·
    refine ⟨20182277835824101167584627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13454851890549400778389751 20182277835824101167584627)
    ·
      refine ⟨30273416753736151751376941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20182277835824101167584627 30273416753736151751376941)
      ·
        refine ⟨11352531282651056906766353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30273416753736151751376941 11352531282651056906766353)
        ·
          refine ⟨8514398461988292680074765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11352531282651056906766353 8514398461988292680074765)
          ·
            refine ⟨3192899423245609755028037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8514398461988292680074765 3192899423245609755028037)
            ·
              refine ⟨598668641858551829067757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3192899423245609755028037 598668641858551829067757)
              ·
                refine ⟨224500740696956935900409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598668641858551829067757 224500740696956935900409)
                ·
                  refine ⟨168375555522717701925307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224500740696956935900409 168375555522717701925307)
                  ·
                    rfl

theorem cell20_368899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2].length) (baseStart_368899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368899 prefixEnd_368899 := by exact prefixLift 368899
  have htrace : WordTrace (prefixWord ++ tailWord_368899) baseStart_368899 baseEnd_368899 := by
    simpa [prefixWord, tailWord_368899, baseEnd_368899] using wordTrace_append hprefix tailTrace_368899
  have hstable : (prefixWord ++ tailWord_368899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368899).length < 2 ^ (prefixWord ++ tailWord_368899).sum := by decide
  have hdescent : baseEnd_368899 < baseStart_368899 := by decide
  rcases family_descends (prefixWord ++ tailWord_368899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368913 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_368913 : Nat := 118140960795 + 368913 * 2 ^ 59
def prefixEnd_368913 : Nat := 4983230072969 + 3 ^ 40 * 368913 * 2
def baseEnd_368913 : Nat := 168381945504195875458583

theorem tailTrace_368913 : CollatzResearch.WordTrace tailWord_368913 prefixEnd_368913 168381945504195875458583 := by
  unfold tailWord_368913
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455362512498681169399393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8970241674999120779599595 13455362512498681169399393)
  ·
    refine ⟨10091521884374010877049545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13455362512498681169399393 10091521884374010877049545)
    ·
      refine ⟨7568641413280508157787159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10091521884374010877049545 7568641413280508157787159)
      ·
        refine ⟨11352962119920762236680739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7568641413280508157787159 11352962119920762236680739)
        ·
          refine ⟨17029443179881143355021109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11352962119920762236680739 17029443179881143355021109)
          ·
            refine ⟨1596510298113857189533229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17029443179881143355021109 1596510298113857189533229)
            ·
              refine ⟨598691361792696446074961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596510298113857189533229 598691361792696446074961)
              ·
                refine ⟨449018521344522334556221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598691361792696446074961 449018521344522334556221)
                ·
                  refine ⟨168381945504195875458583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449018521344522334556221 168381945504195875458583)
                  ·
                    rfl

theorem cell20_368913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_368913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368913 prefixEnd_368913 := by exact prefixLift 368913
  have htrace : WordTrace (prefixWord ++ tailWord_368913) baseStart_368913 baseEnd_368913 := by
    simpa [prefixWord, tailWord_368913, baseEnd_368913] using wordTrace_append hprefix tailTrace_368913
  have hstable : (prefixWord ++ tailWord_368913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368913).length < 2 ^ (prefixWord ++ tailWord_368913).sum := by decide
  have hdescent : baseEnd_368913 < baseStart_368913 := by decide
  rcases family_descends (prefixWord ++ tailWord_368913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368920 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_368920 : Nat := 118140960795 + 368920 * 2 ^ 59
def prefixEnd_368920 : Nat := 4983230072969 + 3 ^ 40 * 368920 * 2
def baseEnd_368920 : Nat := 168385140494934962225221

theorem tailTrace_368920 : CollatzResearch.WordTrace tailWord_368920 prefixEnd_368920 168385140494934962225221 := by
  unfold tailWord_368920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727808911736660682452107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8970411882315547576602809 6727808911736660682452107)
  ·
    refine ⟨10091713367604991023678161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727808911736660682452107 10091713367604991023678161)
    ·
      refine ⟨7568785025703743267758621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10091713367604991023678161 7568785025703743267758621)
      ·
        refine ⟨2838294384638903725409483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7568785025703743267758621 2838294384638903725409483)
        ·
          refine ⟨4257441576958355588114225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838294384638903725409483 4257441576958355588114225)
          ·
            refine ⟨3193081182718766691085669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4257441576958355588114225 3193081182718766691085669)
            ·
              refine ⟨598702721759768754578563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3193081182718766691085669 598702721759768754578563)
              ·
                refine ⟨898054082639653131867845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598702721759768754578563 898054082639653131867845)
                ·
                  refine ⟨168385140494934962225221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898054082639653131867845 168385140494934962225221)
                  ·
                    rfl

theorem cell20_368920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_368920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368920 prefixEnd_368920 := by exact prefixLift 368920
  have htrace : WordTrace (prefixWord ++ tailWord_368920) baseStart_368920 baseEnd_368920 := by
    simpa [prefixWord, tailWord_368920, baseEnd_368920] using wordTrace_append hprefix tailTrace_368920
  have hstable : (prefixWord ++ tailWord_368920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368920).length < 2 ^ (prefixWord ++ tailWord_368920).sum := by decide
  have hdescent : baseEnd_368920 < baseStart_368920 := by decide
  rcases family_descends (prefixWord ++ tailWord_368920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368926 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_368926 : Nat := 118140960795 + 368926 * 2 ^ 59
def prefixEnd_368926 : Nat := 4983230072969 + 3 ^ 40 * 368926 * 2
def baseEnd_368926 : Nat := 168387879058425608025197

theorem tailTrace_368926 : CollatzResearch.WordTrace tailWord_368926 prefixEnd_368926 168387879058425608025197 := by
  unfold tailWord_368926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681979582681448048702829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8970557774301056259748421 1681979582681448048702829)
  ·
    refine ⟨630742343505543018263561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1681979582681448048702829 630742343505543018263561)
    ·
      refine ⟨473056757629157263697671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630742343505543018263561 473056757629157263697671)
      ·
        refine ⟨709585136443735895546507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473056757629157263697671 709585136443735895546507)
        ·
          refine ⟨1064377704665603843319761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709585136443735895546507 1064377704665603843319761)
          ·
            refine ⟨798283278499202882489821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064377704665603843319761 798283278499202882489821)
            ·
              refine ⟨299356229437201080933683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798283278499202882489821 299356229437201080933683)
              ·
                refine ⟨449034344155801621400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299356229437201080933683 449034344155801621400525)
                ·
                  refine ⟨168387879058425608025197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449034344155801621400525 168387879058425608025197)
                  ·
                    rfl

theorem cell20_368926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_368926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368926 prefixEnd_368926 := by exact prefixLift 368926
  have htrace : WordTrace (prefixWord ++ tailWord_368926) baseStart_368926 baseEnd_368926 := by
    simpa [prefixWord, tailWord_368926, baseEnd_368926] using wordTrace_append hprefix tailTrace_368926
  have hstable : (prefixWord ++ tailWord_368926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368926).length < 2 ^ (prefixWord ++ tailWord_368926).sum := by decide
  have hdescent : baseEnd_368926 < baseStart_368926 := by decide
  rcases family_descends (prefixWord ++ tailWord_368926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368954 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_368954 : Nat := 118140960795 + 368954 * 2 ^ 59
def prefixEnd_368954 : Nat := 4983230072969 + 3 ^ 40 * 368954 * 2
def baseEnd_368954 : Nat := 168400659021381955091749

theorem tailTrace_368954 : CollatzResearch.WordTrace tailWord_368954 prefixEnd_368954 168400659021381955091749 := by
  unfold tailWord_368954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364214476337536292910479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8971238603566763447761277 3364214476337536292910479)
  ·
    refine ⟨5046321714506304439365719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3364214476337536292910479 5046321714506304439365719)
    ·
      refine ⟨7569482571759456659048579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5046321714506304439365719 7569482571759456659048579)
      ·
        refine ⟨11354223857639184988572869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569482571759456659048579 11354223857639184988572869)
        ·
          refine ⟨2128916973307347185357413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11354223857639184988572869 2128916973307347185357413)
          ·
            refine ⟨399171932495127597254515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2128916973307347185357413 399171932495127597254515)
            ·
              refine ⟨598757898742691395881773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399171932495127597254515 598757898742691395881773)
              ·
                refine ⟨224534212028509273455665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598757898742691395881773 224534212028509273455665)
                ·
                  refine ⟨168400659021381955091749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224534212028509273455665 168400659021381955091749)
                  ·
                    rfl

theorem cell20_368954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_368954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368954 prefixEnd_368954 := by exact prefixLift 368954
  have htrace : WordTrace (prefixWord ++ tailWord_368954) baseStart_368954 baseEnd_368954 := by
    simpa [prefixWord, tailWord_368954, baseEnd_368954] using wordTrace_append hprefix tailTrace_368954
  have hstable : (prefixWord ++ tailWord_368954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368954).length < 2 ^ (prefixWord ++ tailWord_368954).sum := by decide
  have hdescent : baseEnd_368954 < baseStart_368954 := by decide
  rcases family_descends (prefixWord ++ tailWord_368954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368961 : List Nat := [1, 2, 5, 2, 3, 1, 6]
def baseStart_368961 : Nat := 118140960795 + 368961 * 2 ^ 59
def prefixEnd_368961 : Nat := 4983230072969 + 3 ^ 40 * 368961 * 2
def baseEnd_368961 : Nat := 18711539334680115762043

theorem tailTrace_368961 : CollatzResearch.WordTrace tailWord_368961 prefixEnd_368961 18711539334680115762043 := by
  unfold tailWord_368961
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457113216324785367146737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971408810883190244764491 13457113216324785367146737)
  ·
    refine ⟨10092834912243589025360053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13457113216324785367146737 10092834912243589025360053)
    ·
      refine ⟨946203273022836471127505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10092834912243589025360053 946203273022836471127505)
      ·
        refine ⟨709652454767127353345629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 946203273022836471127505 709652454767127353345629)
        ·
          refine ⟨266119670537672757504611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709652454767127353345629 266119670537672757504611)
          ·
            refine ⟨399179505806509136256917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266119670537672757504611 399179505806509136256917)
            ·
              refine ⟨18711539334680115762043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 399179505806509136256917 18711539334680115762043)
              ·
                rfl

theorem cell20_368961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 6].length) (baseStart_368961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368961 prefixEnd_368961 := by exact prefixLift 368961
  have htrace : WordTrace (prefixWord ++ tailWord_368961) baseStart_368961 baseEnd_368961 := by
    simpa [prefixWord, tailWord_368961, baseEnd_368961] using wordTrace_append hprefix tailTrace_368961
  have hstable : (prefixWord ++ tailWord_368961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368961).length < 2 ^ (prefixWord ++ tailWord_368961).sum := by decide
  have hdescent : baseEnd_368961 < baseStart_368961 := by decide
  rcases family_descends (prefixWord ++ tailWord_368961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368972 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_368972 : Nat := 118140960795 + 368972 * 2 ^ 59
def prefixEnd_368972 : Nat := 4983230072969 + 3 ^ 40 * 368972 * 2
def baseEnd_368972 : Nat := 168408874711853892491675

theorem tailTrace_368972 : CollatzResearch.WordTrace tailWord_368972 prefixEnd_368972 168408874711853892491675 := by
  unfold tailWord_368972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728757209642467122898585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8971676279523289497198113 6728757209642467122898585)
  ·
    refine ⟨5046567907231850342173939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6728757209642467122898585 5046567907231850342173939)
    ·
      refine ⟨7569851860847775513260909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5046567907231850342173939 7569851860847775513260909)
      ·
        refine ⟨2838694447817915817472841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7569851860847775513260909 2838694447817915817472841)
        ·
          refine ⟨2129020835863436863104631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2838694447817915817472841 2129020835863436863104631)
          ·
            refine ⟨3193531253795155294656947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129020835863436863104631 3193531253795155294656947)
            ·
              refine ⟨4790296880692732941985421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193531253795155294656947 4790296880692732941985421)
              ·
                refine ⟨1796361330259774853244533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4790296880692732941985421 1796361330259774853244533)
                ·
                  refine ⟨168408874711853892491675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1796361330259774853244533 168408874711853892491675)
                  ·
                    rfl

theorem cell20_368972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_368972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368972 prefixEnd_368972 := by exact prefixLift 368972
  have htrace : WordTrace (prefixWord ++ tailWord_368972) baseStart_368972 baseEnd_368972 := by
    simpa [prefixWord, tailWord_368972, baseEnd_368972] using wordTrace_append hprefix tailTrace_368972
  have hstable : (prefixWord ++ tailWord_368972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368972).length < 2 ^ (prefixWord ++ tailWord_368972).sum := by decide
  have hdescent : baseEnd_368972 < baseStart_368972 := by decide
  rcases family_descends (prefixWord ++ tailWord_368972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368979 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_368979 : Nat := 118140960795 + 368979 * 2 ^ 59
def prefixEnd_368979 : Nat := 4983230072969 + 3 ^ 40 * 368979 * 2
def baseEnd_368979 : Nat := 168412069702592979258313

theorem tailTrace_368979 : CollatzResearch.WordTrace tailWord_368979 prefixEnd_368979 168412069702592979258313 := by
  unfold tailWord_368979
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457769730259574441301991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971846486839716294201327 13457769730259574441301991)
  ·
    refine ⟨20186654595389361661952987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13457769730259574441301991 20186654595389361661952987)
    ·
      refine ⟨30279981893084042492929481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20186654595389361661952987 30279981893084042492929481)
      ·
        refine ⟨22709986419813031869697111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30279981893084042492929481 22709986419813031869697111)
        ·
          refine ⟨34064979629719547804545667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22709986419813031869697111 34064979629719547804545667)
          ·
            refine ⟨51097469444579321706818501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34064979629719547804545667 51097469444579321706818501)
            ·
              refine ⟨9580775520858622820028469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51097469444579321706818501 9580775520858622820028469)
              ·
                refine ⟨898197705080495889377669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9580775520858622820028469 898197705080495889377669)
                ·
                  refine ⟨168412069702592979258313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898197705080495889377669 168412069702592979258313)
                  ·
                    rfl

theorem cell20_368979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_368979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_368979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_368979 prefixEnd_368979 := by exact prefixLift 368979
  have htrace : WordTrace (prefixWord ++ tailWord_368979) baseStart_368979 baseEnd_368979 := by
    simpa [prefixWord, tailWord_368979, baseEnd_368979] using wordTrace_append hprefix tailTrace_368979
  have hstable : (prefixWord ++ tailWord_368979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368979).length < 2 ^ (prefixWord ++ tailWord_368979).sum := by decide
  have hdescent : baseEnd_368979 < baseStart_368979 := by decide
  rcases family_descends (prefixWord ++ tailWord_368979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369058 : List Nat := [3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_369058 : Nat := 118140960795 + 369058 * 2 ^ 59
def prefixEnd_369058 : Nat := 4983230072969 + 3 ^ 40 * 369058 * 2
def baseEnd_369058 : Nat := 56149375818406605208219

theorem tailTrace_369058 : CollatzResearch.WordTrace tailWord_369058 prefixEnd_369058 56149375818406605208219 := by
  unfold tailWord_369058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365162774243342733356957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8973767397982247288951885 3365162774243342733356957)
  ·
    refine ⟨1261936040341253525008859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3365162774243342733356957 1261936040341253525008859)
    ·
      refine ⟨1892904060511880287513289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261936040341253525008859 1892904060511880287513289)
      ·
        refine ⟨1419678045383910215634967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892904060511880287513289 1419678045383910215634967)
        ·
          refine ⟨2129517068075865323452451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419678045383910215634967 2129517068075865323452451)
          ·
            refine ⟨3194275602113797985178677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129517068075865323452451 3194275602113797985178677)
            ·
              refine ⟨299463337698168561110501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3194275602113797985178677 299463337698168561110501)
              ·
                refine ⟨56149375818406605208219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299463337698168561110501 56149375818406605208219)
                ·
                  rfl

theorem cell20_369058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_369058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369058 prefixEnd_369058 := by exact prefixLift 369058
  have htrace : WordTrace (prefixWord ++ tailWord_369058) baseStart_369058 baseEnd_369058 := by
    simpa [prefixWord, tailWord_369058, baseEnd_369058] using wordTrace_append hprefix tailTrace_369058
  have hstable : (prefixWord ++ tailWord_369058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369058).length < 2 ^ (prefixWord ++ tailWord_369058).sum := by decide
  have hdescent : baseEnd_369058 < baseStart_369058 := by decide
  rcases family_descends (prefixWord ++ tailWord_369058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369117 : List Nat := [1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_369117 : Nat := 118140960795 + 369117 * 2 ^ 59
def prefixEnd_369117 : Nat := 4983230072969 + 3 ^ 40 * 369117 * 2
def baseEnd_369117 : Nat := 56158352220959277552583

theorem tailTrace_369117 : CollatzResearch.WordTrace tailWord_369117 prefixEnd_369117 56158352220959277552583 := by
  unfold tailWord_369117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462803003759624009825605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8975202002506416006550403 13462803003759624009825605)
  ·
    refine ⟨2524275563204929501842301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13462803003759624009825605 2524275563204929501842301)
    ·
      refine ⟨946603336201848563190863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2524275563204929501842301 946603336201848563190863)
      ·
        refine ⟨1419905004302772844786295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946603336201848563190863 1419905004302772844786295)
        ·
          refine ⟨2129857506454159267179443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419905004302772844786295 2129857506454159267179443)
          ·
            refine ⟨3194786259681238900769165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129857506454159267179443 3194786259681238900769165)
            ·
              refine ⟨1198044847380464587788437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3194786259681238900769165 1198044847380464587788437)
              ·
                refine ⟨56158352220959277552583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198044847380464587788437 56158352220959277552583)
                ·
                  rfl

theorem cell20_369117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_369117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369117 prefixEnd_369117 := by exact prefixLift 369117
  have htrace : WordTrace (prefixWord ++ tailWord_369117) baseStart_369117 baseEnd_369117 := by
    simpa [prefixWord, tailWord_369117, baseEnd_369117] using wordTrace_append hprefix tailTrace_369117
  have hstable : (prefixWord ++ tailWord_369117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369117).length < 2 ^ (prefixWord ++ tailWord_369117).sum := by decide
  have hdescent : baseEnd_369117 < baseStart_369117 := by decide
  rcases family_descends (prefixWord ++ tailWord_369117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369123 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 2]
def baseStart_369123 : Nat := 118140960795 + 369123 * 2 ^ 59
def prefixEnd_369123 : Nat := 4983230072969 + 3 ^ 40 * 369123 * 2
def baseEnd_369123 : Nat := 168477795226368478457725

theorem tailTrace_369123 : CollatzResearch.WordTrace tailWord_369123 prefixEnd_369123 168477795226368478457725 := by
  unfold tailWord_369123
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463021841737887034544023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8975347894491924689696015 13463021841737887034544023)
  ·
    refine ⟨20194532762606830551816035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13463021841737887034544023 20194532762606830551816035)
    ·
      refine ⟨30291799143910245827724053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20194532762606830551816035 30291799143910245827724053)
      ·
        refine ⟨1419928084870792773174565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30291799143910245827724053 1419928084870792773174565)
        ·
          refine ⟨266236515913273644970231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1419928084870792773174565 266236515913273644970231)
          ·
            refine ⟨399354773869910467455347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266236515913273644970231 399354773869910467455347)
            ·
              refine ⟨599032160804865701183021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399354773869910467455347 599032160804865701183021)
              ·
                refine ⟨224637060301824637943633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 599032160804865701183021 224637060301824637943633)
                ·
                  refine ⟨168477795226368478457725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224637060301824637943633 168477795226368478457725)
                  ·
                    rfl

theorem cell20_369123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2].length) (baseStart_369123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369123 prefixEnd_369123 := by exact prefixLift 369123
  have htrace : WordTrace (prefixWord ++ tailWord_369123) baseStart_369123 baseEnd_369123 := by
    simpa [prefixWord, tailWord_369123, baseEnd_369123] using wordTrace_append hprefix tailTrace_369123
  have hstable : (prefixWord ++ tailWord_369123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369123).length < 2 ^ (prefixWord ++ tailWord_369123).sum := by decide
  have hdescent : baseEnd_369123 < baseStart_369123 := by decide
  rcases family_descends (prefixWord ++ tailWord_369123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369154 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_369154 : Nat := 118140960795 + 369154 * 2 ^ 59
def prefixEnd_369154 : Nat := 4983230072969 + 3 ^ 40 * 369154 * 2
def baseEnd_369154 : Nat := 168491944471070148424265

theorem tailTrace_369154 : CollatzResearch.WordTrace tailWord_369154 prefixEnd_369154 168491944471070148424265 := by
  unfold tailWord_369154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366038126156394832230629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8976101669750386219281677 3366038126156394832230629)
  ·
    refine ⟨631132148654324031043243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3366038126156394832230629 631132148654324031043243)
    ·
      refine ⟨946698222981486046564865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631132148654324031043243 946698222981486046564865)
      ·
        refine ⟨710023667236114534923649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 946698222981486046564865 710023667236114534923649)
        ·
          refine ⟨532517750427085901192737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710023667236114534923649 532517750427085901192737)
          ·
            refine ⟨399388312820314425894553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532517750427085901192737 399388312820314425894553)
            ·
              refine ⟨299541234615235819420915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399388312820314425894553 299541234615235819420915)
              ·
                refine ⟨449311851922853729131373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299541234615235819420915 449311851922853729131373)
                ·
                  refine ⟨168491944471070148424265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449311851922853729131373 168491944471070148424265)
                  ·
                    rfl

theorem cell20_369154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_369154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369154 prefixEnd_369154 := by exact prefixLift 369154
  have htrace : WordTrace (prefixWord ++ tailWord_369154) baseStart_369154 baseEnd_369154 := by
    simpa [prefixWord, tailWord_369154, baseEnd_369154] using wordTrace_append hprefix tailTrace_369154
  have hstable : (prefixWord ++ tailWord_369154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369154).length < 2 ^ (prefixWord ++ tailWord_369154).sum := by decide
  have hdescent : baseEnd_369154 < baseStart_369154 := by decide
  rcases family_descends (prefixWord ++ tailWord_369154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369172 : List Nat := [2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_369172 : Nat := 118140960795 + 369172 * 2 ^ 59
def prefixEnd_369172 : Nat := 4983230072969 + 3 ^ 40 * 369172 * 2
def baseEnd_369172 : Nat := 56166720053847361941397

theorem tailTrace_369172 : CollatzResearch.WordTrace tailWord_369172 prefixEnd_369172 56166720053847361941397 := by
  unfold tailWord_369172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732404509280184201538885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8976539345706912268718513 6732404509280184201538885)
  ·
    refine ⟨1262325845490034537788541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6732404509280184201538885 1262325845490034537788541)
    ·
      refine ⟨473372192058762951670703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1262325845490034537788541 473372192058762951670703)
      ·
        refine ⟨710058288088144427506055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473372192058762951670703 710058288088144427506055)
        ·
          refine ⟨1065087432132216641259083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710058288088144427506055 1065087432132216641259083)
          ·
            refine ⟨1597631148198324961888625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065087432132216641259083 1597631148198324961888625)
            ·
              refine ⟨1198223361148743721416469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597631148198324961888625 1198223361148743721416469)
              ·
                refine ⟨56166720053847361941397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198223361148743721416469 56166720053847361941397)
                ·
                  rfl

theorem cell20_369172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_369172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369172 prefixEnd_369172 := by exact prefixLift 369172
  have htrace : WordTrace (prefixWord ++ tailWord_369172) baseStart_369172 baseEnd_369172 := by
    simpa [prefixWord, tailWord_369172, baseEnd_369172] using wordTrace_append hprefix tailTrace_369172
  have hstable : (prefixWord ++ tailWord_369172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369172).length < 2 ^ (prefixWord ++ tailWord_369172).sum := by decide
  have hdescent : baseEnd_369172 < baseStart_369172 := by decide
  rcases family_descends (prefixWord ++ tailWord_369172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369200 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_369200 : Nat := 118140960795 + 369200 * 2 ^ 59
def prefixEnd_369200 : Nat := 4983230072969 + 3 ^ 40 * 369200 * 2
def baseEnd_369200 : Nat := 168512940124498432890743

theorem tailTrace_369200 : CollatzResearch.WordTrace tailWord_369200 prefixEnd_369200 168512940124498432890743 := by
  unfold tailWord_369200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732915131229464592548527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8977220174972619456731369 6732915131229464592548527)
  ·
    refine ⟨10099372696844196888822791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6732915131229464592548527 10099372696844196888822791)
    ·
      refine ⟨15149059045266295333234187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099372696844196888822791 15149059045266295333234187)
      ·
        refine ⟨22723588567899442999851281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149059045266295333234187 22723588567899442999851281)
        ·
          refine ⟨17042691425924582249888461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22723588567899442999851281 17042691425924582249888461)
          ·
            refine ⟨6391009284721718343708173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17042691425924582249888461 6391009284721718343708173)
            ·
              refine ⟨2396628481770644378890565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6391009284721718343708173 2396628481770644378890565)
              ·
                refine ⟨449367840331995821041981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2396628481770644378890565 449367840331995821041981)
                ·
                  refine ⟨168512940124498432890743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449367840331995821041981 168512940124498432890743)
                  ·
                    rfl

theorem cell20_369200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_369200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369200 prefixEnd_369200 := by exact prefixLift 369200
  have htrace : WordTrace (prefixWord ++ tailWord_369200) baseStart_369200 baseEnd_369200 := by
    simpa [prefixWord, tailWord_369200, baseEnd_369200] using wordTrace_append hprefix tailTrace_369200
  have hstable : (prefixWord ++ tailWord_369200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369200).length < 2 ^ (prefixWord ++ tailWord_369200).sum := by decide
  have hdescent : baseEnd_369200 < baseStart_369200 := by decide
  rcases family_descends (prefixWord ++ tailWord_369200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369207 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_369207 : Nat := 118140960795 + 369207 * 2 ^ 59
def prefixEnd_369207 : Nat := 4983230072969 + 3 ^ 40 * 369207 * 2
def baseEnd_369207 : Nat := 168516135115237519657381

theorem tailTrace_369207 : CollatzResearch.WordTrace tailWord_369207 prefixEnd_369207 168516135115237519657381 := by
  unfold tailWord_369207
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466085573433569380601875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8977390382289046253734583 13466085573433569380601875)
  ·
    refine ⟨20199128360150354070902813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466085573433569380601875 20199128360150354070902813)
    ·
      refine ⟨7574673135056382776588555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20199128360150354070902813 7574673135056382776588555)
      ·
        refine ⟨11362009702584574164882833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7574673135056382776588555 11362009702584574164882833)
        ·
          refine ⟨8521507276938430623662125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11362009702584574164882833 8521507276938430623662125)
          ·
            refine ⟨3195565228851911483873297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8521507276938430623662125 3195565228851911483873297)
            ·
              refine ⟨2396673921638933612904973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195565228851911483873297 2396673921638933612904973)
              ·
                refine ⟨898752720614600104839365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396673921638933612904973 898752720614600104839365)
                ·
                  refine ⟨168516135115237519657381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898752720614600104839365 168516135115237519657381)
                  ·
                    rfl

theorem cell20_369207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_369207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369207 prefixEnd_369207 := by exact prefixLift 369207
  have htrace : WordTrace (prefixWord ++ tailWord_369207) baseStart_369207 baseEnd_369207 := by
    simpa [prefixWord, tailWord_369207, baseEnd_369207] using wordTrace_append hprefix tailTrace_369207
  have hstable : (prefixWord ++ tailWord_369207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369207).length < 2 ^ (prefixWord ++ tailWord_369207).sum := by decide
  have hdescent : baseEnd_369207 < baseStart_369207 := by decide
  rcases family_descends (prefixWord ++ tailWord_369207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369217 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_369217 : Nat := 118140960795 + 369217 * 2 ^ 59
def prefixEnd_369217 : Nat := 4983230072969 + 3 ^ 40 * 369217 * 2
def baseEnd_369217 : Nat := 168520699387721929324007

theorem tailTrace_369217 : CollatzResearch.WordTrace tailWord_369217 prefixEnd_369217 168520699387721929324007 := by
  unfold tailWord_369217
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466450303397341088465905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8977633535598227392310603 13466450303397341088465905)
  ·
    refine ⟨10099837727548005816349429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13466450303397341088465905 10099837727548005816349429)
    ·
      refine ⟨946859786957625545282759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10099837727548005816349429 946859786957625545282759)
      ·
        refine ⟨1420289680436438317924139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946859786957625545282759 1420289680436438317924139)
        ·
          refine ⟨2130434520654657476886209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420289680436438317924139 2130434520654657476886209)
          ·
            refine ⟨1597825890490993107664657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130434520654657476886209 1597825890490993107664657)
            ·
              refine ⟨1198369417868244830748493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597825890490993107664657 1198369417868244830748493)
              ·
                refine ⟨449388531700591811530685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198369417868244830748493 449388531700591811530685)
                ·
                  refine ⟨168520699387721929324007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449388531700591811530685 168520699387721929324007)
                  ·
                    rfl

theorem cell20_369217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_369217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369217 prefixEnd_369217 := by exact prefixLift 369217
  have htrace : WordTrace (prefixWord ++ tailWord_369217) baseStart_369217 baseEnd_369217 := by
    simpa [prefixWord, tailWord_369217, baseEnd_369217] using wordTrace_append hprefix tailTrace_369217
  have hstable : (prefixWord ++ tailWord_369217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369217).length < 2 ^ (prefixWord ++ tailWord_369217).sum := by decide
  have hdescent : baseEnd_369217 < baseStart_369217 := by decide
  rcases family_descends (prefixWord ++ tailWord_369217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369252 : List Nat := [2, 3, 1, 1, 2, 2, 9]
def baseStart_369252 : Nat := 118140960795 + 369252 * 2 ^ 59
def prefixEnd_369252 : Nat := 4983230072969 + 3 ^ 40 * 369252 * 2
def baseEnd_369252 : Nat := 18726297149046373684133

theorem tailTrace_369252 : CollatzResearch.WordTrace tailWord_369252 prefixEnd_369252 18726297149046373684133 := by
  unfold tailWord_369252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733863429135271032995005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8978484572180361377326673 6733863429135271032995005)
  ·
    refine ⟨2525198785925726637373127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6733863429135271032995005 2525198785925726637373127)
    ·
      refine ⟨3787798178888589956059691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2525198785925726637373127 3787798178888589956059691)
      ·
        refine ⟨5681697268332884934089537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787798178888589956059691 5681697268332884934089537)
        ·
          refine ⟨4261272951249663700567153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5681697268332884934089537 4261272951249663700567153)
          ·
            refine ⟨3195954713437247775425365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261272951249663700567153 3195954713437247775425365)
            ·
              refine ⟨18726297149046373684133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3195954713437247775425365 18726297149046373684133)
              ·
                rfl

theorem cell20_369252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_369252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369252 prefixEnd_369252 := by exact prefixLift 369252
  have htrace : WordTrace (prefixWord ++ tailWord_369252) baseStart_369252 baseEnd_369252 := by
    simpa [prefixWord, tailWord_369252, baseEnd_369252] using wordTrace_append hprefix tailTrace_369252
  have hstable : (prefixWord ++ tailWord_369252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369252).length < 2 ^ (prefixWord ++ tailWord_369252).sum := by decide
  have hdescent : baseEnd_369252 < baseStart_369252 := by decide
  rcases family_descends (prefixWord ++ tailWord_369252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369262 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_369262 : Nat := 118140960795 + 369262 * 2 ^ 59
def prefixEnd_369262 : Nat := 4983230072969 + 3 ^ 40 * 369262 * 2
def baseEnd_369262 : Nat := 168541238613901772823823

theorem tailTrace_369262 : CollatzResearch.WordTrace tailWord_369262 prefixEnd_369262 168541238613901772823823 := by
  unfold tailWord_369262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683511448529289221731755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8978727725489542515902693 1683511448529289221731755)
  ·
    refine ⟨2525267172793933832597633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1683511448529289221731755 2525267172793933832597633)
    ·
      refine ⟨1893950379595450374448225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2525267172793933832597633 1893950379595450374448225)
      ·
        refine ⟨1420462784696587780836169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1893950379595450374448225 1420462784696587780836169)
        ·
          refine ⟨1065347088522440835627127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420462784696587780836169 1065347088522440835627127)
          ·
            refine ⟨1598020632783661253440691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065347088522440835627127 1598020632783661253440691)
            ·
              refine ⟨2397030949175491880161037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598020632783661253440691 2397030949175491880161037)
              ·
                refine ⟨898886605940809455060389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2397030949175491880161037 898886605940809455060389)
                ·
                  refine ⟨168541238613901772823823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898886605940809455060389 168541238613901772823823)
                  ·
                    rfl

theorem cell20_369262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_369262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369262 prefixEnd_369262 := by exact prefixLift 369262
  have htrace : WordTrace (prefixWord ++ tailWord_369262) baseStart_369262 baseEnd_369262 := by
    simpa [prefixWord, tailWord_369262, baseEnd_369262] using wordTrace_append hprefix tailTrace_369262
  have hstable : (prefixWord ++ tailWord_369262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369262).length < 2 ^ (prefixWord ++ tailWord_369262).sum := by decide
  have hdescent : baseEnd_369262 < baseStart_369262 := by decide
  rcases family_descends (prefixWord ++ tailWord_369262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369276 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_369276 : Nat := 118140960795 + 369276 * 2 ^ 59
def prefixEnd_369276 : Nat := 4983230072969 + 3 ^ 40 * 369276 * 2
def baseEnd_369276 : Nat := 168547628595379946357099

theorem tailTrace_369276 : CollatzResearch.WordTrace tailWord_369276 prefixEnd_369276 168547628595379946357099 := by
  unfold tailWord_369276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734301105091797082431841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8979068140122396109909121 6734301105091797082431841)
  ·
    refine ⟨5050725828818847811823881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6734301105091797082431841 5050725828818847811823881)
    ·
      refine ⟨3788044371614135858867911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5050725828818847811823881 3788044371614135858867911)
      ·
        refine ⟨5682066557421203788301867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788044371614135858867911 5682066557421203788301867)
        ·
          refine ⟨8523099836131805682452801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682066557421203788301867 8523099836131805682452801)
          ·
            refine ⟨6392324877098854261839601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8523099836131805682452801 6392324877098854261839601)
            ·
              refine ⟨4794243657824140696379701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6392324877098854261839601 4794243657824140696379701)
              ·
                refine ⟨449460342921013190285597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4794243657824140696379701 449460342921013190285597)
                ·
                  refine ⟨168547628595379946357099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449460342921013190285597 168547628595379946357099)
                  ·
                    rfl

theorem cell20_369276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_369276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369276 prefixEnd_369276 := by exact prefixLift 369276
  have htrace : WordTrace (prefixWord ++ tailWord_369276) baseStart_369276 baseEnd_369276 := by
    simpa [prefixWord, tailWord_369276, baseEnd_369276] using wordTrace_append hprefix tailTrace_369276
  have hstable : (prefixWord ++ tailWord_369276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369276).length < 2 ^ (prefixWord ++ tailWord_369276).sum := by decide
  have hdescent : baseEnd_369276 < baseStart_369276 := by decide
  rcases family_descends (prefixWord ++ tailWord_369276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369282 : List Nat := [3, 4, 3, 1, 1, 1, 1, 6]
def baseStart_369282 : Nat := 118140960795 + 369282 * 2 ^ 59
def prefixEnd_369282 : Nat := 4983230072969 + 3 ^ 40 * 369282 * 2
def baseEnd_369282 : Nat := 56183455719623530719025

theorem tailTrace_369282 : CollatzResearch.WordTrace tailWord_369282 prefixEnd_369282 56183455719623530719025 := by
  unfold tailWord_369282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367205262040464297395525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8979214032107904793054733 3367205262040464297395525)
  ·
    refine ⟨631350986632587055761661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3367205262040464297395525 631350986632587055761661)
    ·
      refine ⟨236756619987220145910623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 631350986632587055761661 236756619987220145910623)
      ·
        refine ⟨355134929980830218865935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236756619987220145910623 355134929980830218865935)
        ·
          refine ⟨532702394971245328298903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355134929980830218865935 532702394971245328298903)
          ·
            refine ⟨799053592456867992448355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532702394971245328298903 799053592456867992448355)
            ·
              refine ⟨1198580388685301988672533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799053592456867992448355 1198580388685301988672533)
              ·
                refine ⟨56183455719623530719025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198580388685301988672533 56183455719623530719025)
                ·
                  rfl

theorem cell20_369282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_369282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369282 prefixEnd_369282 := by exact prefixLift 369282
  have htrace : WordTrace (prefixWord ++ tailWord_369282) baseStart_369282 baseEnd_369282 := by
    simpa [prefixWord, tailWord_369282, baseEnd_369282] using wordTrace_append hprefix tailTrace_369282
  have hstable : (prefixWord ++ tailWord_369282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369282).length < 2 ^ (prefixWord ++ tailWord_369282).sum := by decide
  have hdescent : baseEnd_369282 < baseStart_369282 := by decide
  rcases family_descends (prefixWord ++ tailWord_369282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369283 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_369283 : Nat := 118140960795 + 369283 * 2 ^ 59
def prefixEnd_369283 : Nat := 4983230072969 + 3 ^ 40 * 369283 * 2
def baseEnd_369283 : Nat := 168550823586119033123737

theorem tailTrace_369283 : CollatzResearch.WordTrace tailWord_369283 prefixEnd_369283 168550823586119033123737 := by
  unfold tailWord_369283
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468857521158234360368503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8979238347438822906912335 13468857521158234360368503)
  ·
    refine ⟨20203286281737351540552755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13468857521158234360368503 20203286281737351540552755)
    ·
      refine ⟨30304929422606027310829133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20203286281737351540552755 30304929422606027310829133)
      ·
        refine ⟨11364348533477260241560925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30304929422606027310829133 11364348533477260241560925)
        ·
          refine ⟨4261630700053972590585347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11364348533477260241560925 4261630700053972590585347)
          ·
            refine ⟨6392446050080958885878021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261630700053972590585347 6392446050080958885878021)
            ·
              refine ⟨1198583634390179791102129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6392446050080958885878021 1198583634390179791102129)
              ·
                refine ⟨898937725792634843326597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198583634390179791102129 898937725792634843326597)
                ·
                  refine ⟨168550823586119033123737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898937725792634843326597 168550823586119033123737)
                  ·
                    rfl

theorem cell20_369283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_369283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369283 prefixEnd_369283 := by exact prefixLift 369283
  have htrace : WordTrace (prefixWord ++ tailWord_369283) baseStart_369283 baseEnd_369283 := by
    simpa [prefixWord, tailWord_369283, baseEnd_369283] using wordTrace_append hprefix tailTrace_369283
  have hstable : (prefixWord ++ tailWord_369283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369283).length < 2 ^ (prefixWord ++ tailWord_369283).sum := by decide
  have hdescent : baseEnd_369283 < baseStart_369283 := by decide
  rcases family_descends (prefixWord ++ tailWord_369283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369331 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 3]
def baseStart_369331 : Nat := 118140960795 + 369331 * 2 ^ 59
def prefixEnd_369331 : Nat := 4983230072969 + 3 ^ 40 * 369331 * 2
def baseEnd_369331 : Nat := 168572732094044199523541

theorem tailTrace_369331 : CollatzResearch.WordTrace tailWord_369331 prefixEnd_369331 168572732094044199523541 := by
  unfold tailWord_369331
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470608224984338558115847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8980405483322892372077231 13470608224984338558115847)
  ·
    refine ⟨20205912337476507837173771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470608224984338558115847 20205912337476507837173771)
    ·
      refine ⟨30308868506214761755760657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205912337476507837173771 30308868506214761755760657)
      ·
        refine ⟨22731651379661071316820493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30308868506214761755760657 22731651379661071316820493)
        ·
          refine ⟨8524369267372901743807685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22731651379661071316820493 8524369267372901743807685)
          ·
            refine ⟨1598319237632419076963941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8524369267372901743807685 1598319237632419076963941)
            ·
              refine ⟨299684857056078576930739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1598319237632419076963941 299684857056078576930739)
              ·
                refine ⟨449527285584117865396109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299684857056078576930739 449527285584117865396109)
                ·
                  refine ⟨168572732094044199523541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449527285584117865396109 168572732094044199523541)
                  ·
                    rfl

theorem cell20_369331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_369331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369331 prefixEnd_369331 := by exact prefixLift 369331
  have htrace : WordTrace (prefixWord ++ tailWord_369331) baseStart_369331 baseEnd_369331 := by
    simpa [prefixWord, tailWord_369331, baseEnd_369331] using wordTrace_append hprefix tailTrace_369331
  have hstable : (prefixWord ++ tailWord_369331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369331).length < 2 ^ (prefixWord ++ tailWord_369331).sum := by decide
  have hdescent : baseEnd_369331 < baseStart_369331 := by decide
  rcases family_descends (prefixWord ++ tailWord_369331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369372 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_369372 : Nat := 118140960795 + 369372 * 2 ^ 59
def prefixEnd_369372 : Nat := 4983230072969 + 3 ^ 40 * 369372 * 2
def baseEnd_369372 : Nat := 168591445611230279156707

theorem tailTrace_369372 : CollatzResearch.WordTrace tailWord_369372 prefixEnd_369372 168591445611230279156707 := by
  unfold tailWord_369372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736051808917901280179185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8981402411890535040238913 6736051808917901280179185)
  ·
    refine ⟨5052038856688425960134389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6736051808917901280179185 5052038856688425960134389)
    ·
      refine ⟨473628642814539933762599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5052038856688425960134389 473628642814539933762599)
      ·
        refine ⟨710442964221809900643899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473628642814539933762599 710442964221809900643899)
        ·
          refine ⟨1065664446332714850965849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710442964221809900643899 1065664446332714850965849)
          ·
            refine ⟨799248334749536138224387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065664446332714850965849 799248334749536138224387)
            ·
              refine ⟨1198872502124304207336581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799248334749536138224387 1198872502124304207336581)
              ·
                refine ⟨224788594148307038875609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1198872502124304207336581 224788594148307038875609)
                ·
                  refine ⟨168591445611230279156707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224788594148307038875609 168591445611230279156707)
                  ·
                    rfl

theorem cell20_369372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_369372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369372 prefixEnd_369372 := by exact prefixLift 369372
  have htrace : WordTrace (prefixWord ++ tailWord_369372) baseStart_369372 baseEnd_369372 := by
    simpa [prefixWord, tailWord_369372, baseEnd_369372] using wordTrace_append hprefix tailTrace_369372
  have hstable : (prefixWord ++ tailWord_369372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369372).length < 2 ^ (prefixWord ++ tailWord_369372).sum := by decide
  have hdescent : baseEnd_369372 < baseStart_369372 := by decide
  rcases family_descends (prefixWord ++ tailWord_369372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369396 : List Nat := [2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_369396 : Nat := 118140960795 + 369396 * 2 ^ 59
def prefixEnd_369396 : Nat := 4983230072969 + 3 ^ 40 * 369396 * 2
def baseEnd_369396 : Nat := 56200799955064287452203

theorem tailTrace_369396 : CollatzResearch.WordTrace tailWord_369396 prefixEnd_369396 56200799955064287452203 := by
  unfold tailWord_369396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736489484874427329616021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8981985979832569772821361 6736489484874427329616021)
  ·
    refine ⟨315772944603488781075751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6736489484874427329616021 315772944603488781075751)
    ·
      refine ⟨473659416905233171613627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315772944603488781075751 473659416905233171613627)
      ·
        refine ⟨710489125357849757420441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473659416905233171613627 710489125357849757420441)
        ·
          refine ⟨532866844018387318065331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710489125357849757420441 532866844018387318065331)
          ·
            refine ⟨799300266027580977097997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532866844018387318065331 799300266027580977097997)
            ·
              refine ⟨299737599760342866411749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799300266027580977097997 299737599760342866411749)
              ·
                refine ⟨56200799955064287452203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299737599760342866411749 56200799955064287452203)
                ·
                  rfl

theorem cell20_369396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_369396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369396 prefixEnd_369396 := by exact prefixLift 369396
  have htrace : WordTrace (prefixWord ++ tailWord_369396) baseStart_369396 baseEnd_369396 := by
    simpa [prefixWord, tailWord_369396, baseEnd_369396] using wordTrace_append hprefix tailTrace_369396
  have hstable : (prefixWord ++ tailWord_369396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369396).length < 2 ^ (prefixWord ++ tailWord_369396).sum := by decide
  have hdescent : baseEnd_369396 < baseStart_369396 := by decide
  rcases family_descends (prefixWord ++ tailWord_369396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369410 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_369410 : Nat := 118140960795 + 369410 * 2 ^ 59
def prefixEnd_369410 : Nat := 4983230072969 + 3 ^ 40 * 369410 * 2
def baseEnd_369410 : Nat := 168608789846671035889885

theorem tailTrace_369410 : CollatzResearch.WordTrace tailWord_369410 prefixEnd_369410 168608789846671035889885 := by
  unfold tailWord_369410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368372397924533762560421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8982326394465423366827789 3368372397924533762560421)
  ·
    refine ⟨631569824610850080480079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3368372397924533762560421 631569824610850080480079)
    ·
      refine ⟨947354736916275120720119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631569824610850080480079 947354736916275120720119)
      ·
        refine ⟨1421032105374412681080179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947354736916275120720119 1421032105374412681080179)
        ·
          refine ⟨2131548158061619021620269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421032105374412681080179 2131548158061619021620269)
          ·
            refine ⟨799330559273107133107601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2131548158061619021620269 799330559273107133107601)
            ·
              refine ⟨599497919454830349830701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799330559273107133107601 599497919454830349830701)
              ·
                refine ⟨224811719795561381186513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 599497919454830349830701 224811719795561381186513)
                ·
                  refine ⟨168608789846671035889885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224811719795561381186513 168608789846671035889885)
                  ·
                    rfl

theorem cell20_369410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_369410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369410 prefixEnd_369410 := by exact prefixLift 369410
  have htrace : WordTrace (prefixWord ++ tailWord_369410) baseStart_369410 baseEnd_369410 := by
    simpa [prefixWord, tailWord_369410, baseEnd_369410] using wordTrace_append hprefix tailTrace_369410
  have hstable : (prefixWord ++ tailWord_369410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369410).length < 2 ^ (prefixWord ++ tailWord_369410).sum := by decide
  have hdescent : baseEnd_369410 < baseStart_369410 := by decide
  rcases family_descends (prefixWord ++ tailWord_369410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369411 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_369411 : Nat := 118140960795 + 369411 * 2 ^ 59
def prefixEnd_369411 : Nat := 4983230072969 + 3 ^ 40 * 369411 * 2
def baseEnd_369411 : Nat := 168609246273919476856547

theorem tailTrace_369411 : CollatzResearch.WordTrace tailWord_369411 prefixEnd_369411 168609246273919476856547 := by
  unfold tailWord_369411
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473526064694512221028087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8982350709796341480685391 13473526064694512221028087)
  ·
    refine ⟨20210289097041768331542131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13473526064694512221028087 20210289097041768331542131)
    ·
      refine ⟨30315433645562652497313197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20210289097041768331542131 30315433645562652497313197)
      ·
        refine ⟨11368287617085994686492449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30315433645562652497313197 11368287617085994686492449)
        ·
          refine ⟨8526215712814496014869337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11368287617085994686492449 8526215712814496014869337)
          ·
            refine ⟨6394661784610872011152003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8526215712814496014869337 6394661784610872011152003)
            ·
              refine ⟨9591992676916308016728005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6394661784610872011152003 9591992676916308016728005)
              ·
                refine ⟨1798498626921807753136501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9591992676916308016728005 1798498626921807753136501)
                ·
                  refine ⟨168609246273919476856547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1798498626921807753136501 168609246273919476856547)
                  ·
                    rfl

theorem cell20_369411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_369411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369411 prefixEnd_369411 := by exact prefixLift 369411
  have htrace : WordTrace (prefixWord ++ tailWord_369411) baseStart_369411 baseEnd_369411 := by
    simpa [prefixWord, tailWord_369411, baseEnd_369411] using wordTrace_append hprefix tailTrace_369411
  have hstable : (prefixWord ++ tailWord_369411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369411).length < 2 ^ (prefixWord ++ tailWord_369411).sum := by decide
  have hdescent : baseEnd_369411 < baseStart_369411 := by decide
  rcases family_descends (prefixWord ++ tailWord_369411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369445 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 3]
def baseStart_369445 : Nat := 118140960795 + 369445 * 2 ^ 59
def prefixEnd_369445 : Nat := 4983230072969 + 3 ^ 40 * 369445 * 2
def baseEnd_369445 : Nat := 168624764800366469723075

theorem tailTrace_369445 : CollatzResearch.WordTrace tailWord_369445 prefixEnd_369445 168624764800366469723075 := by
  unfold tailWord_369445
  simp only [CollatzResearch.WordTrace]
  refine ⟨13474766146571336027765789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8983177431047557351843859 13474766146571336027765789)
  ·
    refine ⟨5053037304964251010412171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13474766146571336027765789 5053037304964251010412171)
    ·
      refine ⟨7579555957446376515618257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053037304964251010412171 7579555957446376515618257)
      ·
        refine ⟨5684666968084782386713693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579555957446376515618257 5684666968084782386713693)
        ·
          refine ⟨2131750113031793395017635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5684666968084782386713693 2131750113031793395017635)
          ·
            refine ⟨3197625169547690092526453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131750113031793395017635 3197625169547690092526453)
            ·
              refine ⟨299777359645095946174355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3197625169547690092526453 299777359645095946174355)
              ·
                refine ⟨449666039467643919261533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299777359645095946174355 449666039467643919261533)
                ·
                  refine ⟨168624764800366469723075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449666039467643919261533 168624764800366469723075)
                  ·
                    rfl

theorem cell20_369445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_369445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369445 prefixEnd_369445 := by exact prefixLift 369445
  have htrace : WordTrace (prefixWord ++ tailWord_369445) baseStart_369445 baseEnd_369445 := by
    simpa [prefixWord, tailWord_369445, baseEnd_369445] using wordTrace_append hprefix tailTrace_369445
  have hstable : (prefixWord ++ tailWord_369445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369445).length < 2 ^ (prefixWord ++ tailWord_369445).sum := by decide
  have hdescent : baseEnd_369445 < baseStart_369445 := by decide
  rcases family_descends (prefixWord ++ tailWord_369445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369459 : List Nat := [1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_369459 : Nat := 118140960795 + 369459 * 2 ^ 59
def prefixEnd_369459 : Nat := 4983230072969 + 3 ^ 40 * 369459 * 2
def baseEnd_369459 : Nat := 56210384927281547752117

theorem tailTrace_369459 : CollatzResearch.WordTrace tailWord_369459 prefixEnd_369459 56210384927281547752117 := by
  unfold tailWord_369459
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475276768520616418775431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8983517845680410945850287 13475276768520616418775431)
  ·
    refine ⟨20212915152780924628163147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13475276768520616418775431 20212915152780924628163147)
    ·
      refine ⟨30319372729171386942244721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20212915152780924628163147 30319372729171386942244721)
      ·
        refine ⟨22739529546878540206683541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30319372729171386942244721 22739529546878540206683541)
        ·
          refine ⟨1065915447509931572188291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22739529546878540206683541 1065915447509931572188291)
          ·
            refine ⟨1598873171264897358282437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065915447509931572188291 1598873171264897358282437)
            ·
              refine ⟨299788719612168254677957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1598873171264897358282437 299788719612168254677957)
              ·
                refine ⟨56210384927281547752117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299788719612168254677957 56210384927281547752117)
                ·
                  rfl

theorem cell20_369459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_369459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369459 prefixEnd_369459 := by exact prefixLift 369459
  have htrace : WordTrace (prefixWord ++ tailWord_369459) baseStart_369459 baseEnd_369459 := by
    simpa [prefixWord, tailWord_369459, baseEnd_369459] using wordTrace_append hprefix tailTrace_369459
  have hstable : (prefixWord ++ tailWord_369459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369459).length < 2 ^ (prefixWord ++ tailWord_369459).sum := by decide
  have hdescent : baseEnd_369459 < baseStart_369459 := by decide
  rcases family_descends (prefixWord ++ tailWord_369459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369500 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_369500 : Nat := 118140960795 + 369500 * 2 ^ 59
def prefixEnd_369500 : Nat := 4983230072969 + 3 ^ 40 * 369500 * 2
def baseEnd_369500 : Nat := 168649868299030722889517

theorem tailTrace_369500 : CollatzResearch.WordTrace tailWord_369500 prefixEnd_369500 168649868299030722889517 := by
  unfold tailWord_369500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738386080686040210508977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8984514774248053614011969 6738386080686040210508977)
  ·
    refine ⟨5053789560514530157881733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6738386080686040210508977 5053789560514530157881733)
    ·
      refine ⟨947585542596474404602825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5053789560514530157881733 947585542596474404602825)
      ·
        refine ⟨710689156947355803452119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 947585542596474404602825 710689156947355803452119)
        ·
          refine ⟨1066033735421033705178179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710689156947355803452119 1066033735421033705178179)
          ·
            refine ⟨1599050603131550557767269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066033735421033705178179 1599050603131550557767269)
            ·
              refine ⟨299821988087165729581363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1599050603131550557767269 299821988087165729581363)
              ·
                refine ⟨449732982130748594372045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299821988087165729581363 449732982130748594372045)
                ·
                  refine ⟨168649868299030722889517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449732982130748594372045 168649868299030722889517)
                  ·
                    rfl

theorem cell20_369500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_369500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369500 prefixEnd_369500 := by exact prefixLift 369500
  have htrace : WordTrace (prefixWord ++ tailWord_369500) baseStart_369500 baseEnd_369500 := by
    simpa [prefixWord, tailWord_369500, baseEnd_369500] using wordTrace_append hprefix tailTrace_369500
  have hstable : (prefixWord ++ tailWord_369500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369500).length < 2 ^ (prefixWord ++ tailWord_369500).sum := by decide
  have hdescent : baseEnd_369500 < baseStart_369500 := by decide
  rcases family_descends (prefixWord ++ tailWord_369500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369504 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_369504 : Nat := 118140960795 + 369504 * 2 ^ 59
def prefixEnd_369504 : Nat := 4983230072969 + 3 ^ 40 * 369504 * 2
def baseEnd_369504 : Nat := 168651694008024486756167

theorem tailTrace_369504 : CollatzResearch.WordTrace tailWord_369504 prefixEnd_369504 168651694008024486756167 := by
  unfold tailWord_369504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738459026678794552081783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8984612035571726069442377 6738459026678794552081783)
  ·
    refine ⟨10107688540018191828122675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6738459026678794552081783 10107688540018191828122675)
    ·
      refine ⟨15161532810027287742184013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10107688540018191828122675 15161532810027287742184013)
      ·
        refine ⟨5685574803760232903319005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15161532810027287742184013 5685574803760232903319005)
        ·
          refine ⟨2132090551410087338744627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5685574803760232903319005 2132090551410087338744627)
          ·
            refine ⟨3198135827115131008116941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132090551410087338744627 3198135827115131008116941)
            ·
              refine ⟨1199300935168174128043853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3198135827115131008116941 1199300935168174128043853)
              ·
                refine ⟨449737850688065298016445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199300935168174128043853 449737850688065298016445)
                ·
                  refine ⟨168651694008024486756167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449737850688065298016445 168651694008024486756167)
                  ·
                    rfl

theorem cell20_369504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_369504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369504 prefixEnd_369504 := by exact prefixLift 369504
  have htrace : WordTrace (prefixWord ++ tailWord_369504) baseStart_369504 baseEnd_369504 := by
    simpa [prefixWord, tailWord_369504, baseEnd_369504] using wordTrace_append hprefix tailTrace_369504
  have hstable : (prefixWord ++ tailWord_369504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369504).length < 2 ^ (prefixWord ++ tailWord_369504).sum := by decide
  have hdescent : baseEnd_369504 < baseStart_369504 := by decide
  rcases family_descends (prefixWord ++ tailWord_369504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369545 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 2]
def baseStart_369545 : Nat := 118140960795 + 369545 * 2 ^ 59
def prefixEnd_369545 : Nat := 4983230072969 + 3 ^ 40 * 369545 * 2
def baseEnd_369545 : Nat := 168670407525210566389333

theorem tailTrace_369545 : CollatzResearch.WordTrace tailWord_369545 prefixEnd_369545 168670407525210566389333 := by
  unfold tailWord_369545
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478413446209053106406089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8985608964139368737604059 13478413446209053106406089)
  ·
    refine ⟨10108810084656789829804567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13478413446209053106406089 10108810084656789829804567)
    ·
      refine ⟨15163215126985184744706851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10108810084656789829804567 15163215126985184744706851)
      ·
        refine ⟨22744822690477777117060277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15163215126985184744706851 22744822690477777117060277)
        ·
          refine ⟨2132327127232291604724401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22744822690477777117060277 2132327127232291604724401)
          ·
            refine ⟨1599245345424218703543301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2132327127232291604724401 1599245345424218703543301)
            ·
              refine ⟨299858502267041006914369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1599245345424218703543301 299858502267041006914369)
              ·
                refine ⟨224893876700280755185777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299858502267041006914369 224893876700280755185777)
                ·
                  refine ⟨168670407525210566389333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224893876700280755185777 168670407525210566389333)
                  ·
                    rfl

theorem cell20_369545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_369545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369545 prefixEnd_369545 := by exact prefixLift 369545
  have htrace : WordTrace (prefixWord ++ tailWord_369545) baseStart_369545 baseEnd_369545 := by
    simpa [prefixWord, tailWord_369545, baseEnd_369545] using wordTrace_append hprefix tailTrace_369545
  have hstable : (prefixWord ++ tailWord_369545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369545).length < 2 ^ (prefixWord ++ tailWord_369545).sum := by decide
  have hdescent : baseEnd_369545 < baseStart_369545 := by decide
  rcases family_descends (prefixWord ++ tailWord_369545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369625 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_369625 : Nat := 118140960795 + 369625 * 2 ^ 59
def prefixEnd_369625 : Nat := 4983230072969 + 3 ^ 40 * 369625 * 2
def baseEnd_369625 : Nat := 168706921705085843722339

theorem tailTrace_369625 : CollatzResearch.WordTrace tailWord_369625 prefixEnd_369625 168706921705085843722339 := by
  unfold tailWord_369625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481331285919226769318329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8987554190612817846212219 13481331285919226769318329)
  ·
    refine ⟨10110998464439420076988747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13481331285919226769318329 10110998464439420076988747)
    ·
      refine ⟨15166497696659130115483121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10110998464439420076988747 15166497696659130115483121)
      ·
        refine ⟨11374873272494347586612341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15166497696659130115483121 11374873272494347586612341)
        ·
          refine ⟨1066394369296345086244907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11374873272494347586612341 1066394369296345086244907)
          ·
            refine ⟨1599591553944517629367361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066394369296345086244907 1599591553944517629367361)
            ·
              refine ⟨1199693665458388222025521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599591553944517629367361 1199693665458388222025521)
              ·
                refine ⟨899770249093791166519141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199693665458388222025521 899770249093791166519141)
                ·
                  refine ⟨168706921705085843722339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899770249093791166519141 168706921705085843722339)
                  ·
                    rfl

theorem cell20_369625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_369625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369625 prefixEnd_369625 := by exact prefixLift 369625
  have htrace : WordTrace (prefixWord ++ tailWord_369625) baseStart_369625 baseEnd_369625 := by
    simpa [prefixWord, tailWord_369625, baseEnd_369625] using wordTrace_append hprefix tailTrace_369625
  have hstable : (prefixWord ++ tailWord_369625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369625).length < 2 ^ (prefixWord ++ tailWord_369625).sum := by decide
  have hdescent : baseEnd_369625 < baseStart_369625 := by decide
  rcases family_descends (prefixWord ++ tailWord_369625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369725 : List Nat := [1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_369725 : Nat := 118140960795 + 369725 * 2 ^ 59
def prefixEnd_369725 : Nat := 4983230072969 + 3 ^ 40 * 369725 * 2
def baseEnd_369725 : Nat := 56250854809976646796199

theorem tailTrace_369725 : CollatzResearch.WordTrace tailWord_369725 prefixEnd_369725 56250854809976646796199 := by
  unfold tailWord_369725
  simp only [CollatzResearch.WordTrace]
  refine ⟨13484978585556943847958629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8989985723704629231972419 13484978585556943847958629)
  ·
    refine ⟨2528433484791926971492243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13484978585556943847958629 2528433484791926971492243)
    ·
      refine ⟨3792650227187890457238365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528433484791926971492243 3792650227187890457238365)
      ·
        refine ⟨1422243835195458921464387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3792650227187890457238365 1422243835195458921464387)
        ·
          refine ⟨2133365752793188382196581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422243835195458921464387 2133365752793188382196581)
          ·
            refine ⟨400006078648722821661859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2133365752793188382196581 400006078648722821661859)
            ·
              refine ⟨600009117973084232492789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400006078648722821661859 600009117973084232492789)
              ·
                refine ⟨56250854809976646796199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600009117973084232492789 56250854809976646796199)
                ·
                  rfl

theorem cell20_369725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_369725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369725 prefixEnd_369725 := by exact prefixLift 369725
  have htrace : WordTrace (prefixWord ++ tailWord_369725) baseStart_369725 baseEnd_369725 := by
    simpa [prefixWord, tailWord_369725, baseEnd_369725] using wordTrace_append hprefix tailTrace_369725
  have hstable : (prefixWord ++ tailWord_369725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369725).length < 2 ^ (prefixWord ++ tailWord_369725).sum := by decide
  have hdescent : baseEnd_369725 < baseStart_369725 := by decide
  rcases family_descends (prefixWord ++ tailWord_369725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369760 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_369760 : Nat := 118140960795 + 369760 * 2 ^ 59
def prefixEnd_369760 : Nat := 4983230072969 + 3 ^ 40 * 369760 * 2
def baseEnd_369760 : Nat := 168768539383625374221787

theorem tailTrace_369760 : CollatzResearch.WordTrace tailWord_369760 prefixEnd_369760 168768539383625374221787 := by
  unfold tailWord_369760
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743127570215072412741367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8990836760286763216988489 6743127570215072412741367)
  ·
    refine ⟨10114691355322608619112051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6743127570215072412741367 10114691355322608619112051)
    ·
      refine ⟨15172037032983912928668077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114691355322608619112051 15172037032983912928668077)
      ·
        refine ⟨5689513887368967348250529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15172037032983912928668077 5689513887368967348250529)
        ·
          refine ⟨4267135415526725511187897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5689513887368967348250529 4267135415526725511187897)
          ·
            refine ⟨3200351561645044133390923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267135415526725511187897 3200351561645044133390923)
            ·
              refine ⟨4800527342467566200086385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200351561645044133390923 4800527342467566200086385)
              ·
                refine ⟨3600395506850674650064789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800527342467566200086385 3600395506850674650064789)
                ·
                  refine ⟨168768539383625374221787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3600395506850674650064789 168768539383625374221787)
                  ·
                    rfl

theorem cell20_369760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_369760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369760 prefixEnd_369760 := by exact prefixLift 369760
  have htrace : WordTrace (prefixWord ++ tailWord_369760) baseStart_369760 baseEnd_369760 := by
    simpa [prefixWord, tailWord_369760, baseEnd_369760] using wordTrace_append hprefix tailTrace_369760
  have hstable : (prefixWord ++ tailWord_369760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369760).length < 2 ^ (prefixWord ++ tailWord_369760).sum := by decide
  have hdescent : baseEnd_369760 < baseStart_369760 := by decide
  rcases family_descends (prefixWord ++ tailWord_369760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369770 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_369770 : Nat := 118140960795 + 369770 * 2 ^ 59
def prefixEnd_369770 : Nat := 4983230072969 + 3 ^ 40 * 369770 * 2
def baseEnd_369770 : Nat := 168773103656109783888413

theorem tailTrace_369770 : CollatzResearch.WordTrace tailWord_369770 prefixEnd_369770 168773103656109783888413 := by
  unfold tailWord_369770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371654967598479133336691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8991079913595944355564509 3371654967598479133336691)
  ·
    refine ⟨5057482451397718700005037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371654967598479133336691 5057482451397718700005037)
    ·
      refine ⟨1896555919274144512501889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5057482451397718700005037 1896555919274144512501889)
      ·
        refine ⟨1422416939455608384376417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1896555919274144512501889 1422416939455608384376417)
        ·
          refine ⟨1066812704591706288282313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1422416939455608384376417 1066812704591706288282313)
          ·
            refine ⟨800109528443779716211735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066812704591706288282313 800109528443779716211735)
            ·
              refine ⟨1200164292665669574317603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800109528443779716211735 1200164292665669574317603)
              ·
                refine ⟨1800246438998504361476405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200164292665669574317603 1800246438998504361476405)
                ·
                  refine ⟨168773103656109783888413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1800246438998504361476405 168773103656109783888413)
                  ·
                    rfl

theorem cell20_369770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_369770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369770 prefixEnd_369770 := by exact prefixLift 369770
  have htrace : WordTrace (prefixWord ++ tailWord_369770) baseStart_369770 baseEnd_369770 := by
    simpa [prefixWord, tailWord_369770, baseEnd_369770] using wordTrace_append hprefix tailTrace_369770
  have hstable : (prefixWord ++ tailWord_369770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369770).length < 2 ^ (prefixWord ++ tailWord_369770).sum := by decide
  have hdescent : baseEnd_369770 < baseStart_369770 := by decide
  rcases family_descends (prefixWord ++ tailWord_369770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369801 : List Nat := [1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_369801 : Nat := 118140960795 + 369801 * 2 ^ 59
def prefixEnd_369801 : Nat := 4983230072969 + 3 ^ 40 * 369801 * 2
def baseEnd_369801 : Nat := 56262417633603817951651

theorem tailTrace_369801 : CollatzResearch.WordTrace tailWord_369801 prefixEnd_369801 56262417633603817951651 := by
  unfold tailWord_369801
  simp only [CollatzResearch.WordTrace]
  refine ⟨13487750533281608827725257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8991833688854405885150171 13487750533281608827725257)
  ·
    refine ⟨10115812899961206620793943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13487750533281608827725257 10115812899961206620793943)
    ·
      refine ⟨15173719349941809931190915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10115812899961206620793943 15173719349941809931190915)
      ·
        refine ⟨22760579024912714896786373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15173719349941809931190915 22760579024912714896786373)
        ·
          refine ⟨4267608567171134043147445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22760579024912714896786373 4267608567171134043147445)
          ·
            refine ⟨400088303172293816545073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4267608567171134043147445 400088303172293816545073)
            ·
              refine ⟨300066227379220362408805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400088303172293816545073 300066227379220362408805)
              ·
                refine ⟨56262417633603817951651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300066227379220362408805 56262417633603817951651)
                ·
                  rfl

theorem cell20_369801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_369801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369801 prefixEnd_369801 := by exact prefixLift 369801
  have htrace : WordTrace (prefixWord ++ tailWord_369801) baseStart_369801 baseEnd_369801 := by
    simpa [prefixWord, tailWord_369801, baseEnd_369801] using wordTrace_append hprefix tailTrace_369801
  have hstable : (prefixWord ++ tailWord_369801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369801).length < 2 ^ (prefixWord ++ tailWord_369801).sum := by decide
  have hdescent : baseEnd_369801 < baseStart_369801 := by decide
  rcases family_descends (prefixWord ++ tailWord_369801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369829 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_369829 : Nat := 118140960795 + 369829 * 2 ^ 59
def prefixEnd_369829 : Nat := 4983230072969 + 3 ^ 40 * 369829 * 2
def baseEnd_369829 : Nat := 168800032863767800921505

theorem tailTrace_369829 : CollatzResearch.WordTrace tailWord_369829 prefixEnd_369829 168800032863767800921505 := by
  unfold tailWord_369829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488771777180169609744541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8992514518120113073163027 13488771777180169609744541)
  ·
    refine ⟨5058289416442563603654203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13488771777180169609744541 5058289416442563603654203)
    ·
      refine ⟨7587434124663845405481305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058289416442563603654203 7587434124663845405481305)
      ·
        refine ⟨5690575593497884054110979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587434124663845405481305 5690575593497884054110979)
        ·
          refine ⟨8535863390246826081166469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690575593497884054110979 8535863390246826081166469)
          ·
            refine ⟨1600474385671279890218713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8535863390246826081166469 1600474385671279890218713)
            ·
              refine ⟨1200355789253459917664035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600474385671279890218713 1200355789253459917664035)
              ·
                refine ⟨1800533683880189876496053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200355789253459917664035 1800533683880189876496053)
                ·
                  refine ⟨168800032863767800921505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1800533683880189876496053 168800032863767800921505)
                  ·
                    rfl

theorem cell20_369829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_369829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369829 prefixEnd_369829 := by exact prefixLift 369829
  have htrace : WordTrace (prefixWord ++ tailWord_369829) baseStart_369829 baseEnd_369829 := by
    simpa [prefixWord, tailWord_369829, baseEnd_369829] using wordTrace_append hprefix tailTrace_369829
  have hstable : (prefixWord ++ tailWord_369829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369829).length < 2 ^ (prefixWord ++ tailWord_369829).sum := by decide
  have hdescent : baseEnd_369829 < baseStart_369829 := by decide
  rcases family_descends (prefixWord ++ tailWord_369829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369836 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_369836 : Nat := 118140960795 + 369836 * 2 ^ 59
def prefixEnd_369836 : Nat := 4983230072969 + 3 ^ 40 * 369836 * 2
def baseEnd_369836 : Nat := 168803227854506887688143

theorem tailTrace_369836 : CollatzResearch.WordTrace tailWord_369836 prefixEnd_369836 168803227854506887688143 := by
  unfold tailWord_369836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744513544077404902624681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8992684725436539870166241 6744513544077404902624681)
  ·
    refine ⟨5058385158058053676968511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6744513544077404902624681 5058385158058053676968511)
    ·
      refine ⟨7587577737087080515452767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058385158058053676968511 7587577737087080515452767)
      ·
        refine ⟨11381366605630620773179151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587577737087080515452767 11381366605630620773179151)
        ·
          refine ⟨17072049908445931159768727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11381366605630620773179151 17072049908445931159768727)
          ·
            refine ⟨25608074862668896739653091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17072049908445931159768727 25608074862668896739653091)
            ·
              refine ⟨38412112294003345109479637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25608074862668896739653091 38412112294003345109479637)
              ·
                refine ⟨900283881890703401003429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38412112294003345109479637 900283881890703401003429)
                ·
                  refine ⟨168803227854506887688143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900283881890703401003429 168803227854506887688143)
                  ·
                    rfl

theorem cell20_369836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_369836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369836 prefixEnd_369836 := by exact prefixLift 369836
  have htrace : WordTrace (prefixWord ++ tailWord_369836) baseStart_369836 baseEnd_369836 := by
    simpa [prefixWord, tailWord_369836, baseEnd_369836] using wordTrace_append hprefix tailTrace_369836
  have hstable : (prefixWord ++ tailWord_369836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369836).length < 2 ^ (prefixWord ++ tailWord_369836).sum := by decide
  have hdescent : baseEnd_369836 < baseStart_369836 := by decide
  rcases family_descends (prefixWord ++ tailWord_369836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369843 : List Nat := [1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_369843 : Nat := 118140960795 + 369843 * 2 ^ 59
def prefixEnd_369843 : Nat := 4983230072969 + 3 ^ 40 * 369843 * 2
def baseEnd_369843 : Nat := 56268807615081991484927

theorem tailTrace_369843 : CollatzResearch.WordTrace tailWord_369843 prefixEnd_369843 56268807615081991484927 := by
  unfold tailWord_369843
  simp only [CollatzResearch.WordTrace]
  refine ⟨13489282399129450000754183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8992854932752966667169455 13489282399129450000754183)
  ·
    refine ⟨20233923598694175001131275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13489282399129450000754183 20233923598694175001131275)
    ·
      refine ⟨30350885398041262501696913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20233923598694175001131275 30350885398041262501696913)
      ·
        refine ⟨22763164048530946876272685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30350885398041262501696913 22763164048530946876272685)
        ·
          refine ⟨8536186518199105078602257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22763164048530946876272685 8536186518199105078602257)
          ·
            refine ⟨6402139888649328808951693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536186518199105078602257 6402139888649328808951693)
            ·
              refine ⟨2400802458243498303356885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6402139888649328808951693 2400802458243498303356885)
              ·
                refine ⟨56268807615081991484927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2400802458243498303356885 56268807615081991484927)
                ·
                  rfl

theorem cell20_369843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_369843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369843 prefixEnd_369843 := by exact prefixLift 369843
  have htrace : WordTrace (prefixWord ++ tailWord_369843) baseStart_369843 baseEnd_369843 := by
    simpa [prefixWord, tailWord_369843, baseEnd_369843] using wordTrace_append hprefix tailTrace_369843
  have hstable : (prefixWord ++ tailWord_369843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369843).length < 2 ^ (prefixWord ++ tailWord_369843).sum := by decide
  have hdescent : baseEnd_369843 < baseStart_369843 := by decide
  rcases family_descends (prefixWord ++ tailWord_369843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369898 : List Nat := [3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_369898 : Nat := 118140960795 + 369898 * 2 ^ 59
def prefixEnd_369898 : Nat := 4983230072969 + 3 ^ 40 * 369898 * 2
def baseEnd_369898 : Nat := 56277175447970075873741

theorem tailTrace_369898 : CollatzResearch.WordTrace tailWord_369898 prefixEnd_369898 56277175447970075873741 := by
  unfold tailWord_369898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372822103482548598501587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8994192275953462929337565 3372822103482548598501587)
  ·
    refine ⟨5059233155223822897752381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372822103482548598501587 5059233155223822897752381)
    ·
      refine ⟨1897212433208933586657143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5059233155223822897752381 1897212433208933586657143)
      ·
        refine ⟨2845818649813400379985715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897212433208933586657143 2845818649813400379985715)
        ·
          refine ⟨4268727974720100569978573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845818649813400379985715 4268727974720100569978573)
          ·
            refine ⟨1600772990520037713741965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4268727974720100569978573 1600772990520037713741965)
            ·
              refine ⟨600289871445014142653237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600772990520037713741965 600289871445014142653237)
              ·
                refine ⟨56277175447970075873741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600289871445014142653237 56277175447970075873741)
                ·
                  rfl

theorem cell20_369898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_369898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369898 prefixEnd_369898 := by exact prefixLift 369898
  have htrace : WordTrace (prefixWord ++ tailWord_369898) baseStart_369898 baseEnd_369898 := by
    simpa [prefixWord, tailWord_369898, baseEnd_369898] using wordTrace_append hprefix tailTrace_369898
  have hstable : (prefixWord ++ tailWord_369898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369898).length < 2 ^ (prefixWord ++ tailWord_369898).sum := by decide
  have hdescent : baseEnd_369898 < baseStart_369898 := by decide
  rcases family_descends (prefixWord ++ tailWord_369898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369943 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_369943 : Nat := 118140960795 + 369943 * 2 ^ 59
def prefixEnd_369943 : Nat := 4983230072969 + 3 ^ 40 * 369943 * 2
def baseEnd_369943 : Nat := 168852065570090071121039

theorem tailTrace_369943 : CollatzResearch.WordTrace tailWord_369943 prefixEnd_369943 168852065570090071121039 := by
  unfold tailWord_369943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492929698767167079394483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8995286465844778052929655 13492929698767167079394483)
  ·
    refine ⟨20239394548150750619091725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492929698767167079394483 20239394548150750619091725)
    ·
      refine ⟨7589772955556531482159397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20239394548150750619091725 7589772955556531482159397)
      ·
        refine ⟨1423082429166849652904887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7589772955556531482159397 1423082429166849652904887)
        ·
          refine ⟨2134623643750274479357331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423082429166849652904887 2134623643750274479357331)
          ·
            refine ⟨3201935465625411719035997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134623643750274479357331 3201935465625411719035997)
            ·
              refine ⟨1200725799609529394638499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201935465625411719035997 1200725799609529394638499)
              ·
                refine ⟨1801088699414294091957749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200725799609529394638499 1801088699414294091957749)
                ·
                  refine ⟨168852065570090071121039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1801088699414294091957749 168852065570090071121039)
                  ·
                    rfl

theorem cell20_369943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_369943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369943 prefixEnd_369943 := by exact prefixLift 369943
  have htrace : WordTrace (prefixWord ++ tailWord_369943) baseStart_369943 baseEnd_369943 := by
    simpa [prefixWord, tailWord_369943, baseEnd_369943] using wordTrace_append hprefix tailTrace_369943
  have hstable : (prefixWord ++ tailWord_369943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369943).length < 2 ^ (prefixWord ++ tailWord_369943).sum := by decide
  have hdescent : baseEnd_369943 < baseStart_369943 := by decide
  rcases family_descends (prefixWord ++ tailWord_369943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369946 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_369946 : Nat := 118140960795 + 369946 * 2 ^ 59
def prefixEnd_369946 : Nat := 4983230072969 + 3 ^ 40 * 369946 * 2
def baseEnd_369946 : Nat := 168853434851835394021027

theorem tailTrace_369946 : CollatzResearch.WordTrace tailWord_369946 prefixEnd_369946 168853434851835394021027 := by
  unfold tailWord_369946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373259779439074647938423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8995359411837532394502461 3373259779439074647938423)
  ·
    refine ⟨5059889669158611971907635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3373259779439074647938423 5059889669158611971907635)
    ·
      refine ⟨7589834503737917957861453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059889669158611971907635 7589834503737917957861453)
      ·
        refine ⟨2846187938901719234198045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7589834503737917957861453 2846187938901719234198045)
        ·
          refine ⟨1067320477088144712824267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2846187938901719234198045 1067320477088144712824267)
          ·
            refine ⟨1600980715632217069236401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067320477088144712824267 1600980715632217069236401)
            ·
              refine ⟨1200735536724162801927301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600980715632217069236401 1200735536724162801927301)
              ·
                refine ⟨225137913135780525361369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1200735536724162801927301 225137913135780525361369)
                ·
                  refine ⟨168853434851835394021027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225137913135780525361369 168853434851835394021027)
                  ·
                    rfl

theorem cell20_369946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_369946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369946 prefixEnd_369946 := by exact prefixLift 369946
  have htrace : WordTrace (prefixWord ++ tailWord_369946) baseStart_369946 baseEnd_369946 := by
    simpa [prefixWord, tailWord_369946, baseEnd_369946] using wordTrace_append hprefix tailTrace_369946
  have hstable : (prefixWord ++ tailWord_369946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369946).length < 2 ^ (prefixWord ++ tailWord_369946).sum := by decide
  have hdescent : baseEnd_369946 < baseStart_369946 := by decide
  rcases family_descends (prefixWord ++ tailWord_369946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369997 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 2]
def baseStart_369997 : Nat := 118140960795 + 369997 * 2 ^ 59
def prefixEnd_369997 : Nat := 4983230072969 + 3 ^ 40 * 369997 * 2
def baseEnd_369997 : Nat := 168876712641505883320819

theorem tailTrace_369997 : CollatzResearch.WordTrace tailWord_369997 prefixEnd_369997 168876712641505883320819 := by
  unfold tailWord_369997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494899240571534301860245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8996599493714356201240163 13494899240571534301860245)
  ·
    refine ⟨632573401901790670399699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13494899240571534301860245 632573401901790670399699)
    ·
      refine ⟨948860102852686005599549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632573401901790670399699 948860102852686005599549)
      ·
        refine ⟨355822538569757252099831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 948860102852686005599549 355822538569757252099831)
        ·
          refine ⟨533733807854635878149747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355822538569757252099831 533733807854635878149747)
          ·
            refine ⟨800600711781953817224621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533733807854635878149747 800600711781953817224621)
            ·
              refine ⟨300225266918232681459233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 800600711781953817224621 300225266918232681459233)
              ·
                refine ⟨225168950188674511094425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300225266918232681459233 225168950188674511094425)
                ·
                  refine ⟨168876712641505883320819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225168950188674511094425 168876712641505883320819)
                  ·
                    rfl

theorem cell20_369997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_369997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_369997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_369997 prefixEnd_369997 := by exact prefixLift 369997
  have htrace : WordTrace (prefixWord ++ tailWord_369997) baseStart_369997 baseEnd_369997 := by
    simpa [prefixWord, tailWord_369997, baseEnd_369997] using wordTrace_append hprefix tailTrace_369997
  have hstable : (prefixWord ++ tailWord_369997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369997).length < 2 ^ (prefixWord ++ tailWord_369997).sum := by decide
  have hdescent : baseEnd_369997 < baseStart_369997 := by decide
  rcases family_descends (prefixWord ++ tailWord_369997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370005 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_370005 : Nat := 118140960795 + 370005 * 2 ^ 59
def prefixEnd_370005 : Nat := 4983230072969 + 3 ^ 40 * 370005 * 2
def baseEnd_370005 : Nat := 168880364059493411054119

theorem tailTrace_370005 : CollatzResearch.WordTrace tailWord_370005 prefixEnd_370005 168880364059493411054119 := by
  unfold tailWord_370005
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495191024542551668151469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8996794016361701112100979 13495191024542551668151469)
  ·
    refine ⟨5060696634203456875556801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13495191024542551668151469 5060696634203456875556801)
    ·
      refine ⟨3795522475652592656667601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5060696634203456875556801 3795522475652592656667601)
      ·
        refine ⟨2846641856739444492500701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3795522475652592656667601 2846641856739444492500701)
        ·
          refine ⟨1067490696277291684687763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2846641856739444492500701 1067490696277291684687763)
          ·
            refine ⟨1601236044415937527031645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067490696277291684687763 1601236044415937527031645)
            ·
              refine ⟨600463516655976572636867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1601236044415937527031645 600463516655976572636867)
              ·
                refine ⟨900695274983964858955301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600463516655976572636867 900695274983964858955301)
                ·
                  refine ⟨168880364059493411054119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900695274983964858955301 168880364059493411054119)
                  ·
                    rfl

theorem cell20_370005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_370005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370005 prefixEnd_370005 := by exact prefixLift 370005
  have htrace : WordTrace (prefixWord ++ tailWord_370005) baseStart_370005 baseEnd_370005 := by
    simpa [prefixWord, tailWord_370005, baseEnd_370005] using wordTrace_append hprefix tailTrace_370005
  have hstable : (prefixWord ++ tailWord_370005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370005).length < 2 ^ (prefixWord ++ tailWord_370005).sum := by decide
  have hdescent : baseEnd_370005 < baseStart_370005 := by decide
  rcases family_descends (prefixWord ++ tailWord_370005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370033 : List Nat := [1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_370033 : Nat := 118140960795 + 370033 * 2 ^ 59
def prefixEnd_370033 : Nat := 4983230072969 + 3 ^ 40 * 370033 * 2
def baseEnd_370033 : Nat := 56297714674149919373557

theorem tailTrace_370033 : CollatzResearch.WordTrace tailWord_370033 prefixEnd_370033 56297714674149919373557 := by
  unfold tailWord_370033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496212268441112450170753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8997474845627408300113835 13496212268441112450170753)
  ·
    refine ⟨10122159201330834337628065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13496212268441112450170753 10122159201330834337628065)
    ·
      refine ⟨7591619400998125753221049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10122159201330834337628065 7591619400998125753221049)
      ·
        refine ⟨5693714550748594314915787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7591619400998125753221049 5693714550748594314915787)
        ·
          refine ⟨8540571826122891472373681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693714550748594314915787 8540571826122891472373681)
          ·
            refine ⟨6405428869592168604280261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540571826122891472373681 6405428869592168604280261)
            ·
              refine ⟨1201017913048531613302549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6405428869592168604280261 1201017913048531613302549)
              ·
                refine ⟨56297714674149919373557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1201017913048531613302549 56297714674149919373557)
                ·
                  rfl

theorem cell20_370033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_370033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370033 prefixEnd_370033 := by exact prefixLift 370033
  have htrace : WordTrace (prefixWord ++ tailWord_370033) baseStart_370033 baseEnd_370033 := by
    simpa [prefixWord, tailWord_370033, baseEnd_370033] using wordTrace_append hprefix tailTrace_370033
  have hstable : (prefixWord ++ tailWord_370033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370033).length < 2 ^ (prefixWord ++ tailWord_370033).sum := by decide
  have hdescent : baseEnd_370033 < baseStart_370033 := by decide
  rcases family_descends (prefixWord ++ tailWord_370033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370043 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 2]
def baseStart_370043 : Nat := 118140960795 + 370043 * 2 ^ 59
def prefixEnd_370043 : Nat := 4983230072969 + 3 ^ 40 * 370043 * 2
def baseEnd_370043 : Nat := 168897708294934167787297

theorem tailTrace_370043 : CollatzResearch.WordTrace tailWord_370043 prefixEnd_370043 168897708294934167787297 := by
  unfold tailWord_370043
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496576998404884158034783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8997717998936589438689855 13496576998404884158034783)
  ·
    refine ⟨20244865497607326237052175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13496576998404884158034783 20244865497607326237052175)
    ·
      refine ⟨30367298246410989355578263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20244865497607326237052175 30367298246410989355578263)
      ·
        refine ⟨45550947369616484033367395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30367298246410989355578263 45550947369616484033367395)
        ·
          refine ⟨68326421054424726050051093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45550947369616484033367395 68326421054424726050051093)
          ·
            refine ⟨3202800986926159033596145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68326421054424726050051093 3202800986926159033596145)
            ·
              refine ⟨2402100740194619275197109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202800986926159033596145 2402100740194619275197109)
              ·
                refine ⟨225196944393245557049729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2402100740194619275197109 225196944393245557049729)
                ·
                  refine ⟨168897708294934167787297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225196944393245557049729 168897708294934167787297)
                  ·
                    rfl

theorem cell20_370043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2].length) (baseStart_370043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370043 prefixEnd_370043 := by exact prefixLift 370043
  have htrace : WordTrace (prefixWord ++ tailWord_370043) baseStart_370043 baseEnd_370043 := by
    simpa [prefixWord, tailWord_370043, baseEnd_370043] using wordTrace_append hprefix tailTrace_370043
  have hstable : (prefixWord ++ tailWord_370043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370043).length < 2 ^ (prefixWord ++ tailWord_370043).sum := by decide
  have hdescent : baseEnd_370043 < baseStart_370043 := by decide
  rcases family_descends (prefixWord ++ tailWord_370043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370046 : List Nat := [4, 2, 3, 2, 2, 7]
def baseStart_370046 : Nat := 118140960795 + 370046 * 2 ^ 59
def prefixEnd_370046 : Nat := 4983230072969 + 3 ^ 40 * 370046 * 2
def baseEnd_370046 : Nat := 6255521391728870025455

theorem tailTrace_370046 : CollatzResearch.WordTrace tailWord_370046 prefixEnd_370046 6255521391728870025455 := by
  unfold tailWord_370046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687085802174251958799249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8997790944929343780262661 1687085802174251958799249)
  ·
    refine ⟨1265314351630688969099437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1687085802174251958799249 1265314351630688969099437)
    ·
      refine ⟨474492881861508363412289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1265314351630688969099437 474492881861508363412289)
      ·
        refine ⟨355869661396131272559217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474492881861508363412289 355869661396131272559217)
        ·
          refine ⟨266902246047098454419413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355869661396131272559217 266902246047098454419413)
          ·
            refine ⟨6255521391728870025455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 266902246047098454419413 6255521391728870025455)
            ·
              rfl

theorem cell20_370046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 7].length) (baseStart_370046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370046 prefixEnd_370046 := by exact prefixLift 370046
  have htrace : WordTrace (prefixWord ++ tailWord_370046) baseStart_370046 baseEnd_370046 := by
    simpa [prefixWord, tailWord_370046, baseEnd_370046] using wordTrace_append hprefix tailTrace_370046
  have hstable : (prefixWord ++ tailWord_370046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370046).length < 2 ^ (prefixWord ++ tailWord_370046).sum := by decide
  have hdescent : baseEnd_370046 < baseStart_370046 := by decide
  rcases family_descends (prefixWord ++ tailWord_370046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370108 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_370108 : Nat := 118140960795 + 370108 * 2 ^ 59
def prefixEnd_370108 : Nat := 4983230072969 + 3 ^ 40 * 370108 * 2
def baseEnd_370108 : Nat := 168927376066082830620365

theorem tailTrace_370108 : CollatzResearch.WordTrace tailWord_370108 prefixEnd_370108 168927376066082830620365 := by
  unfold tailWord_370108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6749473871584700129575489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8999298495446266839433985 6749473871584700129575489)
  ·
    refine ⟨5062105403688525097181617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6749473871584700129575489 5062105403688525097181617)
    ·
      refine ⟨3796579052766393822886213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5062105403688525097181617 3796579052766393822886213)
      ·
        refine ⟨711858572393698841791165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3796579052766393822886213 711858572393698841791165)
        ·
          refine ⟨266946964647637065671687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 711858572393698841791165 266946964647637065671687)
          ·
            refine ⟨400420446971455598507531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266946964647637065671687 400420446971455598507531)
            ·
              refine ⟨600630670457183397761297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400420446971455598507531 600630670457183397761297)
              ·
                refine ⟨450473002842887548320973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600630670457183397761297 450473002842887548320973)
                ·
                  refine ⟨168927376066082830620365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450473002842887548320973 168927376066082830620365)
                  ·
                    rfl

theorem cell20_370108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_370108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370108 prefixEnd_370108 := by exact prefixLift 370108
  have htrace : WordTrace (prefixWord ++ tailWord_370108) baseStart_370108 baseEnd_370108 := by
    simpa [prefixWord, tailWord_370108, baseEnd_370108] using wordTrace_append hprefix tailTrace_370108
  have hstable : (prefixWord ++ tailWord_370108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370108).length < 2 ^ (prefixWord ++ tailWord_370108).sum := by decide
  have hdescent : baseEnd_370108 < baseStart_370108 := by decide
  rcases family_descends (prefixWord ++ tailWord_370108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370109 : List Nat := [1, 4, 1, 2, 2, 1, 9]
def baseStart_370109 : Nat := 118140960795 + 370109 * 2 ^ 59
def prefixEnd_370109 : Nat := 4983230072969 + 3 ^ 40 * 370109 * 2
def baseEnd_370109 : Nat := 18769759165925696843003

theorem tailTrace_370109 : CollatzResearch.WordTrace tailWord_370109 prefixEnd_370109 18769759165925696843003 := by
  unfold tailWord_370109
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498984216165777429937381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8999322810777184953291587 13498984216165777429937381)
  ·
    refine ⟨2531059540531083268113259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13498984216165777429937381 2531059540531083268113259)
    ·
      refine ⟨3796589310796624902169889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531059540531083268113259 3796589310796624902169889)
      ·
        refine ⟨2847441983097468676627417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3796589310796624902169889 2847441983097468676627417)
        ·
          refine ⟨2135581487323101507470563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2847441983097468676627417 2135581487323101507470563)
          ·
            refine ⟨3203372230984652261205845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135581487323101507470563 3203372230984652261205845)
            ·
              refine ⟨18769759165925696843003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3203372230984652261205845 18769759165925696843003)
              ·
                rfl

theorem cell20_370109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_370109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370109 prefixEnd_370109 := by exact prefixLift 370109
  have htrace : WordTrace (prefixWord ++ tailWord_370109) baseStart_370109 baseEnd_370109 := by
    simpa [prefixWord, tailWord_370109, baseEnd_370109] using wordTrace_append hprefix tailTrace_370109
  have hstable : (prefixWord ++ tailWord_370109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370109).length < 2 ^ (prefixWord ++ tailWord_370109).sum := by decide
  have hdescent : baseEnd_370109 < baseStart_370109 := by decide
  rcases family_descends (prefixWord ++ tailWord_370109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370119 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 2]
def baseStart_370119 : Nat := 118140960795 + 370119 * 2 ^ 59
def prefixEnd_370119 : Nat := 4983230072969 + 3 ^ 40 * 370119 * 2
def baseEnd_370119 : Nat := 168932396765815681253653

theorem tailTrace_370119 : CollatzResearch.WordTrace tailWord_370119 prefixEnd_370119 168932396765815681253653 := by
  unfold tailWord_370119
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499348946129549137801411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8999565964086366091867607 13499348946129549137801411)
  ·
    refine ⟨20249023419194323706702117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13499348946129549137801411 20249023419194323706702117)
    ·
      refine ⟨3796691891098935695006647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20249023419194323706702117 3796691891098935695006647)
      ·
        refine ⟨5695037836648403542509971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796691891098935695006647 5695037836648403542509971)
        ·
          refine ⟨8542556754972605313764957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695037836648403542509971 8542556754972605313764957)
          ·
            refine ⟨3203458783114726992661859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8542556754972605313764957 3203458783114726992661859)
            ·
              refine ⟨4805188174672090488992789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203458783114726992661859 4805188174672090488992789)
              ·
                refine ⟨225243195687754241671537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4805188174672090488992789 225243195687754241671537)
                ·
                  refine ⟨168932396765815681253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225243195687754241671537 168932396765815681253653)
                  ·
                    rfl

theorem cell20_370119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2].length) (baseStart_370119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370119 prefixEnd_370119 := by exact prefixLift 370119
  have htrace : WordTrace (prefixWord ++ tailWord_370119) baseStart_370119 baseEnd_370119 := by
    simpa [prefixWord, tailWord_370119, baseEnd_370119] using wordTrace_append hprefix tailTrace_370119
  have hstable : (prefixWord ++ tailWord_370119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370119).length < 2 ^ (prefixWord ++ tailWord_370119).sum := by decide
  have hdescent : baseEnd_370119 < baseStart_370119 := by decide
  rcases family_descends (prefixWord ++ tailWord_370119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370185 : List Nat := [1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_370185 : Nat := 118140960795 + 370185 * 2 ^ 59
def prefixEnd_370185 : Nat := 4983230072969 + 3 ^ 40 * 370185 * 2
def baseEnd_370185 : Nat := 56320840321404261684461

theorem tailTrace_370185 : CollatzResearch.WordTrace tailWord_370185 prefixEnd_370185 56320840321404261684461 := by
  unfold tailWord_370185
  simp only [CollatzResearch.WordTrace]
  refine ⟨13501756163890442409704009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9001170775926961606469339 13501756163890442409704009)
  ·
    refine ⟨10126317122917831807278007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13501756163890442409704009 10126317122917831807278007)
    ·
      refine ⟨15189475684376747710917011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10126317122917831807278007 15189475684376747710917011)
      ·
        refine ⟨22784213526565121566375517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189475684376747710917011 22784213526565121566375517)
        ·
          refine ⟨8544080072461920587390819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22784213526565121566375517 8544080072461920587390819)
          ·
            refine ⟨12816120108692880881086229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544080072461920587390819 12816120108692880881086229)
            ·
              refine ⟨600755630094978791300917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12816120108692880881086229 600755630094978791300917)
              ·
                refine ⟨56320840321404261684461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600755630094978791300917 56320840321404261684461)
                ·
                  rfl

theorem cell20_370185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_370185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370185 prefixEnd_370185 := by exact prefixLift 370185
  have htrace : WordTrace (prefixWord ++ tailWord_370185) baseStart_370185 baseEnd_370185 := by
    simpa [prefixWord, tailWord_370185, baseEnd_370185] using wordTrace_append hprefix tailTrace_370185
  have hstable : (prefixWord ++ tailWord_370185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370185).length < 2 ^ (prefixWord ++ tailWord_370185).sum := by decide
  have hdescent : baseEnd_370185 < baseStart_370185 := by decide
  rcases family_descends (prefixWord ++ tailWord_370185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370188 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_370188 : Nat := 118140960795 + 370188 * 2 ^ 59
def prefixEnd_370188 : Nat := 4983230072969 + 3 ^ 40 * 370188 * 2
def baseEnd_370188 : Nat := 168963890245958107953371

theorem tailTrace_370188 : CollatzResearch.WordTrace tailWord_370188 prefixEnd_370188 168963890245958107953371 := by
  unfold tailWord_370188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6750932791439786961031609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9001243721919715948042145 6750932791439786961031609)
  ·
    refine ⟨5063199593579840220773707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6750932791439786961031609 5063199593579840220773707)
    ·
      refine ⟨7594799390369760331160561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063199593579840220773707 7594799390369760331160561)
      ·
        refine ⟨5696099542777320248370421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7594799390369760331160561 5696099542777320248370421)
        ·
          refine ⟨534009332135373773284727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5696099542777320248370421 534009332135373773284727)
          ·
            refine ⟨801013998203060659927091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534009332135373773284727 801013998203060659927091)
            ·
              refine ⟨1201520997304590989890637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801013998203060659927091 1201520997304590989890637)
              ·
                refine ⟨450570373989221621208989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201520997304590989890637 450570373989221621208989)
                ·
                  refine ⟨168963890245958107953371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450570373989221621208989 168963890245958107953371)
                  ·
                    rfl

theorem cell20_370188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_370188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370188 prefixEnd_370188 := by exact prefixLift 370188
  have htrace : WordTrace (prefixWord ++ tailWord_370188) baseStart_370188 baseEnd_370188 := by
    simpa [prefixWord, tailWord_370188, baseEnd_370188] using wordTrace_append hprefix tailTrace_370188
  have hstable : (prefixWord ++ tailWord_370188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370188).length < 2 ^ (prefixWord ++ tailWord_370188).sum := by decide
  have hdescent : baseEnd_370188 < baseStart_370188 := by decide
  rcases family_descends (prefixWord ++ tailWord_370188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370229 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 2]
def baseStart_370229 : Nat := 118140960795 + 370229 * 2 ^ 59
def prefixEnd_370229 : Nat := 4983230072969 + 3 ^ 40 * 370229 * 2
def baseEnd_370229 : Nat := 168982603763144187586537

theorem tailTrace_370229 : CollatzResearch.WordTrace tailWord_370229 prefixEnd_370229 168982603763144187586537 := by
  unfold tailWord_370229
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503360975731037924305741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9002240650487358616203827 13503360975731037924305741)
  ·
    refine ⟨5063760365899139221614653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13503360975731037924305741 5063760365899139221614653)
    ·
      refine ⟨1898910137212177208105495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5063760365899139221614653 1898910137212177208105495)
      ·
        refine ⟨2848365205818265812158243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898910137212177208105495 2848365205818265812158243)
        ·
          refine ⟨4272547808727398718237365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848365205818265812158243 4272547808727398718237365)
          ·
            refine ⟨400551357068193629834753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4272547808727398718237365 400551357068193629834753)
            ·
              refine ⟨300413517801145222376065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400551357068193629834753 300413517801145222376065)
              ·
                refine ⟨225310138350858916782049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300413517801145222376065 225310138350858916782049)
                ·
                  refine ⟨168982603763144187586537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225310138350858916782049 168982603763144187586537)
                  ·
                    rfl

theorem cell20_370229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_370229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370229 prefixEnd_370229 := by exact prefixLift 370229
  have htrace : WordTrace (prefixWord ++ tailWord_370229) baseStart_370229 baseEnd_370229 := by
    simpa [prefixWord, tailWord_370229, baseEnd_370229] using wordTrace_append hprefix tailTrace_370229
  have hstable : (prefixWord ++ tailWord_370229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370229).length < 2 ^ (prefixWord ++ tailWord_370229).sum := by decide
  have hdescent : baseEnd_370229 < baseStart_370229 := by decide
  rcases family_descends (prefixWord ++ tailWord_370229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370312 : List Nat := [2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_370312 : Nat := 118140960795 + 370312 * 2 ^ 59
def prefixEnd_370312 : Nat := 4983230072969 + 3 ^ 40 * 370312 * 2
def baseEnd_370312 : Nat := 56340162408254929273177

theorem tailTrace_370312 : CollatzResearch.WordTrace tailWord_370312 prefixEnd_370312 56340162408254929273177 := by
  unfold tailWord_370312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753194117215171549788595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9004258822953562066384793 6753194117215171549788595)
  ·
    refine ⟨10129791175822757324682893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753194117215171549788595 10129791175822757324682893)
    ·
      refine ⟨3798671690933533996756085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10129791175822757324682893 3798671690933533996756085)
      ·
        refine ⟨356125471025018812195883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3798671690933533996756085 356125471025018812195883)
        ·
          refine ⟨534188206537528218293825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356125471025018812195883 534188206537528218293825)
          ·
            refine ⟨400641154903146163720369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534188206537528218293825 400641154903146163720369)
            ·
              refine ⟨300480866177359622790277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400641154903146163720369 300480866177359622790277)
              ·
                refine ⟨56340162408254929273177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300480866177359622790277 56340162408254929273177)
                ·
                  rfl

theorem cell20_370312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_370312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370312 prefixEnd_370312 := by exact prefixLift 370312
  have htrace : WordTrace (prefixWord ++ tailWord_370312) baseStart_370312 baseEnd_370312 := by
    simpa [prefixWord, tailWord_370312, baseEnd_370312] using wordTrace_append hprefix tailTrace_370312
  have hstable : (prefixWord ++ tailWord_370312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370312).length < 2 ^ (prefixWord ++ tailWord_370312).sum := by decide
  have hdescent : baseEnd_370312 < baseStart_370312 := by decide
  rcases family_descends (prefixWord ++ tailWord_370312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370322 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_370322 : Nat := 118140960795 + 370322 * 2 ^ 59
def prefixEnd_370322 : Nat := 4983230072969 + 3 ^ 40 * 370322 * 2
def baseEnd_370322 : Nat := 169025051497249197486157

theorem tailTrace_370322 : CollatzResearch.WordTrace tailWord_370322 prefixEnd_370322 169025051497249197486157 := by
  unfold tailWord_370322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376688241098528701860305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9004501976262743204960813 3376688241098528701860305)
  ·
    refine ⟨2532516180823896526395229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3376688241098528701860305 2532516180823896526395229)
    ·
      refine ⟨949693567808961197398211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2532516180823896526395229 949693567808961197398211)
      ·
        refine ⟨1424540351713441796097317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949693567808961197398211 1424540351713441796097317)
        ·
          refine ⟨267101315946270336768247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1424540351713441796097317 267101315946270336768247)
          ·
            refine ⟨400651973919405505152371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267101315946270336768247 400651973919405505152371)
            ·
              refine ⟨600977960879108257728557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400651973919405505152371 600977960879108257728557)
              ·
                refine ⟨225366735329665596648209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600977960879108257728557 225366735329665596648209)
                ·
                  refine ⟨169025051497249197486157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225366735329665596648209 169025051497249197486157)
                  ·
                    rfl

theorem cell20_370322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_370322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370322 prefixEnd_370322 := by exact prefixLift 370322
  have htrace : WordTrace (prefixWord ++ tailWord_370322) baseStart_370322 baseEnd_370322 := by
    simpa [prefixWord, tailWord_370322, baseEnd_370322] using wordTrace_append hprefix tailTrace_370322
  have hstable : (prefixWord ++ tailWord_370322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370322).length < 2 ^ (prefixWord ++ tailWord_370322).sum := by decide
  have hdescent : baseEnd_370322 < baseStart_370322 := by decide
  rcases family_descends (prefixWord ++ tailWord_370322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370337 : List Nat := [1, 2, 3, 3, 2, 1, 8]
def baseStart_370337 : Nat := 118140960795 + 370337 * 2 ^ 59
def prefixEnd_370337 : Nat := 4983230072969 + 3 ^ 40 * 370337 * 2
def baseEnd_370337 : Nat := 18781321989552867998455

theorem tailTrace_370337 : CollatzResearch.WordTrace tailWord_370337 prefixEnd_370337 18781321989552867998455 := by
  unfold tailWord_370337
  simp only [CollatzResearch.WordTrace]
  refine ⟨13507300059339772369237265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9004866706226514912824843 13507300059339772369237265)
  ·
    refine ⟨10130475044504829276927949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13507300059339772369237265 10130475044504829276927949)
    ·
      refine ⟨3798928141689310978847981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10130475044504829276927949 3798928141689310978847981)
      ·
        refine ⟨1424598053133491617067993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3798928141689310978847981 1424598053133491617067993)
        ·
          refine ⟨1068448539850118712800995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424598053133491617067993 1068448539850118712800995)
          ·
            refine ⟨1602672809775178069201493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068448539850118712800995 1602672809775178069201493)
            ·
              refine ⟨18781321989552867998455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1602672809775178069201493 18781321989552867998455)
              ·
                rfl

theorem cell20_370337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_370337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370337 prefixEnd_370337 := by exact prefixLift 370337
  have htrace : WordTrace (prefixWord ++ tailWord_370337) baseStart_370337 baseEnd_370337 := by
    simpa [prefixWord, tailWord_370337, baseEnd_370337] using wordTrace_append hprefix tailTrace_370337
  have hstable : (prefixWord ++ tailWord_370337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370337).length < 2 ^ (prefixWord ++ tailWord_370337).sum := by decide
  have hdescent : baseEnd_370337 < baseStart_370337 := by decide
  rcases family_descends (prefixWord ++ tailWord_370337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370399 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_370399 : Nat := 118140960795 + 370399 * 2 ^ 59
def prefixEnd_370399 : Nat := 4983230072969 + 3 ^ 40 * 370399 * 2
def baseEnd_370399 : Nat := 169060196395379151919175

theorem tailTrace_370399 : CollatzResearch.WordTrace tailWord_370399 prefixEnd_370399 169060196395379151919175 := by
  unfold tailWord_370399
  simp only [CollatzResearch.WordTrace]
  refine ⟨13509561385115156957994251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9006374256743437971996167 13509561385115156957994251)
  ·
    refine ⟨20264342077672735436991377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13509561385115156957994251 20264342077672735436991377)
    ·
      refine ⟨15198256558254551577743533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20264342077672735436991377 15198256558254551577743533)
      ·
        refine ⟨5699346209345456841653825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15198256558254551577743533 5699346209345456841653825)
        ·
          refine ⟨4274509657009092631240369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699346209345456841653825 4274509657009092631240369)
          ·
            refine ⟨3205882242756819473430277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274509657009092631240369 3205882242756819473430277)
            ·
              refine ⟨601102920516903651268177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3205882242756819473430277 601102920516903651268177)
              ·
                refine ⟨450827190387677738451133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601102920516903651268177 450827190387677738451133)
                ·
                  refine ⟨169060196395379151919175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450827190387677738451133 169060196395379151919175)
                  ·
                    rfl

theorem cell20_370399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_370399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370399 prefixEnd_370399 := by exact prefixLift 370399
  have htrace : WordTrace (prefixWord ++ tailWord_370399) baseStart_370399 baseEnd_370399 := by
    simpa [prefixWord, tailWord_370399, baseEnd_370399] using wordTrace_append hprefix tailTrace_370399
  have hstable : (prefixWord ++ tailWord_370399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370399).length < 2 ^ (prefixWord ++ tailWord_370399).sum := by decide
  have hdescent : baseEnd_370399 < baseStart_370399 := by decide
  rcases family_descends (prefixWord ++ tailWord_370399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370482 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_370482 : Nat := 118140960795 + 370482 * 2 ^ 59
def prefixEnd_370482 : Nat := 4983230072969 + 3 ^ 40 * 370482 * 2
def baseEnd_370482 : Nat := 169098079856999752152169

theorem tailTrace_370482 : CollatzResearch.WordTrace tailWord_370482 prefixEnd_370482 169098079856999752152169 := by
  unfold tailWord_370482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378147160953615533316425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9008392429209641422177133 3378147160953615533316425)
  ·
    refine ⟨2533610370715211649987319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3378147160953615533316425 2533610370715211649987319)
    ·
      refine ⟨3800415556072817474980979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2533610370715211649987319 3800415556072817474980979)
      ·
        refine ⟨5700623334109226212471469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800415556072817474980979 5700623334109226212471469)
        ·
          refine ⟨2137733750290959829676801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5700623334109226212471469 2137733750290959829676801)
          ·
            refine ⟨1603300312718219872257601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137733750290959829676801 1603300312718219872257601)
            ·
              refine ⟨1202475234538664904193201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603300312718219872257601 1202475234538664904193201)
              ·
                refine ⟨901856425903998678144901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202475234538664904193201 901856425903998678144901)
                ·
                  refine ⟨169098079856999752152169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 901856425903998678144901 169098079856999752152169)
                  ·
                    rfl

theorem cell20_370482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_370482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370482 prefixEnd_370482 := by exact prefixLift 370482
  have htrace : WordTrace (prefixWord ++ tailWord_370482) baseStart_370482 baseEnd_370482 := by
    simpa [prefixWord, tailWord_370482, baseEnd_370482] using wordTrace_append hprefix tailTrace_370482
  have hstable : (prefixWord ++ tailWord_370482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370482).length < 2 ^ (prefixWord ++ tailWord_370482).sum := by decide
  have hdescent : baseEnd_370482 < baseStart_370482 := by decide
  rcases family_descends (prefixWord ++ tailWord_370482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370485 : List Nat := [1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_370485 : Nat := 118140960795 + 370485 * 2 ^ 59
def prefixEnd_370485 : Nat := 4983230072969 + 3 ^ 40 * 370485 * 2
def baseEnd_370485 : Nat := 56366483046248358350719

theorem tailTrace_370485 : CollatzResearch.WordTrace tailWord_370485 prefixEnd_370485 56366483046248358350719 := by
  unfold tailWord_370485
  simp only [CollatzResearch.WordTrace]
  refine ⟨13512698062803593645624909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9008465375202395763749939 13512698062803593645624909)
  ·
    refine ⟨5067261773551347617109341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13512698062803593645624909 5067261773551347617109341)
    ·
      refine ⟨1900223165081755356416003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5067261773551347617109341 1900223165081755356416003)
      ·
        refine ⟨2850334747622633034624005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900223165081755356416003 2850334747622633034624005)
        ·
          refine ⟨534437765179243693992001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2850334747622633034624005 534437765179243693992001)
          ·
            refine ⟨400828323884432770494001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534437765179243693992001 400828323884432770494001)
            ·
              refine ⟨300621242913324577870501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400828323884432770494001 300621242913324577870501)
              ·
                refine ⟨56366483046248358350719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300621242913324577870501 56366483046248358350719)
                ·
                  rfl

theorem cell20_370485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_370485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370485 prefixEnd_370485 := by exact prefixLift 370485
  have htrace : WordTrace (prefixWord ++ tailWord_370485) baseStart_370485 baseEnd_370485 := by
    simpa [prefixWord, tailWord_370485, baseEnd_370485] using wordTrace_append hprefix tailTrace_370485
  have hstable : (prefixWord ++ tailWord_370485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370485).length < 2 ^ (prefixWord ++ tailWord_370485).sum := by decide
  have hdescent : baseEnd_370485 < baseStart_370485 := by decide
  rcases family_descends (prefixWord ++ tailWord_370485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370495 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 2]
def baseStart_370495 : Nat := 118140960795 + 370495 * 2 ^ 59
def prefixEnd_370495 : Nat := 4983230072969 + 3 ^ 40 * 370495 * 2
def baseEnd_370495 : Nat := 169104013411229484718783

theorem tailTrace_370495 : CollatzResearch.WordTrace tailWord_370495 prefixEnd_370495 169104013411229484718783 := by
  unfold tailWord_370495
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513062792767365353488939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9008708528511576902325959 13513062792767365353488939)
  ·
    refine ⟨20269594189151048030233409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13513062792767365353488939 20269594189151048030233409)
    ·
      refine ⟨15202195641863286022675057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20269594189151048030233409 15202195641863286022675057)
      ·
        refine ⟨11401646731397464517006293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15202195641863286022675057 11401646731397464517006293)
        ·
          refine ⟨267226095267128074617335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11401646731397464517006293 267226095267128074617335)
          ·
            refine ⟨400839142900692111926003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267226095267128074617335 400839142900692111926003)
            ·
              refine ⟨601258714351038167889005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400839142900692111926003 601258714351038167889005)
              ·
                refine ⟨225472017881639312958377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601258714351038167889005 225472017881639312958377)
                ·
                  refine ⟨169104013411229484718783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225472017881639312958377 169104013411229484718783)
                  ·
                    rfl

theorem cell20_370495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2].length) (baseStart_370495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370495 prefixEnd_370495 := by exact prefixLift 370495
  have htrace : WordTrace (prefixWord ++ tailWord_370495) baseStart_370495 baseEnd_370495 := by
    simpa [prefixWord, tailWord_370495, baseEnd_370495] using wordTrace_append hprefix tailTrace_370495
  have hstable : (prefixWord ++ tailWord_370495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370495).length < 2 ^ (prefixWord ++ tailWord_370495).sum := by decide
  have hdescent : baseEnd_370495 < baseStart_370495 := by decide
  rcases family_descends (prefixWord ++ tailWord_370495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370499 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 2]
def baseStart_370499 : Nat := 118140960795 + 370499 * 2 ^ 59
def prefixEnd_370499 : Nat := 4983230072969 + 3 ^ 40 * 370499 * 2
def baseEnd_370499 : Nat := 169105839120223248585433

theorem tailTrace_370499 : CollatzResearch.WordTrace tailWord_370499 prefixEnd_370499 169105839120223248585433 := by
  unfold tailWord_370499
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513208684752874036634551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9008805789835249357756367 13513208684752874036634551)
  ·
    refine ⟨20269813027129311054951827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13513208684752874036634551 20269813027129311054951827)
    ·
      refine ⟨30404719540693966582427741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20269813027129311054951827 30404719540693966582427741)
      ·
        refine ⟨11401769827760237468410403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30404719540693966582427741 11401769827760237468410403)
        ·
          refine ⟨17102654741640356202615605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11401769827760237468410403 17102654741640356202615605)
          ·
            refine ⟨1603373882028783393995213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17102654741640356202615605 1603373882028783393995213)
            ·
              refine ⟨601265205760793772748205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1603373882028783393995213 601265205760793772748205)
              ·
                refine ⟨225474452160297664780577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601265205760793772748205 225474452160297664780577)
                ·
                  refine ⟨169105839120223248585433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225474452160297664780577 169105839120223248585433)
                  ·
                    rfl

theorem cell20_370499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2].length) (baseStart_370499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370499 prefixEnd_370499 := by exact prefixLift 370499
  have htrace : WordTrace (prefixWord ++ tailWord_370499) baseStart_370499 baseEnd_370499 := by
    simpa [prefixWord, tailWord_370499, baseEnd_370499] using wordTrace_append hprefix tailTrace_370499
  have hstable : (prefixWord ++ tailWord_370499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370499).length < 2 ^ (prefixWord ++ tailWord_370499).sum := by decide
  have hdescent : baseEnd_370499 < baseStart_370499 := by decide
  rcases family_descends (prefixWord ++ tailWord_370499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370503 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_370503 : Nat := 118140960795 + 370503 * 2 ^ 59
def prefixEnd_370503 : Nat := 4983230072969 + 3 ^ 40 * 370503 * 2
def baseEnd_370503 : Nat := 169107664829217012452083

theorem tailTrace_370503 : CollatzResearch.WordTrace tailWord_370503 prefixEnd_370503 169107664829217012452083 := by
  unfold tailWord_370503
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513354576738382719780163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9008903051158921813186775 13513354576738382719780163)
  ·
    refine ⟨20270031865107574079670245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13513354576738382719780163 20270031865107574079670245)
    ·
      refine ⟨3800630974707670139938171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20270031865107574079670245 3800630974707670139938171)
      ·
        refine ⟨5700946462061505209907257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800630974707670139938171 5700946462061505209907257)
        ·
          refine ⟨4275709846546128907430443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5700946462061505209907257 4275709846546128907430443)
          ·
            refine ⟨6413564769819193361145665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275709846546128907430443 6413564769819193361145665)
            ·
              refine ⟨4810173577364395020859249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6413564769819193361145665 4810173577364395020859249)
              ·
                refine ⟨3607630183023296265644437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810173577364395020859249 3607630183023296265644437)
                ·
                  refine ⟨169107664829217012452083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3607630183023296265644437 169107664829217012452083)
                  ·
                    rfl

theorem cell20_370503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_370503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370503 prefixEnd_370503 := by exact prefixLift 370503
  have htrace : WordTrace (prefixWord ++ tailWord_370503) baseStart_370503 baseEnd_370503 := by
    simpa [prefixWord, tailWord_370503, baseEnd_370503] using wordTrace_append hprefix tailTrace_370503
  have hstable : (prefixWord ++ tailWord_370503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370503).length < 2 ^ (prefixWord ++ tailWord_370503).sum := by decide
  have hdescent : baseEnd_370503 < baseStart_370503 := by decide
  rcases family_descends (prefixWord ++ tailWord_370503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370527 : List Nat := [1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_370527 : Nat := 118140960795 + 370527 * 2 ^ 59
def prefixEnd_370527 : Nat := 4983230072969 + 3 ^ 40 * 370527 * 2
def baseEnd_370527 : Nat := 56372873027726531883995

theorem tailTrace_370527 : CollatzResearch.WordTrace tailWord_370527 prefixEnd_370527 56372873027726531883995 := by
  unfold tailWord_370527
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514229928651434818653835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9009486619100956545769223 13514229928651434818653835)
  ·
    refine ⟨20271344892977152227980753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13514229928651434818653835 20271344892977152227980753)
    ·
      refine ⟨15203508669732864170985565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20271344892977152227980753 15203508669732864170985565)
      ·
        refine ⟨5701315751149824064119587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15203508669732864170985565 5701315751149824064119587)
        ·
          refine ⟨8551973626724736096179381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701315751149824064119587 8551973626724736096179381)
          ·
            refine ⟨801747527505444009016817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8551973626724736096179381 801747527505444009016817)
            ·
              refine ⟨601310645629083006762613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801747527505444009016817 601310645629083006762613)
              ·
                refine ⟨56372873027726531883995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 601310645629083006762613 56372873027726531883995)
                ·
                  rfl

theorem cell20_370527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_370527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370527 prefixEnd_370527 := by exact prefixLift 370527
  have htrace : WordTrace (prefixWord ++ tailWord_370527) baseStart_370527 baseEnd_370527 := by
    simpa [prefixWord, tailWord_370527, baseEnd_370527] using wordTrace_append hprefix tailTrace_370527
  have hstable : (prefixWord ++ tailWord_370527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370527).length < 2 ^ (prefixWord ++ tailWord_370527).sum := by decide
  have hdescent : baseEnd_370527 < baseStart_370527 := by decide
  rcases family_descends (prefixWord ++ tailWord_370527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370530 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_370530 : Nat := 118140960795 + 370530 * 2 ^ 59
def prefixEnd_370530 : Nat := 4983230072969 + 3 ^ 40 * 370530 * 2
def baseEnd_370530 : Nat := 169119988364924918551973

theorem tailTrace_370530 : CollatzResearch.WordTrace tailWord_370530 prefixEnd_370530 169119988364924918551973 := by
  unfold tailWord_370530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378584836910141582753261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9009559565093710887342029 3378584836910141582753261)
  ·
    refine ⟨1266969313841303093532473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3378584836910141582753261 1266969313841303093532473)
    ·
      refine ⟨950226985380977320149355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1266969313841303093532473 950226985380977320149355)
      ·
        refine ⟨1425340478071465980224033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950226985380977320149355 1425340478071465980224033)
        ·
          refine ⟨1069005358553599485168025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425340478071465980224033 1069005358553599485168025)
          ·
            refine ⟨801754018915199613876019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069005358553599485168025 801754018915199613876019)
            ·
              refine ⟨1202631028372799420814029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801754018915199613876019 1202631028372799420814029)
              ·
                refine ⟨450986635639799782805261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202631028372799420814029 450986635639799782805261)
                ·
                  refine ⟨169119988364924918551973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450986635639799782805261 169119988364924918551973)
                  ·
                    rfl

theorem cell20_370530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_370530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370530 prefixEnd_370530 := by exact prefixLift 370530
  have htrace : WordTrace (prefixWord ++ tailWord_370530) baseStart_370530 baseEnd_370530 := by
    simpa [prefixWord, tailWord_370530, baseEnd_370530] using wordTrace_append hprefix tailTrace_370530
  have hstable : (prefixWord ++ tailWord_370530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370530).length < 2 ^ (prefixWord ++ tailWord_370530).sum := by decide
  have hdescent : baseEnd_370530 < baseStart_370530 := by decide
  rcases family_descends (prefixWord ++ tailWord_370530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370568 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_370568 : Nat := 118140960795 + 370568 * 2 ^ 59
def prefixEnd_370568 : Nat := 4983230072969 + 3 ^ 40 * 370568 * 2
def baseEnd_370568 : Nat := 169137332600365675285151

theorem tailTrace_370568 : CollatzResearch.WordTrace tailWord_370568 prefixEnd_370568 169137332600365675285151 := by
  unfold tailWord_370568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757862660751449410448179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9010483547668599213930905 6757862660751449410448179)
  ·
    refine ⟨10136793991127174115672269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6757862660751449410448179 10136793991127174115672269)
    ·
      refine ⟨3801297746672690293377101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10136793991127174115672269 3801297746672690293377101)
      ·
        refine ⟨1425486655002258860016413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3801297746672690293377101 1425486655002258860016413)
        ·
          refine ⟨534557495625847072506155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1425486655002258860016413 534557495625847072506155)
          ·
            refine ⟨801836243438770608759233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534557495625847072506155 801836243438770608759233)
            ·
              refine ⟨601377182579077956569425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801836243438770608759233 601377182579077956569425)
              ·
                refine ⟨451032886934308467427069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601377182579077956569425 451032886934308467427069)
                ·
                  refine ⟨169137332600365675285151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451032886934308467427069 169137332600365675285151)
                  ·
                    rfl

theorem cell20_370568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_370568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370568 prefixEnd_370568 := by exact prefixLift 370568
  have htrace : WordTrace (prefixWord ++ tailWord_370568) baseStart_370568 baseEnd_370568 := by
    simpa [prefixWord, tailWord_370568, baseEnd_370568] using wordTrace_append hprefix tailTrace_370568
  have hstable : (prefixWord ++ tailWord_370568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370568).length < 2 ^ (prefixWord ++ tailWord_370568).sum := by decide
  have hdescent : baseEnd_370568 < baseStart_370568 := by decide
  rcases family_descends (prefixWord ++ tailWord_370568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370589 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_370589 : Nat := 118140960795 + 370589 * 2 ^ 59
def prefixEnd_370589 : Nat := 4983230072969 + 3 ^ 40 * 370589 * 2
def baseEnd_370589 : Nat := 169146917572582935585065

theorem tailTrace_370589 : CollatzResearch.WordTrace tailWord_370589 prefixEnd_370589 169146917572582935585065 := by
  unfold tailWord_370589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13516491254426819407410821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9010994169617879604940547 13516491254426819407410821)
  ·
    refine ⟨2534342110205028638889529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13516491254426819407410821 2534342110205028638889529)
    ·
      refine ⟨1900756582653771479167147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2534342110205028638889529 1900756582653771479167147)
      ·
        refine ⟨2851134873980657218750721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900756582653771479167147 2851134873980657218750721)
        ·
          refine ⟨2138351155485492914063041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851134873980657218750721 2138351155485492914063041)
          ·
            refine ⟨1603763366614119685547281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138351155485492914063041 1603763366614119685547281)
            ·
              refine ⟨1202822524960589764160461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603763366614119685547281 1202822524960589764160461)
              ·
                refine ⟨451058446860221161560173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202822524960589764160461 451058446860221161560173)
                ·
                  refine ⟨169146917572582935585065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451058446860221161560173 169146917572582935585065)
                  ·
                    rfl

theorem cell20_370589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_370589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370589 prefixEnd_370589 := by exact prefixLift 370589
  have htrace : WordTrace (prefixWord ++ tailWord_370589) baseStart_370589 baseEnd_370589 := by
    simpa [prefixWord, tailWord_370589, baseEnd_370589] using wordTrace_append hprefix tailTrace_370589
  have hstable : (prefixWord ++ tailWord_370589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370589).length < 2 ^ (prefixWord ++ tailWord_370589).sum := by decide
  have hdescent : baseEnd_370589 < baseStart_370589 := by decide
  rcases family_descends (prefixWord ++ tailWord_370589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370596 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_370596 : Nat := 118140960795 + 370596 * 2 ^ 59
def prefixEnd_370596 : Nat := 4983230072969 + 3 ^ 40 * 370596 * 2
def baseEnd_370596 : Nat := 169150112563322022351703

theorem tailTrace_370596 : CollatzResearch.WordTrace tailWord_370596 prefixEnd_370596 169150112563322022351703 := by
  unfold tailWord_370596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758373282700729801457821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9011164376934306401943761 6758373282700729801457821)
  ·
    refine ⟨2534389981012773675546683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6758373282700729801457821 2534389981012773675546683)
    ·
      refine ⟨3801584971519160513320025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534389981012773675546683 3801584971519160513320025)
      ·
        refine ⟨2851188728639370384990019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801584971519160513320025 2851188728639370384990019)
        ·
          refine ⟨4276783092959055577485029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851188728639370384990019 4276783092959055577485029)
          ·
            refine ⟨801896829929822920778443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4276783092959055577485029 801896829929822920778443)
            ·
              refine ⟨1202845244894734381167665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801896829929822920778443 1202845244894734381167665)
              ·
                refine ⟨902133933671050785875749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202845244894734381167665 902133933671050785875749)
                ·
                  refine ⟨169150112563322022351703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902133933671050785875749 169150112563322022351703)
                  ·
                    rfl

theorem cell20_370596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_370596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370596 prefixEnd_370596 := by exact prefixLift 370596
  have htrace : WordTrace (prefixWord ++ tailWord_370596) baseStart_370596 baseEnd_370596 := by
    simpa [prefixWord, tailWord_370596, baseEnd_370596] using wordTrace_append hprefix tailTrace_370596
  have hstable : (prefixWord ++ tailWord_370596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370596).length < 2 ^ (prefixWord ++ tailWord_370596).sum := by decide
  have hdescent : baseEnd_370596 < baseStart_370596 := by decide
  rcases family_descends (prefixWord ++ tailWord_370596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370613 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 2]
def baseStart_370613 : Nat := 118140960795 + 370613 * 2 ^ 59
def prefixEnd_370613 : Nat := 4983230072969 + 3 ^ 40 * 370613 * 2
def baseEnd_370613 : Nat := 169157871826545518784967

theorem tailTrace_370613 : CollatzResearch.WordTrace tailWord_370613 prefixEnd_370613 169157871826545518784967 := by
  unfold tailWord_370613
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517366606339871506284493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9011577737559914337522995 13517366606339871506284493)
  ·
    refine ⟨5069012477377451814856685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13517366606339871506284493 5069012477377451814856685)
    ·
      refine ⟨1900879679016544430571257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5069012477377451814856685 1900879679016544430571257)
      ·
        refine ⟨1425659759262408322928443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900879679016544430571257 1425659759262408322928443)
        ·
          refine ⟨2138489638893612484392665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425659759262408322928443 2138489638893612484392665)
          ·
            refine ⟨1603867229170209363294499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138489638893612484392665 1603867229170209363294499)
            ·
              refine ⟨2405800843755314044941749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603867229170209363294499 2405800843755314044941749)
              ·
                refine ⟨225543829102060691713289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2405800843755314044941749 225543829102060691713289)
                ·
                  refine ⟨169157871826545518784967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225543829102060691713289 169157871826545518784967)
                  ·
                    rfl

theorem cell20_370613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_370613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370613 prefixEnd_370613 := by exact prefixLift 370613
  have htrace : WordTrace (prefixWord ++ tailWord_370613) baseStart_370613 baseEnd_370613 := by
    simpa [prefixWord, tailWord_370613, baseEnd_370613] using wordTrace_append hprefix tailTrace_370613
  have hstable : (prefixWord ++ tailWord_370613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370613).length < 2 ^ (prefixWord ++ tailWord_370613).sum := by decide
  have hdescent : baseEnd_370613 < baseStart_370613 := by decide
  rcases family_descends (prefixWord ++ tailWord_370613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370617 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_370617 : Nat := 118140960795 + 370617 * 2 ^ 59
def prefixEnd_370617 : Nat := 4983230072969 + 3 ^ 40 * 370617 * 2
def baseEnd_370617 : Nat := 169159697535539282651617

theorem tailTrace_370617 : CollatzResearch.WordTrace tailWord_370617 prefixEnd_370617 169159697535539282651617 := by
  unfold tailWord_370617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517512498325380189430105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9011674998883586792953403 13517512498325380189430105)
  ·
    refine ⟨10138134373744035142072579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13517512498325380189430105 10138134373744035142072579)
    ·
      refine ⟨15207201560616052713108869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10138134373744035142072579 15207201560616052713108869)
      ·
        refine ⟨2851350292615509883707913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15207201560616052713108869 2851350292615509883707913)
        ·
          refine ⟨2138512719461632412780935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851350292615509883707913 2138512719461632412780935)
          ·
            refine ⟨3207769079192448619171403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138512719461632412780935 3207769079192448619171403)
            ·
              refine ⟨4811653618788672928757105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207769079192448619171403 4811653618788672928757105)
              ·
                refine ⟨3608740214091504696567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811653618788672928757105 3608740214091504696567829)
                ·
                  refine ⟨169159697535539282651617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3608740214091504696567829 169159697535539282651617)
                  ·
                    rfl

theorem cell20_370617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_370617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370617 prefixEnd_370617 := by exact prefixLift 370617
  have htrace : WordTrace (prefixWord ++ tailWord_370617) baseStart_370617 baseEnd_370617 := by
    simpa [prefixWord, tailWord_370617, baseEnd_370617] using wordTrace_append hprefix tailTrace_370617
  have hstable : (prefixWord ++ tailWord_370617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370617).length < 2 ^ (prefixWord ++ tailWord_370617).sum := by decide
  have hdescent : baseEnd_370617 < baseStart_370617 := by decide
  rcases family_descends (prefixWord ++ tailWord_370617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370620 : List Nat := [2, 2, 2, 5, 1, 1, 7]
def baseStart_370620 : Nat := 118140960795 + 370620 * 2 ^ 59
def prefixEnd_370620 : Nat := 4983230072969 + 3 ^ 40 * 370620 * 2
def baseEnd_370620 : Nat := 18795674090809400616845

theorem tailTrace_370620 : CollatzResearch.WordTrace tailWord_370620 prefixEnd_370620 18795674090809400616845 := by
  unfold tailWord_370620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758810958657255850894657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9011747944876341134526209 6758810958657255850894657)
  ·
    refine ⟨5069108218992941888170993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6758810958657255850894657 5069108218992941888170993)
    ·
      refine ⟨3801831164244706416128245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069108218992941888170993 3801831164244706416128245)
      ·
        refine ⟨356421671647941226512023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3801831164244706416128245 356421671647941226512023)
        ·
          refine ⟨534632507471911839768035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356421671647941226512023 534632507471911839768035)
          ·
            refine ⟨801948761207867759652053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534632507471911839768035 801948761207867759652053)
            ·
              refine ⟨18795674090809400616845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 801948761207867759652053 18795674090809400616845)
              ·
                rfl

theorem cell20_370620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_370620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370620 prefixEnd_370620 := by exact prefixLift 370620
  have htrace : WordTrace (prefixWord ++ tailWord_370620) baseStart_370620 baseEnd_370620 := by
    simpa [prefixWord, tailWord_370620, baseEnd_370620] using wordTrace_append hprefix tailTrace_370620
  have hstable : (prefixWord ++ tailWord_370620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370620).length < 2 ^ (prefixWord ++ tailWord_370620).sum := by decide
  have hdescent : baseEnd_370620 < baseStart_370620 := by decide
  rcases family_descends (prefixWord ++ tailWord_370620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370624 : List Nat := [2, 1, 1, 2, 3, 2, 9]
def baseStart_370624 : Nat := 118140960795 + 370624 * 2 ^ 59
def prefixEnd_370624 : Nat := 4983230072969 + 3 ^ 40 * 370624 * 2
def baseEnd_370624 : Nat := 18795876947364263268695

theorem tailTrace_370624 : CollatzResearch.WordTrace tailWord_370624 prefixEnd_370624 18795876947364263268695 := by
  unfold tailWord_370624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758883904650010192467463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9011845206200013589956617 6758883904650010192467463)
  ·
    refine ⟨10138325856975015288701195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6758883904650010192467463 10138325856975015288701195)
    ·
      refine ⟨15207488785462522933051793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10138325856975015288701195 15207488785462522933051793)
      ·
        refine ⟨11405616589096892199788845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15207488785462522933051793 11405616589096892199788845)
        ·
          refine ⟨4277106220911334574920817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11405616589096892199788845 4277106220911334574920817)
          ·
            refine ⟨3207829665683500931190613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4277106220911334574920817 3207829665683500931190613)
            ·
              refine ⟨18795876947364263268695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3207829665683500931190613 18795876947364263268695)
              ·
                rfl

theorem cell20_370624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_370624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370624 prefixEnd_370624 := by exact prefixLift 370624
  have htrace : WordTrace (prefixWord ++ tailWord_370624) baseStart_370624 baseEnd_370624 := by
    simpa [prefixWord, tailWord_370624, baseEnd_370624] using wordTrace_append hprefix tailTrace_370624
  have hstable : (prefixWord ++ tailWord_370624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370624).length < 2 ^ (prefixWord ++ tailWord_370624).sum := by decide
  have hdescent : baseEnd_370624 < baseStart_370624 := by decide
  rcases family_descends (prefixWord ++ tailWord_370624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370644 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_370644 : Nat := 118140960795 + 370644 * 2 ^ 59
def prefixEnd_370644 : Nat := 4983230072969 + 3 ^ 40 * 370644 * 2
def baseEnd_370644 : Nat := 169172021071247188751507

theorem tailTrace_370644 : CollatzResearch.WordTrace tailWord_370644 prefixEnd_370644 169172021071247188751507 := by
  unfold tailWord_370644
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759248634613781900331493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9012331512818375867108657 6759248634613781900331493)
  ·
    refine ⟨1267359118990084106312155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6759248634613781900331493 1267359118990084106312155)
    ·
      refine ⟨1901038678485126159468233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267359118990084106312155 1901038678485126159468233)
      ·
        refine ⟨1425779008863844619601175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901038678485126159468233 1425779008863844619601175)
        ·
          refine ⟨2138668513295766929401763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425779008863844619601175 2138668513295766929401763)
          ·
            refine ⟨3208002769943650394102645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138668513295766929401763 3208002769943650394102645)
            ·
              refine ⟨300750259682217224447123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3208002769943650394102645 300750259682217224447123)
              ·
                refine ⟨451125389523325836670685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300750259682217224447123 451125389523325836670685)
                ·
                  refine ⟨169172021071247188751507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451125389523325836670685 169172021071247188751507)
                  ·
                    rfl

theorem cell20_370644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_370644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370644 prefixEnd_370644 := by exact prefixLift 370644
  have htrace : WordTrace (prefixWord ++ tailWord_370644) baseStart_370644 baseEnd_370644 := by
    simpa [prefixWord, tailWord_370644, baseEnd_370644] using wordTrace_append hprefix tailTrace_370644
  have hstable : (prefixWord ++ tailWord_370644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370644).length < 2 ^ (prefixWord ++ tailWord_370644).sum := by decide
  have hdescent : baseEnd_370644 < baseStart_370644 := by decide
  rcases family_descends (prefixWord ++ tailWord_370644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370717 : List Nat := [1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_370717 : Nat := 118140960795 + 370717 * 2 ^ 59
def prefixEnd_370717 : Nat := 4983230072969 + 3 ^ 40 * 370717 * 2
def baseEnd_370717 : Nat := 56401780086794459772625

theorem tailTrace_370717 : CollatzResearch.WordTrace tailWord_370717 prefixEnd_370717 56401780086794459772625 := by
  unfold tailWord_370717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13521159797963097268070405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9014106531975398178713603 13521159797963097268070405)
  ·
    refine ⟨2535217462118080737763201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13521159797963097268070405 2535217462118080737763201)
    ·
      refine ⟨1901413096588560553322401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2535217462118080737763201 1901413096588560553322401)
      ·
        refine ⟨1426059822441420414991801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901413096588560553322401 1426059822441420414991801)
        ·
          refine ⟨1069544866831065311243851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426059822441420414991801 1069544866831065311243851)
          ·
            refine ⟨1604317300246597966865777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069544866831065311243851 1604317300246597966865777)
            ·
              refine ⟨1203237975184948475149333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604317300246597966865777 1203237975184948475149333)
              ·
                refine ⟨56401780086794459772625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1203237975184948475149333 56401780086794459772625)
                ·
                  rfl

theorem cell20_370717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_370717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370717 prefixEnd_370717 := by exact prefixLift 370717
  have htrace : WordTrace (prefixWord ++ tailWord_370717) baseStart_370717 baseEnd_370717 := by
    simpa [prefixWord, tailWord_370717, baseEnd_370717] using wordTrace_append hprefix tailTrace_370717
  have hstable : (prefixWord ++ tailWord_370717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370717).length < 2 ^ (prefixWord ++ tailWord_370717).sum := by decide
  have hdescent : baseEnd_370717 < baseStart_370717 := by decide
  rcases family_descends (prefixWord ++ tailWord_370717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370738 : List Nat := [3, 2, 1, 1, 2, 11]
def baseStart_370738 : Nat := 118140960795 + 370738 * 2 ^ 59
def prefixEnd_370738 : Nat := 4983230072969 + 3 ^ 40 * 370738 * 2
def baseEnd_370738 : Nat := 6267219453059282948807

theorem tailTrace_370738 : CollatzResearch.WordTrace tailWord_370738 prefixEnd_370738 6267219453059282948807 := by
  unfold tailWord_370738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380481432721754463646217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9014617153924678569723245 3380481432721754463646217)
  ·
    refine ⟨2535361074541315847734663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3380481432721754463646217 2535361074541315847734663)
    ·
      refine ⟨3803041611811973771601995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535361074541315847734663 3803041611811973771601995)
      ·
        refine ⟨5704562417717960657402993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803041611811973771601995 5704562417717960657402993)
        ·
          refine ⟨4278421813288470493052245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704562417717960657402993 4278421813288470493052245)
          ·
            refine ⟨6267219453059282948807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4278421813288470493052245 6267219453059282948807)
            ·
              rfl

theorem cell20_370738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 11].length) (baseStart_370738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370738 prefixEnd_370738 := by exact prefixLift 370738
  have htrace : WordTrace (prefixWord ++ tailWord_370738) baseStart_370738 baseEnd_370738 := by
    simpa [prefixWord, tailWord_370738, baseEnd_370738] using wordTrace_append hprefix tailTrace_370738
  have hstable : (prefixWord ++ tailWord_370738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370738).length < 2 ^ (prefixWord ++ tailWord_370738).sum := by decide
  have hdescent : baseEnd_370738 < baseStart_370738 := by decide
  rcases family_descends (prefixWord ++ tailWord_370738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370740 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_370740 : Nat := 118140960795 + 370740 * 2 ^ 59
def prefixEnd_370740 : Nat := 4983230072969 + 3 ^ 40 * 370740 * 2
def baseEnd_370740 : Nat := 169215838087097521551115

theorem tailTrace_370740 : CollatzResearch.WordTrace tailWord_370740 prefixEnd_370740 169215838087097521551115 := by
  unfold tailWord_370740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760999338439886098078837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9014665784586514797438449 6760999338439886098078837)
  ·
    refine ⟨633843687978739321694891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6760999338439886098078837 633843687978739321694891)
    ·
      refine ⟨950765531968108982542337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633843687978739321694891 950765531968108982542337)
      ·
        refine ⟨713074148976081736906753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950765531968108982542337 713074148976081736906753)
        ·
          refine ⟨534805611732061302680065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713074148976081736906753 534805611732061302680065)
          ·
            refine ⟨401104208799045977010049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534805611732061302680065 401104208799045977010049)
            ·
              refine ⟨300828156599284482757537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401104208799045977010049 300828156599284482757537)
              ·
                refine ⟨225621117449463362068153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300828156599284482757537 225621117449463362068153)
                ·
                  refine ⟨169215838087097521551115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225621117449463362068153 169215838087097521551115)
                  ·
                    rfl

theorem cell20_370740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_370740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370740 prefixEnd_370740 := by exact prefixLift 370740
  have htrace : WordTrace (prefixWord ++ tailWord_370740) baseStart_370740 baseEnd_370740 := by
    simpa [prefixWord, tailWord_370740, baseEnd_370740] using wordTrace_append hprefix tailTrace_370740
  have hstable : (prefixWord ++ tailWord_370740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370740).length < 2 ^ (prefixWord ++ tailWord_370740).sum := by decide
  have hdescent : baseEnd_370740 < baseStart_370740 := by decide
  rcases family_descends (prefixWord ++ tailWord_370740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370758 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_370758 : Nat := 118140960795 + 370758 * 2 ^ 59
def prefixEnd_370758 : Nat := 4983230072969 + 3 ^ 40 * 370758 * 2
def baseEnd_370758 : Nat := 169224053777569458951041

theorem tailTrace_370758 : CollatzResearch.WordTrace tailWord_370758 prefixEnd_370758 169224053777569458951041 := by
  unfold tailWord_370758
  simp only [CollatzResearch.WordTrace]
  refine ⟨422582974712955039697279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9015103460543040846875285 422582974712955039697279)
  ·
    refine ⟨633874462069432559545919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422582974712955039697279 633874462069432559545919)
    ·
      refine ⟨950811693104148839318879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633874462069432559545919 950811693104148839318879)
      ·
        refine ⟨1426217539656223258978319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950811693104148839318879 1426217539656223258978319)
        ·
          refine ⟨2139326309484334888467479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426217539656223258978319 2139326309484334888467479)
          ·
            refine ⟨3208989464226502332701219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139326309484334888467479 3208989464226502332701219)
            ·
              refine ⟨4813484196339753499051829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208989464226502332701219 4813484196339753499051829)
              ·
                refine ⟨451264143406851890536109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4813484196339753499051829 451264143406851890536109)
                ·
                  refine ⟨169224053777569458951041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451264143406851890536109 169224053777569458951041)
                  ·
                    rfl

theorem cell20_370758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_370758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370758 prefixEnd_370758 := by exact prefixLift 370758
  have htrace : WordTrace (prefixWord ++ tailWord_370758) baseStart_370758 baseEnd_370758 := by
    simpa [prefixWord, tailWord_370758, baseEnd_370758] using wordTrace_append hprefix tailTrace_370758
  have hstable : (prefixWord ++ tailWord_370758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370758).length < 2 ^ (prefixWord ++ tailWord_370758).sum := by decide
  have hdescent : baseEnd_370758 < baseStart_370758 := by decide
  rcases family_descends (prefixWord ++ tailWord_370758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370800 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_370800 : Nat := 118140960795 + 370800 * 2 ^ 59
def prefixEnd_370800 : Nat := 4983230072969 + 3 ^ 40 * 370800 * 2
def baseEnd_370800 : Nat := 169243223722003979550869

theorem tailTrace_370800 : CollatzResearch.WordTrace tailWord_370800 prefixEnd_370800 169243223722003979550869 := by
  unfold tailWord_370800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762093528331201221670927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9016124704441601628894569 6762093528331201221670927)
  ·
    refine ⟨10143140292496801832506391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6762093528331201221670927 10143140292496801832506391)
    ·
      refine ⟨15214710438745202748759587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143140292496801832506391 15214710438745202748759587)
      ·
        refine ⟨22822065658117804123139381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15214710438745202748759587 22822065658117804123139381)
        ·
          refine ⟨2139568655448544136544317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22822065658117804123139381 2139568655448544136544317)
          ·
            refine ⟨802338245793204051204119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2139568655448544136544317 802338245793204051204119)
            ·
              refine ⟨1203507368689806076806179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802338245793204051204119 1203507368689806076806179)
              ·
                refine ⟨1805261053034709115209269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203507368689806076806179 1805261053034709115209269)
                ·
                  refine ⟨169243223722003979550869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805261053034709115209269 169243223722003979550869)
                  ·
                    rfl

theorem cell20_370800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_370800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370800 prefixEnd_370800 := by exact prefixLift 370800
  have htrace : WordTrace (prefixWord ++ tailWord_370800) baseStart_370800 baseEnd_370800 := by
    simpa [prefixWord, tailWord_370800, baseEnd_370800] using wordTrace_append hprefix tailTrace_370800
  have hstable : (prefixWord ++ tailWord_370800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370800).length < 2 ^ (prefixWord ++ tailWord_370800).sum := by decide
  have hdescent : baseEnd_370800 < baseStart_370800 := by decide
  rcases family_descends (prefixWord ++ tailWord_370800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370807 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_370807 : Nat := 118140960795 + 370807 * 2 ^ 59
def prefixEnd_370807 : Nat := 4983230072969 + 3 ^ 40 * 370807 * 2
def baseEnd_370807 : Nat := 169246418712743066317507

theorem tailTrace_370807 : CollatzResearch.WordTrace tailWord_370807 prefixEnd_370807 169246418712743066317507 := by
  unfold tailWord_370807
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524442367637042638846675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9016294911758028425897783 13524442367637042638846675)
  ·
    refine ⟨20286663551455563958270013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13524442367637042638846675 20286663551455563958270013)
    ·
      refine ⟨7607498831795836484351255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20286663551455563958270013 7607498831795836484351255)
      ·
        refine ⟨11411248247693754726526883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607498831795836484351255 11411248247693754726526883)
        ·
          refine ⟨17116872371540632089790325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11411248247693754726526883 17116872371540632089790325)
          ·
            refine ⟨1604706784831934258417843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17116872371540632089790325 1604706784831934258417843)
            ·
              refine ⟨2407060177247901387626765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604706784831934258417843 2407060177247901387626765)
              ·
                refine ⟨902647566467963020360037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2407060177247901387626765 902647566467963020360037)
                ·
                  refine ⟨169246418712743066317507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902647566467963020360037 169246418712743066317507)
                  ·
                    rfl

theorem cell20_370807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_370807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370807 prefixEnd_370807 := by exact prefixLift 370807
  have htrace : WordTrace (prefixWord ++ tailWord_370807) baseStart_370807 baseEnd_370807 := by
    simpa [prefixWord, tailWord_370807, baseEnd_370807] using wordTrace_append hprefix tailTrace_370807
  have hstable : (prefixWord ++ tailWord_370807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370807).length < 2 ^ (prefixWord ++ tailWord_370807).sum := by decide
  have hdescent : baseEnd_370807 < baseStart_370807 := by decide
  rcases family_descends (prefixWord ++ tailWord_370807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370824 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_370824 : Nat := 118140960795 + 370824 * 2 ^ 59
def prefixEnd_370824 : Nat := 4983230072969 + 3 ^ 40 * 370824 * 2
def baseEnd_370824 : Nat := 169254177975966562750771

theorem tailTrace_370824 : CollatzResearch.WordTrace tailWord_370824 prefixEnd_370824 169254177975966562750771 := by
  unfold tailWord_370824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762531204287727271107763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9016708272383636361477017 6762531204287727271107763)
  ·
    refine ⟨10143796806431590906661645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6762531204287727271107763 10143796806431590906661645)
    ·
      refine ⟨3803923802411846589998117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10143796806431590906661645 3803923802411846589998117)
      ·
        refine ⟨713235712952221235624647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3803923802411846589998117 713235712952221235624647)
        ·
          refine ⟨1069853569428331853436971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713235712952221235624647 1069853569428331853436971)
          ·
            refine ⟨1604780354142497780155457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069853569428331853436971 1604780354142497780155457)
            ·
              refine ⟨1203585265606873335116593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604780354142497780155457 1203585265606873335116593)
              ·
                refine ⟨902688949205155001337445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203585265606873335116593 902688949205155001337445)
                ·
                  refine ⟨169254177975966562750771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902688949205155001337445 169254177975966562750771)
                  ·
                    rfl

theorem cell20_370824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_370824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370824 prefixEnd_370824 := by exact prefixLift 370824
  have htrace : WordTrace (prefixWord ++ tailWord_370824) baseStart_370824 baseEnd_370824 := by
    simpa [prefixWord, tailWord_370824, baseEnd_370824] using wordTrace_append hprefix tailTrace_370824
  have hstable : (prefixWord ++ tailWord_370824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370824).length < 2 ^ (prefixWord ++ tailWord_370824).sum := by decide
  have hdescent : baseEnd_370824 < baseStart_370824 := by decide
  rcases family_descends (prefixWord ++ tailWord_370824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370858 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_370858 : Nat := 118140960795 + 370858 * 2 ^ 59
def prefixEnd_370858 : Nat := 4983230072969 + 3 ^ 40 * 370858 * 2
def baseEnd_370858 : Nat := 169269696502413555617299

theorem tailTrace_370858 : CollatzResearch.WordTrace tailWord_370858 prefixEnd_370858 169269696502413555617299 := by
  unfold tailWord_370858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381575622613069587238307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9017534993634852232635485 3381575622613069587238307)
  ·
    refine ⟨5072363433919604380857461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381575622613069587238307 5072363433919604380857461)
    ·
      refine ⟨475534071929962910705387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5072363433919604380857461 475534071929962910705387)
      ·
        refine ⟨713301107894944366058081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475534071929962910705387 713301107894944366058081)
        ·
          refine ⟨534975830921208274543561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713301107894944366058081 534975830921208274543561)
          ·
            refine ⟨401231873190906205907671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534975830921208274543561 401231873190906205907671)
            ·
              refine ⟨601847809786359308861507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401231873190906205907671 601847809786359308861507)
              ·
                refine ⟨902771714679538963292261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601847809786359308861507 902771714679538963292261)
                ·
                  refine ⟨169269696502413555617299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902771714679538963292261 169269696502413555617299)
                  ·
                    rfl

theorem cell20_370858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_370858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370858 prefixEnd_370858 := by exact prefixLift 370858
  have htrace : WordTrace (prefixWord ++ tailWord_370858) baseStart_370858 baseEnd_370858 := by
    simpa [prefixWord, tailWord_370858, baseEnd_370858] using wordTrace_append hprefix tailTrace_370858
  have hstable : (prefixWord ++ tailWord_370858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370858).length < 2 ^ (prefixWord ++ tailWord_370858).sum := by decide
  have hdescent : baseEnd_370858 < baseStart_370858 := by decide
  rcases family_descends (prefixWord ++ tailWord_370858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370868 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_370868 : Nat := 118140960795 + 370868 * 2 ^ 59
def prefixEnd_370868 : Nat := 4983230072969 + 3 ^ 40 * 370868 * 2
def baseEnd_370868 : Nat := 169274260774897965283925

theorem tailTrace_370868 : CollatzResearch.WordTrace tailWord_370868 prefixEnd_370868 169274260774897965283925 := by
  unfold tailWord_370868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763333610208025028408629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9017778146944033371211505 6763333610208025028408629)
  ·
    refine ⟨634062525957002346413309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6763333610208025028408629 634062525957002346413309)
    ·
      refine ⟨237773447233875879904991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 634062525957002346413309 237773447233875879904991)
      ·
        refine ⟨356660170850813819857487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237773447233875879904991 356660170850813819857487)
        ·
          refine ⟨534990256276220729786231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356660170850813819857487 534990256276220729786231)
          ·
            refine ⟨802485384414331094679347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534990256276220729786231 802485384414331094679347)
            ·
              refine ⟨1203728076621496642019021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802485384414331094679347 1203728076621496642019021)
              ·
                refine ⟨451398028733061240757133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203728076621496642019021 451398028733061240757133)
                ·
                  refine ⟨169274260774897965283925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451398028733061240757133 169274260774897965283925)
                  ·
                    rfl

theorem cell20_370868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_370868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370868 prefixEnd_370868 := by exact prefixLift 370868
  have htrace : WordTrace (prefixWord ++ tailWord_370868) baseStart_370868 baseEnd_370868 := by
    simpa [prefixWord, tailWord_370868, baseEnd_370868] using wordTrace_append hprefix tailTrace_370868
  have hstable : (prefixWord ++ tailWord_370868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370868).length < 2 ^ (prefixWord ++ tailWord_370868).sum := by decide
  have hdescent : baseEnd_370868 < baseStart_370868 := by decide
  rcases family_descends (prefixWord ++ tailWord_370868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370890 : List Nat := [3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_370890 : Nat := 118140960795 + 370890 * 2 ^ 59
def prefixEnd_370890 : Nat := 4983230072969 + 3 ^ 40 * 370890 * 2
def baseEnd_370890 : Nat := 56428100724787888850167

theorem tailTrace_370890 : CollatzResearch.WordTrace tailWord_370890 prefixEnd_370890 56428100724787888850167 := by
  unfold tailWord_370890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381867406584086953529531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9018313084224231876078749 3381867406584086953529531)
  ·
    refine ⟨5072801109876130430294297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381867406584086953529531 5072801109876130430294297)
    ·
      refine ⟨3804600832407097822720723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5072801109876130430294297 3804600832407097822720723)
      ·
        refine ⟨5706901248610646734081085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804600832407097822720723 5706901248610646734081085)
        ·
          refine ⟨2140087968228992525280407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5706901248610646734081085 2140087968228992525280407)
          ·
            refine ⟨3210131952343488787920611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140087968228992525280407 3210131952343488787920611)
            ·
              refine ⟨4815197928515233181880917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210131952343488787920611 4815197928515233181880917)
              ·
                refine ⟨56428100724787888850167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4815197928515233181880917 56428100724787888850167)
                ·
                  rfl

theorem cell20_370890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_370890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370890 prefixEnd_370890 := by exact prefixLift 370890
  have htrace : WordTrace (prefixWord ++ tailWord_370890) baseStart_370890 baseEnd_370890 := by
    simpa [prefixWord, tailWord_370890, baseEnd_370890] using wordTrace_append hprefix tailTrace_370890
  have hstable : (prefixWord ++ tailWord_370890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370890).length < 2 ^ (prefixWord ++ tailWord_370890).sum := by decide
  have hdescent : baseEnd_370890 < baseStart_370890 := by decide
  rcases family_descends (prefixWord ++ tailWord_370890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370897 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_370897 : Nat := 118140960795 + 370897 * 2 ^ 59
def prefixEnd_370897 : Nat := 4983230072969 + 3 ^ 40 * 370897 * 2
def baseEnd_370897 : Nat := 169287497165102753317139

theorem tailTrace_370897 : CollatzResearch.WordTrace tailWord_370897 prefixEnd_370897 169287497165102753317139 := by
  unfold tailWord_370897
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527724937310988009622945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9018483291540658673081963 13527724937310988009622945)
  ·
    refine ⟨10145793702983241007217209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13527724937310988009622945 10145793702983241007217209)
    ·
      refine ⟨7609345277237430755412907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10145793702983241007217209 7609345277237430755412907)
      ·
        refine ⟨11414017915856146133119361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609345277237430755412907 11414017915856146133119361)
        ·
          refine ⟨8560513436892109599839521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11414017915856146133119361 8560513436892109599839521)
          ·
            refine ⟨6420385077669082199879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8560513436892109599839521 6420385077669082199879641)
            ·
              refine ⟨4815288808251811649909731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420385077669082199879641 4815288808251811649909731)
              ·
                refine ⟨7222933212377717474864597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815288808251811649909731 7222933212377717474864597)
                ·
                  refine ⟨169287497165102753317139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7222933212377717474864597 169287497165102753317139)
                  ·
                    rfl

theorem cell20_370897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_370897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370897 prefixEnd_370897 := by exact prefixLift 370897
  have htrace : WordTrace (prefixWord ++ tailWord_370897) baseStart_370897 baseEnd_370897 := by
    simpa [prefixWord, tailWord_370897, baseEnd_370897] using wordTrace_append hprefix tailTrace_370897
  have hstable : (prefixWord ++ tailWord_370897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370897).length < 2 ^ (prefixWord ++ tailWord_370897).sum := by decide
  have hdescent : baseEnd_370897 < baseStart_370897 := by decide
  rcases family_descends (prefixWord ++ tailWord_370897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370917 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 2]
def baseStart_370917 : Nat := 118140960795 + 370917 * 2 ^ 59
def prefixEnd_370917 : Nat := 4983230072969 + 3 ^ 40 * 370917 * 2
def baseEnd_370917 : Nat := 169296625710071572650391

theorem tailTrace_370917 : CollatzResearch.WordTrace tailWord_370917 prefixEnd_370917 169296625710071572650391 := by
  unfold tailWord_370917
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528454397238531425351005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9018969598159020950234003 13528454397238531425351005)
  ·
    refine ⟨5073170398964449284506627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13528454397238531425351005 5073170398964449284506627)
    ·
      refine ⟨7609755598446673926759941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073170398964449284506627 7609755598446673926759941)
      ·
        refine ⟨1426829174708751361267489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7609755598446673926759941 1426829174708751361267489)
        ·
          refine ⟨1070121881031563520950617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426829174708751361267489 1070121881031563520950617)
          ·
            refine ⟨802591410773672640712963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070121881031563520950617 802591410773672640712963)
            ·
              refine ⟨1203887116160508961069445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802591410773672640712963 1203887116160508961069445)
              ·
                refine ⟨225728834280095430200521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1203887116160508961069445 225728834280095430200521)
                ·
                  refine ⟨169296625710071572650391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225728834280095430200521 169296625710071572650391)
                  ·
                    rfl

theorem cell20_370917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_370917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370917 prefixEnd_370917 := by exact prefixLift 370917
  have htrace : WordTrace (prefixWord ++ tailWord_370917) baseStart_370917 baseEnd_370917 := by
    simpa [prefixWord, tailWord_370917, baseEnd_370917] using wordTrace_append hprefix tailTrace_370917
  have hstable : (prefixWord ++ tailWord_370917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370917).length < 2 ^ (prefixWord ++ tailWord_370917).sum := by decide
  have hdescent : baseEnd_370917 < baseStart_370917 := by decide
  rcases family_descends (prefixWord ++ tailWord_370917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370945 : List Nat := [1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_370945 : Nat := 118140960795 + 370945 * 2 ^ 59
def prefixEnd_370945 : Nat := 4983230072969 + 3 ^ 40 * 370945 * 2
def baseEnd_370945 : Nat := 56436468557675973238981

theorem tailTrace_370945 : CollatzResearch.WordTrace tailWord_370945 prefixEnd_370945 56436468557675973238981 := by
  unfold tailWord_370945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529475641137092207370289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9019650427424728138246859 13529475641137092207370289)
  ·
    refine ⟨10147106730852819155527717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13529475641137092207370289 10147106730852819155527717)
    ·
      refine ⟨1902582512034903591661447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10147106730852819155527717 1902582512034903591661447)
      ·
        refine ⟨2853873768052355387492171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902582512034903591661447 2853873768052355387492171)
        ·
          refine ⟨4280810652078533081238257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853873768052355387492171 4280810652078533081238257)
          ·
            refine ⟨3210607989058899810928693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280810652078533081238257 3210607989058899810928693)
            ·
              refine ⟨300994498974271857274565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3210607989058899810928693 300994498974271857274565)
              ·
                refine ⟨56436468557675973238981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300994498974271857274565 56436468557675973238981)
                ·
                  rfl

theorem cell20_370945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_370945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370945 prefixEnd_370945 := by exact prefixLift 370945
  have htrace : WordTrace (prefixWord ++ tailWord_370945) baseStart_370945 baseEnd_370945 := by
    simpa [prefixWord, tailWord_370945, baseEnd_370945] using wordTrace_append hprefix tailTrace_370945
  have hstable : (prefixWord ++ tailWord_370945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370945).length < 2 ^ (prefixWord ++ tailWord_370945).sum := by decide
  have hdescent : baseEnd_370945 < baseStart_370945 := by decide
  rcases family_descends (prefixWord ++ tailWord_370945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370976 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_370976 : Nat := 118140960795 + 370976 * 2 ^ 59
def prefixEnd_370976 : Nat := 4983230072969 + 3 ^ 40 * 370976 * 2
def baseEnd_370976 : Nat := 169323554917729589683483

theorem tailTrace_370976 : CollatzResearch.WordTrace tailWord_370976 prefixEnd_370976 169323554917729589683483 := by
  unfold tailWord_370976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765303152012392250874391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9020404202683189667832521 6765303152012392250874391)
  ·
    refine ⟨10147954728018588376311587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6765303152012392250874391 10147954728018588376311587)
    ·
      refine ⟨15221932092027882564467381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10147954728018588376311587 15221932092027882564467381)
      ·
        refine ⟨1427056133627613990418817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15221932092027882564467381 1427056133627613990418817)
        ·
          refine ⟨1070292100220710492814113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1427056133627613990418817 1070292100220710492814113)
          ·
            refine ⟨802719075165532869610585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070292100220710492814113 802719075165532869610585)
            ·
              refine ⟨602039306374149652207939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802719075165532869610585 602039306374149652207939)
              ·
                refine ⟨903058959561224478311909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602039306374149652207939 903058959561224478311909)
                ·
                  refine ⟨169323554917729589683483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903058959561224478311909 169323554917729589683483)
                  ·
                    rfl

theorem cell20_370976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_370976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370976 prefixEnd_370976 := by exact prefixLift 370976
  have htrace : WordTrace (prefixWord ++ tailWord_370976) baseStart_370976 baseEnd_370976 := by
    simpa [prefixWord, tailWord_370976, baseEnd_370976] using wordTrace_append hprefix tailTrace_370976
  have hstable : (prefixWord ++ tailWord_370976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370976).length < 2 ^ (prefixWord ++ tailWord_370976).sum := by decide
  have hdescent : baseEnd_370976 < baseStart_370976 := by decide
  rcases family_descends (prefixWord ++ tailWord_370976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370997 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_370997 : Nat := 118140960795 + 370997 * 2 ^ 59
def prefixEnd_370997 : Nat := 4983230072969 + 3 ^ 40 * 370997 * 2
def baseEnd_370997 : Nat := 169333139889946849983397

theorem tailTrace_370997 : CollatzResearch.WordTrace tailWord_370997 prefixEnd_370997 169333139889946849983397 := by
  unfold tailWord_370997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531372236948705088263245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9020914824632470058842163 13531372236948705088263245)
  ·
    refine ⟨5074264588855764408098717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13531372236948705088263245 5074264588855764408098717)
    ·
      refine ⟨1902849220820911653037019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5074264588855764408098717 1902849220820911653037019)
      ·
        refine ⟨2854273831231367479555529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902849220820911653037019 2854273831231367479555529)
        ·
          refine ⟨2140705373423525609666647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854273831231367479555529 2140705373423525609666647)
          ·
            refine ⟨3211058060135288414499971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140705373423525609666647 3211058060135288414499971)
            ·
              refine ⟨4816587090202932621749957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211058060135288414499971 4816587090202932621749957)
              ·
                refine ⟨903110079413049866578117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4816587090202932621749957 903110079413049866578117)
                ·
                  refine ⟨169333139889946849983397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903110079413049866578117 169333139889946849983397)
                  ·
                    rfl

theorem cell20_370997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_370997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_370997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_370997 prefixEnd_370997 := by exact prefixLift 370997
  have htrace : WordTrace (prefixWord ++ tailWord_370997) baseStart_370997 baseEnd_370997 := by
    simpa [prefixWord, tailWord_370997, baseEnd_370997] using wordTrace_append hprefix tailTrace_370997
  have hstable : (prefixWord ++ tailWord_370997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370997).length < 2 ^ (prefixWord ++ tailWord_370997).sum := by decide
  have hdescent : baseEnd_370997 < baseStart_370997 := by decide
  rcases family_descends (prefixWord ++ tailWord_370997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371004 : List Nat := [2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_371004 : Nat := 118140960795 + 371004 * 2 ^ 59
def prefixEnd_371004 : Nat := 4983230072969 + 3 ^ 40 * 371004 * 2
def baseEnd_371004 : Nat := 56445444960228645583345

theorem tailTrace_371004 : CollatzResearch.WordTrace tailWord_371004 prefixEnd_371004 56445444960228645583345 := by
  unfold tailWord_371004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765813773961672641884033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9021085031948896855845377 6765813773961672641884033)
  ·
    refine ⟨5074360330471254481413025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6765813773961672641884033 5074360330471254481413025)
    ·
      refine ⟨3805770247853440861059769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074360330471254481413025 3805770247853440861059769)
      ·
        refine ⟨2854327685890080645794827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3805770247853440861059769 2854327685890080645794827)
        ·
          refine ⟨4281491528835120968692241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854327685890080645794827 4281491528835120968692241)
          ·
            refine ⟨3211118646626340726519181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4281491528835120968692241 3211118646626340726519181)
            ·
              refine ⟨1204169492484877772444693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3211118646626340726519181 1204169492484877772444693)
              ·
                refine ⟨56445444960228645583345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1204169492484877772444693 56445444960228645583345)
                ·
                  rfl

theorem cell20_371004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_371004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371004 prefixEnd_371004 := by exact prefixLift 371004
  have htrace : WordTrace (prefixWord ++ tailWord_371004) baseStart_371004 baseEnd_371004 := by
    simpa [prefixWord, tailWord_371004, baseEnd_371004] using wordTrace_append hprefix tailTrace_371004
  have hstable : (prefixWord ++ tailWord_371004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371004).length < 2 ^ (prefixWord ++ tailWord_371004).sum := by decide
  have hdescent : baseEnd_371004 < baseStart_371004 := by decide
  rcases family_descends (prefixWord ++ tailWord_371004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371011 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_371011 : Nat := 118140960795 + 371011 * 2 ^ 59
def prefixEnd_371011 : Nat := 4983230072969 + 3 ^ 40 * 371011 * 2
def baseEnd_371011 : Nat := 169339529871425023516673

theorem tailTrace_371011 : CollatzResearch.WordTrace tailWord_371011 prefixEnd_371011 169339529871425023516673 := by
  unfold tailWord_371011
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531882858897985479272887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9021255239265323652848591 13531882858897985479272887)
  ·
    refine ⟨20297824288346978218909331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531882858897985479272887 20297824288346978218909331)
    ·
      refine ⟨30446736432520467328363997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297824288346978218909331 30446736432520467328363997)
      ·
        refine ⟨11417526162195175248136499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30446736432520467328363997 11417526162195175248136499)
        ·
          refine ⟨17126289243292762872204749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417526162195175248136499 17126289243292762872204749)
          ·
            refine ⟨6422358466234786077076781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17126289243292762872204749 6422358466234786077076781)
            ·
              refine ⟨2408384424838044778903793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6422358466234786077076781 2408384424838044778903793)
              ·
                refine ⟨1806288318628533584177845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408384424838044778903793 1806288318628533584177845)
                ·
                  refine ⟨169339529871425023516673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806288318628533584177845 169339529871425023516673)
                  ·
                    rfl

theorem cell20_371011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_371011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371011 prefixEnd_371011 := by exact prefixLift 371011
  have htrace : WordTrace (prefixWord ++ tailWord_371011) baseStart_371011 baseEnd_371011 := by
    simpa [prefixWord, tailWord_371011, baseEnd_371011] using wordTrace_append hprefix tailTrace_371011
  have hstable : (prefixWord ++ tailWord_371011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371011).length < 2 ^ (prefixWord ++ tailWord_371011).sum := by decide
  have hdescent : baseEnd_371011 < baseStart_371011 := by decide
  rcases family_descends (prefixWord ++ tailWord_371011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371028 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_371028 : Nat := 118140960795 + 371028 * 2 ^ 59
def prefixEnd_371028 : Nat := 4983230072969 + 3 ^ 40 * 371028 * 2
def baseEnd_371028 : Nat := 169347289134648519949937

theorem tailTrace_371028 : CollatzResearch.WordTrace tailWord_371028 prefixEnd_371028 169347289134648519949937 := by
  unfold tailWord_371028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766251449918198691320869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9021668599890931588427825 6766251449918198691320869)
  ·
    refine ⟨1268672146859662254622663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6766251449918198691320869 1268672146859662254622663)
    ·
      refine ⟨1903008220289493381933995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268672146859662254622663 1903008220289493381933995)
      ·
        refine ⟨2854512330434240072900993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903008220289493381933995 2854512330434240072900993)
        ·
          refine ⟨2140884247825680054675745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854512330434240072900993 2140884247825680054675745)
          ·
            refine ⟨1605663185869260041006809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140884247825680054675745 1605663185869260041006809)
            ·
              refine ⟨1204247389401945030755107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605663185869260041006809 1204247389401945030755107)
              ·
                refine ⟨1806371084102917546132661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204247389401945030755107 1806371084102917546132661)
                ·
                  refine ⟨169347289134648519949937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806371084102917546132661 169347289134648519949937)
                  ·
                    rfl

theorem cell20_371028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_371028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371028 prefixEnd_371028 := by exact prefixLift 371028
  have htrace : WordTrace (prefixWord ++ tailWord_371028) baseStart_371028 baseEnd_371028 := by
    simpa [prefixWord, tailWord_371028, baseEnd_371028] using wordTrace_append hprefix tailTrace_371028
  have hstable : (prefixWord ++ tailWord_371028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371028).length < 2 ^ (prefixWord ++ tailWord_371028).sum := by decide
  have hdescent : baseEnd_371028 < baseStart_371028 := by decide
  rcases family_descends (prefixWord ++ tailWord_371028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371031 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 2]
def baseStart_371031 : Nat := 118140960795 + 371031 * 2 ^ 59
def prefixEnd_371031 : Nat := 4983230072969 + 3 ^ 40 * 371031 * 2
def baseEnd_371031 : Nat := 169348658416393842849925

theorem tailTrace_371031 : CollatzResearch.WordTrace tailWord_371031 prefixEnd_371031 169348658416393842849925 := by
  unfold tailWord_371031
  simp only [CollatzResearch.WordTrace]
  refine ⟨13532612318825528895000947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9021741545883685930000631 13532612318825528895000947)
  ·
    refine ⟨20298918478238293342501421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13532612318825528895000947 20298918478238293342501421)
    ·
      refine ⟨7612094429339360003438033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20298918478238293342501421 7612094429339360003438033)
      ·
        refine ⟨5709070822004520002578525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7612094429339360003438033 5709070822004520002578525)
        ·
          refine ⟨2140901558251695000966947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5709070822004520002578525 2140901558251695000966947)
          ·
            refine ⟨3211352337377542501450421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140901558251695000966947 3211352337377542501450421)
            ·
              refine ⟨301064281629144609510977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3211352337377542501450421 301064281629144609510977)
              ·
                refine ⟨225798211221858457133233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301064281629144609510977 225798211221858457133233)
                ·
                  refine ⟨169348658416393842849925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225798211221858457133233 169348658416393842849925)
                  ·
                    rfl

theorem cell20_371031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2].length) (baseStart_371031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371031 prefixEnd_371031 := by exact prefixLift 371031
  have htrace : WordTrace (prefixWord ++ tailWord_371031) baseStart_371031 baseEnd_371031 := by
    simpa [prefixWord, tailWord_371031, baseEnd_371031] using wordTrace_append hprefix tailTrace_371031
  have hstable : (prefixWord ++ tailWord_371031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371031).length < 2 ^ (prefixWord ++ tailWord_371031).sum := by decide
  have hdescent : baseEnd_371031 < baseStart_371031 := by decide
  rcases family_descends (prefixWord ++ tailWord_371031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371045 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 3]
def baseStart_371045 : Nat := 118140960795 + 371045 * 2 ^ 59
def prefixEnd_371045 : Nat := 4983230072969 + 3 ^ 40 * 371045 * 2
def baseEnd_371045 : Nat := 169355048397872016383201

theorem tailTrace_371045 : CollatzResearch.WordTrace tailWord_371045 prefixEnd_371045 169355048397872016383201 := by
  unfold tailWord_371045
  simp only [CollatzResearch.WordTrace]
  refine ⟨13533122940774809286010589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9022081960516539524007059 13533122940774809286010589)
  ·
    refine ⟨5074921102790553482253971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13533122940774809286010589 5074921102790553482253971)
    ·
      refine ⟨7612381654185830223380957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074921102790553482253971 7612381654185830223380957)
      ·
        refine ⟨2854643120319686333767859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7612381654185830223380957 2854643120319686333767859)
        ·
          refine ⟨4281964680479529500651789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854643120319686333767859 4281964680479529500651789)
          ·
            refine ⟨1605736755179823562744421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4281964680479529500651789 1605736755179823562744421)
            ·
              refine ⟨301075641596216918014579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1605736755179823562744421 301075641596216918014579)
              ·
                refine ⟨451613462394325377021869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301075641596216918014579 451613462394325377021869)
                ·
                  refine ⟨169355048397872016383201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451613462394325377021869 169355048397872016383201)
                  ·
                    rfl

theorem cell20_371045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_371045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371045 prefixEnd_371045 := by exact prefixLift 371045
  have htrace : WordTrace (prefixWord ++ tailWord_371045) baseStart_371045 baseEnd_371045 := by
    simpa [prefixWord, tailWord_371045, baseEnd_371045] using wordTrace_append hprefix tailTrace_371045
  have hstable : (prefixWord ++ tailWord_371045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371045).length < 2 ^ (prefixWord ++ tailWord_371045).sum := by decide
  have hdescent : baseEnd_371045 < baseStart_371045 := by decide
  rcases family_descends (prefixWord ++ tailWord_371045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371082 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_371082 : Nat := 118140960795 + 371082 * 2 ^ 59
def prefixEnd_371082 : Nat := 4983230072969 + 3 ^ 40 * 371082 * 2
def baseEnd_371082 : Nat := 169371936206064332149717

theorem tailTrace_371082 : CollatzResearch.WordTrace tailWord_371082 prefixEnd_371082 169371936206064332149717 := by
  unfold tailWord_371082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383618110410191151276875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9022981627760509736738333 3383618110410191151276875)
  ·
    refine ⟨5075427165615286726915313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383618110410191151276875 5075427165615286726915313)
    ·
      refine ⟨3806570374211465045186485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5075427165615286726915313 3806570374211465045186485)
      ·
        refine ⟨356865972582324847986233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3806570374211465045186485 356865972582324847986233)
        ·
          refine ⟨267649479436743635989675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356865972582324847986233 267649479436743635989675)
          ·
            refine ⟨401474219155115453984513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267649479436743635989675 401474219155115453984513)
            ·
              refine ⟨301105664366336590488385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401474219155115453984513 301105664366336590488385)
              ·
                refine ⟨225829248274752442866289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301105664366336590488385 225829248274752442866289)
                ·
                  refine ⟨169371936206064332149717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225829248274752442866289 169371936206064332149717)
                  ·
                    rfl

theorem cell20_371082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_371082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371082 prefixEnd_371082 := by exact prefixLift 371082
  have htrace : WordTrace (prefixWord ++ tailWord_371082) baseStart_371082 baseEnd_371082 := by
    simpa [prefixWord, tailWord_371082, baseEnd_371082] using wordTrace_append hprefix tailTrace_371082
  have hstable : (prefixWord ++ tailWord_371082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371082).length < 2 ^ (prefixWord ++ tailWord_371082).sum := by decide
  have hdescent : baseEnd_371082 < baseStart_371082 := by decide
  rcases family_descends (prefixWord ++ tailWord_371082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371086 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_371086 : Nat := 118140960795 + 371086 * 2 ^ 59
def prefixEnd_371086 : Nat := 4983230072969 + 3 ^ 40 * 371086 * 2
def baseEnd_371086 : Nat := 169373761915058096016367

theorem tailTrace_371086 : CollatzResearch.WordTrace tailWord_371086 prefixEnd_371086 169373761915058096016367 := by
  unfold tailWord_371086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691827291703284161031639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9023078889084182192168741 1691827291703284161031639)
  ·
    refine ⟨2537740937554926241547459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1691827291703284161031639 2537740937554926241547459)
    ·
      refine ⟨3806611406332389362321189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537740937554926241547459 3806611406332389362321189)
      ·
        refine ⟨713739638687323005435223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3806611406332389362321189 713739638687323005435223)
        ·
          refine ⟨1070609458030984508152835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713739638687323005435223 1070609458030984508152835)
          ·
            refine ⟨1605914187046476762229253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070609458030984508152835 1605914187046476762229253)
            ·
              refine ⟨301108910071214392917985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1605914187046476762229253 301108910071214392917985)
              ·
                refine ⟨225831682553410794688489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301108910071214392917985 225831682553410794688489)
                ·
                  refine ⟨169373761915058096016367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225831682553410794688489 169373761915058096016367)
                  ·
                    rfl

theorem cell20_371086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_371086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371086 prefixEnd_371086 := by exact prefixLift 371086
  have htrace : WordTrace (prefixWord ++ tailWord_371086) baseStart_371086 baseEnd_371086 := by
    simpa [prefixWord, tailWord_371086, baseEnd_371086] using wordTrace_append hprefix tailTrace_371086
  have hstable : (prefixWord ++ tailWord_371086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371086).length < 2 ^ (prefixWord ++ tailWord_371086).sum := by decide
  have hdescent : baseEnd_371086 < baseStart_371086 := by decide
  rcases family_descends (prefixWord ++ tailWord_371086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371104 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_371104 : Nat := 118140960795 + 371104 * 2 ^ 59
def prefixEnd_371104 : Nat := 4983230072969 + 3 ^ 40 * 371104 * 2
def baseEnd_371104 : Nat := 169381977605530033416293

theorem tailTrace_371104 : CollatzResearch.WordTrace tailWord_371104 prefixEnd_371104 169381977605530033416293 := by
  unfold tailWord_371104
  simp only [CollatzResearch.WordTrace]
  refine ⟨6767637423780531181204183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9023516565040708241605577 6767637423780531181204183)
  ·
    refine ⟨10151456135670796771806275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6767637423780531181204183 10151456135670796771806275)
    ·
      refine ⟨15227184203506195157709413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151456135670796771806275 15227184203506195157709413)
      ·
        refine ⟨2855097038157411592070515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15227184203506195157709413 2855097038157411592070515)
        ·
          refine ⟨4282645557236117388105773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855097038157411592070515 4282645557236117388105773)
          ·
            refine ⟨1605992083963544020539665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4282645557236117388105773 1605992083963544020539665)
            ·
              refine ⟨1204494062972658015404749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605992083963544020539665 1204494062972658015404749)
              ·
                refine ⟨451685273614746755776781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204494062972658015404749 451685273614746755776781)
                ·
                  refine ⟨169381977605530033416293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451685273614746755776781 169381977605530033416293)
                  ·
                    rfl

theorem cell20_371104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_371104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371104 prefixEnd_371104 := by exact prefixLift 371104
  have htrace : WordTrace (prefixWord ++ tailWord_371104) baseStart_371104 baseEnd_371104 := by
    simpa [prefixWord, tailWord_371104, baseEnd_371104] using wordTrace_append hprefix tailTrace_371104
  have hstable : (prefixWord ++ tailWord_371104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371104).length < 2 ^ (prefixWord ++ tailWord_371104).sum := by decide
  have hdescent : baseEnd_371104 < baseStart_371104 := by decide
  rcases family_descends (prefixWord ++ tailWord_371104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371111 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_371111 : Nat := 118140960795 + 371111 * 2 ^ 59
def prefixEnd_371111 : Nat := 4983230072969 + 3 ^ 40 * 371111 * 2
def baseEnd_371111 : Nat := 169385172596269120182931

theorem tailTrace_371111 : CollatzResearch.WordTrace tailWord_371111 prefixEnd_371111 169385172596269120182931 := by
  unfold tailWord_371111
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535530158535702557913187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9023686772357135038608791 13535530158535702557913187)
  ·
    refine ⟨20303295237803553836869781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13535530158535702557913187 20303295237803553836869781)
    ·
      refine ⟨951716964272041586103271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20303295237803553836869781 951716964272041586103271)
      ·
        refine ⟨1427575446408062379154907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951716964272041586103271 1427575446408062379154907)
        ·
          refine ⟨2141363169612093568732361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427575446408062379154907 2141363169612093568732361)
          ·
            refine ⟨1606022377209070176549271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141363169612093568732361 1606022377209070176549271)
            ·
              refine ⟨2409033565813605264823907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606022377209070176549271 2409033565813605264823907)
              ·
                refine ⟨3613550348720407897235861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409033565813605264823907 3613550348720407897235861)
                ·
                  refine ⟨169385172596269120182931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3613550348720407897235861 169385172596269120182931)
                  ·
                    rfl

theorem cell20_371111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_371111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371111 prefixEnd_371111 := by exact prefixLift 371111
  have htrace : WordTrace (prefixWord ++ tailWord_371111) baseStart_371111 baseEnd_371111 := by
    simpa [prefixWord, tailWord_371111, baseEnd_371111] using wordTrace_append hprefix tailTrace_371111
  have hstable : (prefixWord ++ tailWord_371111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371111).length < 2 ^ (prefixWord ++ tailWord_371111).sum := by decide
  have hdescent : baseEnd_371111 < baseStart_371111 := by decide
  rcases family_descends (prefixWord ++ tailWord_371111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371173 : List Nat := [1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_371173 : Nat := 118140960795 + 371173 * 2 ^ 59
def prefixEnd_371173 : Nat := 4983230072969 + 3 ^ 40 * 371173 * 2
def baseEnd_371173 : Nat := 56471157028557486705337

theorem tailTrace_371173 : CollatzResearch.WordTrace tailWord_371173 prefixEnd_371173 56471157028557486705337 := by
  unfold tailWord_371173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537791484311087146670173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9025194322874058097780115 13537791484311087146670173)
  ·
    refine ⟨5076671806616657680001315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13537791484311087146670173 5076671806616657680001315)
    ·
      refine ⟨7615007709924986520001973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5076671806616657680001315 7615007709924986520001973)
      ·
        refine ⟨713906972805467486250185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7615007709924986520001973 713906972805467486250185)
        ·
          refine ⟨535430229604100614687639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713906972805467486250185 535430229604100614687639)
          ·
            refine ⟨803145344406150922031459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535430229604100614687639 803145344406150922031459)
            ·
              refine ⟨1204718016609226383047189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803145344406150922031459 1204718016609226383047189)
              ·
                refine ⟨56471157028557486705337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1204718016609226383047189 56471157028557486705337)
                ·
                  rfl

theorem cell20_371173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_371173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371173 prefixEnd_371173 := by exact prefixLift 371173
  have htrace : WordTrace (prefixWord ++ tailWord_371173) baseStart_371173 baseEnd_371173 := by
    simpa [prefixWord, tailWord_371173, baseEnd_371173] using wordTrace_append hprefix tailTrace_371173
  have hstable : (prefixWord ++ tailWord_371173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371173).length < 2 ^ (prefixWord ++ tailWord_371173).sum := by decide
  have hdescent : baseEnd_371173 < baseStart_371173 := by decide
  rcases family_descends (prefixWord ++ tailWord_371173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371204 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_371204 : Nat := 118140960795 + 371204 * 2 ^ 59
def prefixEnd_371204 : Nat := 4983230072969 + 3 ^ 40 * 371204 * 2
def baseEnd_371204 : Nat := 169427620330374130082551

theorem tailTrace_371204 : CollatzResearch.WordTrace tailWord_371204 prefixEnd_371204 169427620330374130082551 := by
  unfold tailWord_371204
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769461073599389720524333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9025948098132519627365777 6769461073599389720524333)
  ·
    refine ⟨2538547902599771145196625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6769461073599389720524333 2538547902599771145196625)
    ·
      refine ⟨1903910926949828358897469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2538547902599771145196625 1903910926949828358897469)
      ·
        refine ⟨713966597606185634586551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1903910926949828358897469 713966597606185634586551)
        ·
          refine ⟨1070949896409278451879827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713966597606185634586551 1070949896409278451879827)
          ·
            refine ⟨1606424844613917677819741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070949896409278451879827 1606424844613917677819741)
            ·
              refine ⟨602409316730219129182403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1606424844613917677819741 602409316730219129182403)
              ·
                refine ⟨903613975095328693773605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602409316730219129182403 903613975095328693773605)
                ·
                  refine ⟨169427620330374130082551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903613975095328693773605 169427620330374130082551)
                  ·
                    rfl

theorem cell20_371204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_371204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371204 prefixEnd_371204 := by exact prefixLift 371204
  have htrace : WordTrace (prefixWord ++ tailWord_371204) baseStart_371204 baseEnd_371204 := by
    simpa [prefixWord, tailWord_371204, baseEnd_371204] using wordTrace_append hprefix tailTrace_371204
  have hstable : (prefixWord ++ tailWord_371204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371204).length < 2 ^ (prefixWord ++ tailWord_371204).sum := by decide
  have hdescent : baseEnd_371204 < baseStart_371204 := by decide
  rcases family_descends (prefixWord ++ tailWord_371204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371214 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_371214 : Nat := 118140960795 + 371214 * 2 ^ 59
def prefixEnd_371214 : Nat := 4983230072969 + 3 ^ 40 * 371214 * 2
def baseEnd_371214 : Nat := 169432184602858539749177

theorem tailTrace_371214 : CollatzResearch.WordTrace tailWord_371214 prefixEnd_371214 169432184602858539749177 := by
  unfold tailWord_371214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692410859645318893614087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9026191251441700765941797 1692410859645318893614087)
  ·
    refine ⟨2538616289467978340421131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692410859645318893614087 2538616289467978340421131)
    ·
      refine ⟨3807924434201967510631697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538616289467978340421131 3807924434201967510631697)
      ·
        refine ⟨2855943325651475632973773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807924434201967510631697 2855943325651475632973773)
        ·
          refine ⟨1070978747119303362365165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2855943325651475632973773 1070978747119303362365165)
          ·
            refine ⟨401617030169738760886937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1070978747119303362365165 401617030169738760886937)
            ·
              refine ⟨301212772627304070665203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401617030169738760886937 301212772627304070665203)
              ·
                refine ⟨451819158940956105997805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301212772627304070665203 451819158940956105997805)
                ·
                  refine ⟨169432184602858539749177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451819158940956105997805 169432184602858539749177)
                  ·
                    rfl

theorem cell20_371214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_371214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371214 prefixEnd_371214 := by exact prefixLift 371214
  have htrace : WordTrace (prefixWord ++ tailWord_371214) baseStart_371214 baseEnd_371214 := by
    simpa [prefixWord, tailWord_371214, baseEnd_371214] using wordTrace_append hprefix tailTrace_371214
  have hstable : (prefixWord ++ tailWord_371214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371214).length < 2 ^ (prefixWord ++ tailWord_371214).sum := by decide
  have hdescent : baseEnd_371214 < baseStart_371214 := by decide
  rcases family_descends (prefixWord ++ tailWord_371214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371215 : List Nat := [1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_371215 : Nat := 118140960795 + 371215 * 2 ^ 59
def prefixEnd_371215 : Nat := 4983230072969 + 3 ^ 40 * 371215 * 2
def baseEnd_371215 : Nat := 56477547010035660238613

theorem tailTrace_371215 : CollatzResearch.WordTrace tailWord_371215 prefixEnd_371215 56477547010035660238613 := by
  unfold tailWord_371215
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539323350158928319699099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026215566772618879799399 13539323350158928319699099)
  ·
    refine ⟨20308985025238392479548649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13539323350158928319699099 20308985025238392479548649)
    ·
      refine ⟨15231738768928794359661487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20308985025238392479548649 15231738768928794359661487)
      ·
        refine ⟨22847608153393191539492231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15231738768928794359661487 22847608153393191539492231)
        ·
          refine ⟨34271412230089787309238347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22847608153393191539492231 34271412230089787309238347)
          ·
            refine ⟨51407118345134680963857521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34271412230089787309238347 51407118345134680963857521)
            ·
              refine ⟨38555338758851010722893141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51407118345134680963857521 38555338758851010722893141)
              ·
                refine ⟨56477547010035660238613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 38555338758851010722893141 56477547010035660238613)
                ·
                  rfl

theorem cell20_371215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_371215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371215 prefixEnd_371215 := by exact prefixLift 371215
  have htrace : WordTrace (prefixWord ++ tailWord_371215) baseStart_371215 baseEnd_371215 := by
    simpa [prefixWord, tailWord_371215, baseEnd_371215] using wordTrace_append hprefix tailTrace_371215
  have hstable : (prefixWord ++ tailWord_371215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371215).length < 2 ^ (prefixWord ++ tailWord_371215).sum := by decide
  have hdescent : baseEnd_371215 < baseStart_371215 := by decide
  rcases family_descends (prefixWord ++ tailWord_371215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371245 : List Nat := [1, 5, 4, 1, 2, 7]
def baseStart_371245 : Nat := 118140960795 + 371245 * 2 ^ 59
def prefixEnd_371245 : Nat := 4983230072969 + 3 ^ 40 * 371245 * 2
def baseEnd_371245 : Nat := 6275790142502229989471

theorem tailTrace_371245 : CollatzResearch.WordTrace tailWord_371245 prefixEnd_371245 6275790142502229989471 := by
  unfold tailWord_371245
  simp only [CollatzResearch.WordTrace]
  refine ⟨13540417540050243443291189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026945026700162295527459 13540417540050243443291189)
  ·
    refine ⟨1269414144379710322808549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13540417540050243443291189 1269414144379710322808549)
    ·
      refine ⟨238015152071195685526603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1269414144379710322808549 238015152071195685526603)
      ·
        refine ⟨357022728106793528289905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238015152071195685526603 357022728106793528289905)
        ·
          refine ⟨267767046080095146217429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357022728106793528289905 267767046080095146217429)
          ·
            refine ⟨6275790142502229989471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 267767046080095146217429 6275790142502229989471)
            ·
              rfl

theorem cell20_371245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 7].length) (baseStart_371245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371245 prefixEnd_371245 := by exact prefixLift 371245
  have htrace : WordTrace (prefixWord ++ tailWord_371245) baseStart_371245 baseEnd_371245 := by
    simpa [prefixWord, tailWord_371245, baseEnd_371245] using wordTrace_append hprefix tailTrace_371245
  have hstable : (prefixWord ++ tailWord_371245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371245).length < 2 ^ (prefixWord ++ tailWord_371245).sum := by decide
  have hdescent : baseEnd_371245 < baseStart_371245 := by decide
  rcases family_descends (prefixWord ++ tailWord_371245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371256 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_371256 : Nat := 118140960795 + 371256 * 2 ^ 59
def prefixEnd_371256 : Nat := 4983230072969 + 3 ^ 40 * 371256 * 2
def baseEnd_371256 : Nat := 169451354547293060349005

theorem tailTrace_371256 : CollatzResearch.WordTrace tailWord_371256 prefixEnd_371256 169451354547293060349005 := by
  unfold tailWord_371256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770409371505196160970811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9027212495340261547961081 6770409371505196160970811)
  ·
    refine ⟨10155614057257794241456217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6770409371505196160970811 10155614057257794241456217)
    ·
      refine ⟨7616710542943345681092163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10155614057257794241456217 7616710542943345681092163)
      ·
        refine ⟨11425065814415018521638245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7616710542943345681092163 11425065814415018521638245)
        ·
          refine ⟨2142199840202815972807171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11425065814415018521638245 2142199840202815972807171)
          ·
            refine ⟨3213299760304223959210757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142199840202815972807171 3213299760304223959210757)
            ·
              refine ⟨602493705057041992352017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3213299760304223959210757 602493705057041992352017)
              ·
                refine ⟨451870278792781494264013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602493705057041992352017 451870278792781494264013)
                ·
                  refine ⟨169451354547293060349005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451870278792781494264013 169451354547293060349005)
                  ·
                    rfl

theorem cell20_371256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_371256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371256 prefixEnd_371256 := by exact prefixLift 371256
  have htrace : WordTrace (prefixWord ++ tailWord_371256) baseStart_371256 baseEnd_371256 := by
    simpa [prefixWord, tailWord_371256, baseEnd_371256] using wordTrace_append hprefix tailTrace_371256
  have hstable : (prefixWord ++ tailWord_371256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371256).length < 2 ^ (prefixWord ++ tailWord_371256).sum := by decide
  have hdescent : baseEnd_371256 < baseStart_371256 := by decide
  rcases family_descends (prefixWord ++ tailWord_371256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371315 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_371315 : Nat := 118140960795 + 371315 * 2 ^ 59
def prefixEnd_371315 : Nat := 4983230072969 + 3 ^ 40 * 371315 * 2
def baseEnd_371315 : Nat := 169478283754951077382097

theorem tailTrace_371315 : CollatzResearch.WordTrace tailWord_371315 prefixEnd_371315 169478283754951077382097 := by
  unfold tailWord_371315
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542970649796645398339399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9028647099864430265559599 13542970649796645398339399)
  ·
    refine ⟨20314455974694968097509099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13542970649796645398339399 20314455974694968097509099)
    ·
      refine ⟨30471683962042452146263649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20314455974694968097509099 30471683962042452146263649)
      ·
        refine ⟨22853762971531839109697737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30471683962042452146263649 22853762971531839109697737)
        ·
          refine ⟨17140322228648879332273303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22853762971531839109697737 17140322228648879332273303)
          ·
            refine ⟨25710483342973318998409955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17140322228648879332273303 25710483342973318998409955)
            ·
              refine ⟨38565725014459978497614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25710483342973318998409955 38565725014459978497614933)
              ·
                refine ⟨451942090013202873018925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 38565725014459978497614933 451942090013202873018925)
                ·
                  refine ⟨169478283754951077382097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451942090013202873018925 169478283754951077382097)
                  ·
                    rfl

theorem cell20_371315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_371315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371315 prefixEnd_371315 := by exact prefixLift 371315
  have htrace : WordTrace (prefixWord ++ tailWord_371315) baseStart_371315 baseEnd_371315 := by
    simpa [prefixWord, tailWord_371315, baseEnd_371315] using wordTrace_append hprefix tailTrace_371315
  have hstable : (prefixWord ++ tailWord_371315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371315).length < 2 ^ (prefixWord ++ tailWord_371315).sum := by decide
  have hdescent : baseEnd_371315 < baseStart_371315 := by decide
  rcases family_descends (prefixWord ++ tailWord_371315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371436 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_371436 : Nat := 118140960795 + 371436 * 2 ^ 59
def prefixEnd_371436 : Nat := 4983230072969 + 3 ^ 40 * 371436 * 2
def baseEnd_371436 : Nat := 169533511452012434348269

theorem tailTrace_371436 : CollatzResearch.WordTrace tailWord_371436 prefixEnd_371436 169533511452012434348269 := by
  unfold tailWord_371436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773691941179141531747081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9031589254905522042329441 6773691941179141531747081)
  ·
    refine ⟨5080268955884356148810311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6773691941179141531747081 5080268955884356148810311)
    ·
      refine ⟨7620403433826534223215467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5080268955884356148810311 7620403433826534223215467)
      ·
        refine ⟨11430605150739801334823201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7620403433826534223215467 11430605150739801334823201)
        ·
          refine ⟨8572953863054851001117401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11430605150739801334823201 8572953863054851001117401)
          ·
            refine ⟨6429715397291138250838051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8572953863054851001117401 6429715397291138250838051)
            ·
              refine ⟨9644573095936707376257077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429715397291138250838051 9644573095936707376257077)
              ·
                refine ⟨904178727744066316524101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9644573095936707376257077 904178727744066316524101)
                ·
                  refine ⟨169533511452012434348269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904178727744066316524101 169533511452012434348269)
                  ·
                    rfl

theorem cell20_371436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_371436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371436 prefixEnd_371436 := by exact prefixLift 371436
  have htrace : WordTrace (prefixWord ++ tailWord_371436) baseStart_371436 baseEnd_371436 := by
    simpa [prefixWord, tailWord_371436, baseEnd_371436] using wordTrace_append hprefix tailTrace_371436
  have hstable : (prefixWord ++ tailWord_371436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371436).length < 2 ^ (prefixWord ++ tailWord_371436).sum := by decide
  have hdescent : baseEnd_371436 < baseStart_371436 := by decide
  rcases family_descends (prefixWord ++ tailWord_371436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371446 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_371446 : Nat := 118140960795 + 371446 * 2 ^ 59
def prefixEnd_371446 : Nat := 4983230072969 + 3 ^ 40 * 371446 * 2
def baseEnd_371446 : Nat := 169538075724496844014895

theorem tailTrace_371446 : CollatzResearch.WordTrace tailWord_371446 prefixEnd_371446 169538075724496844014895 := by
  unfold tailWord_371446
  simp only [CollatzResearch.WordTrace]
  refine ⟨846734288270128423209887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9031832408214703180905461 846734288270128423209887)
  ·
    refine ⟨1270101432405192634814831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846734288270128423209887 1270101432405192634814831)
    ·
      refine ⟨1905152148607788952222247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270101432405192634814831 1905152148607788952222247)
      ·
        refine ⟨2857728222911683428333371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905152148607788952222247 2857728222911683428333371)
        ·
          refine ⟨4286592334367525142500057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857728222911683428333371 4286592334367525142500057)
          ·
            refine ⟨3214944250775643856875043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4286592334367525142500057 3214944250775643856875043)
            ·
              refine ⟨4822416376163465785312565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214944250775643856875043 4822416376163465785312565)
              ·
                refine ⟨452101535265324917373053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4822416376163465785312565 452101535265324917373053)
                ·
                  refine ⟨169538075724496844014895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452101535265324917373053 169538075724496844014895)
                  ·
                    rfl

theorem cell20_371446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_371446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371446 prefixEnd_371446 := by exact prefixLift 371446
  have htrace : WordTrace (prefixWord ++ tailWord_371446) baseStart_371446 baseEnd_371446 := by
    simpa [prefixWord, tailWord_371446, baseEnd_371446] using wordTrace_append hprefix tailTrace_371446
  have hstable : (prefixWord ++ tailWord_371446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371446).length < 2 ^ (prefixWord ++ tailWord_371446).sum := by decide
  have hdescent : baseEnd_371446 < baseStart_371446 := by decide
  rcases family_descends (prefixWord ++ tailWord_371446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371484 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_371484 : Nat := 118140960795 + 371484 * 2 ^ 59
def prefixEnd_371484 : Nat := 4983230072969 + 3 ^ 40 * 371484 * 2
def baseEnd_371484 : Nat := 169555419959937600748073

theorem tailTrace_371484 : CollatzResearch.WordTrace tailWord_371484 prefixEnd_371484 169555419959937600748073 := by
  unfold tailWord_371484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774567293092193630620753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9032756390789591507494337 6774567293092193630620753)
  ·
    refine ⟨5080925469819145222965565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6774567293092193630620753 5080925469819145222965565)
    ·
      refine ⟨1905347051182179458612087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5080925469819145222965565 1905347051182179458612087)
      ·
        refine ⟨2858020576773269187918131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905347051182179458612087 2858020576773269187918131)
        ·
          refine ⟨4287030865159903781877197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858020576773269187918131 4287030865159903781877197)
          ·
            refine ⟨1607636574434963918203949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4287030865159903781877197 1607636574434963918203949)
            ·
              refine ⟨602863715413111469326481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1607636574434963918203949 602863715413111469326481)
              ·
                refine ⟨452147786559833601994861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602863715413111469326481 452147786559833601994861)
                ·
                  refine ⟨169555419959937600748073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452147786559833601994861 169555419959937600748073)
                  ·
                    rfl

theorem cell20_371484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_371484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371484 prefixEnd_371484 := by exact prefixLift 371484
  have htrace : WordTrace (prefixWord ++ tailWord_371484) baseStart_371484 baseEnd_371484 := by
    simpa [prefixWord, tailWord_371484, baseEnd_371484] using wordTrace_append hprefix tailTrace_371484
  have hstable : (prefixWord ++ tailWord_371484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371484).length < 2 ^ (prefixWord ++ tailWord_371484).sum := by decide
  have hdescent : baseEnd_371484 < baseStart_371484 := by decide
  rcases family_descends (prefixWord ++ tailWord_371484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371512 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_371512 : Nat := 118140960795 + 371512 * 2 ^ 59
def prefixEnd_371512 : Nat := 4983230072969 + 3 ^ 40 * 371512 * 2
def baseEnd_371512 : Nat := 169568199922893947814625

theorem tailTrace_371512 : CollatzResearch.WordTrace tailWord_371512 prefixEnd_371512 169568199922893947814625 := by
  unfold tailWord_371512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775077915041474021630395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9033437220055298695507193 6775077915041474021630395)
  ·
    refine ⟨10162616872562211032445593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775077915041474021630395 10162616872562211032445593)
    ·
      refine ⟨7621962654421658274334195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10162616872562211032445593 7621962654421658274334195)
      ·
        refine ⟨11432943981632487411501293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621962654421658274334195 11432943981632487411501293)
        ·
          refine ⟨4287353993112182779312985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11432943981632487411501293 4287353993112182779312985)
          ·
            refine ⟨3215515494834137084484739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4287353993112182779312985 3215515494834137084484739)
            ·
              refine ⟨4823273242251205626727109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215515494834137084484739 4823273242251205626727109)
              ·
                refine ⟨904363732922101055011333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4823273242251205626727109 904363732922101055011333)
                ·
                  refine ⟨169568199922893947814625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904363732922101055011333 169568199922893947814625)
                  ·
                    rfl

theorem cell20_371512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_371512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371512 prefixEnd_371512 := by exact prefixLift 371512
  have htrace : WordTrace (prefixWord ++ tailWord_371512) baseStart_371512 baseEnd_371512 := by
    simpa [prefixWord, tailWord_371512, baseEnd_371512] using wordTrace_append hprefix tailTrace_371512
  have hstable : (prefixWord ++ tailWord_371512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371512).length < 2 ^ (prefixWord ++ tailWord_371512).sum := by decide
  have hdescent : baseEnd_371512 < baseStart_371512 := by decide
  rcases family_descends (prefixWord ++ tailWord_371512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371521 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 2]
def baseStart_371521 : Nat := 118140960795 + 371521 * 2 ^ 59
def prefixEnd_371521 : Nat := 4983230072969 + 3 ^ 40 * 371521 * 2
def baseEnd_371521 : Nat := 169572307768129916514589

theorem tailTrace_371521 : CollatzResearch.WordTrace tailWord_371521 prefixEnd_371521 169572307768129916514589 := by
  unfold tailWord_371521
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550484087050342580338417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9033656058033561720225611 13550484087050342580338417)
  ·
    refine ⟨10162863065287756935253813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13550484087050342580338417 10162863065287756935253813)
    ·
      refine ⟨952768412370727212680045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10162863065287756935253813 952768412370727212680045)
      ·
        refine ⟨357288154639022704755017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 952768412370727212680045 357288154639022704755017)
        ·
          refine ⟨267966115979267028566263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357288154639022704755017 267966115979267028566263)
          ·
            refine ⟨401949173968900542849395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267966115979267028566263 401949173968900542849395)
            ·
              refine ⟨602923760953350814274093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401949173968900542849395 602923760953350814274093)
              ·
                refine ⟨226096410357506555352785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602923760953350814274093 226096410357506555352785)
                ·
                  refine ⟨169572307768129916514589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226096410357506555352785 169572307768129916514589)
                  ·
                    rfl

theorem cell20_371521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_371521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371521 prefixEnd_371521 := by exact prefixLift 371521
  have htrace : WordTrace (prefixWord ++ tailWord_371521) baseStart_371521 baseEnd_371521 := by
    simpa [prefixWord, tailWord_371521, baseEnd_371521] using wordTrace_append hprefix tailTrace_371521
  have hstable : (prefixWord ++ tailWord_371521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371521).length < 2 ^ (prefixWord ++ tailWord_371521).sum := by decide
  have hdescent : baseEnd_371521 < baseStart_371521 := by decide
  rcases family_descends (prefixWord ++ tailWord_371521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
