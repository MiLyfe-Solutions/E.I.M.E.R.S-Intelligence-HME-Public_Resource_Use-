import V185TrunkScan23Chunk0766

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4536064 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_4536064 : Nat := 118140960795 + 4536064 * 2 ^ 59
def prefixEnd_4536064 : Nat := 4983230072969 + 3 ^ 40 * 4536064 * 2
def baseEnd_4536064 : Nat := 2329181111556245862439027

theorem tailTrace_4536064 : CollatzResearch.WordTrace tailWord_4536064 prefixEnd_4536064 2329181111556245862439027 := by
  unfold tailWord_4536064
  simp only [CollatzResearch.WordTrace]
  refine ⟨82721922919311150449723623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110295897225748200599631497 82721922919311150449723623)
  ·
    refine ⟨124082884378966725674585435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82721922919311150449723623 124082884378966725674585435)
    ·
      refine ⟨186124326568450088511878153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124082884378966725674585435 186124326568450088511878153)
      ·
        refine ⟨139593244926337566383908615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186124326568450088511878153 139593244926337566383908615)
        ·
          refine ⟨209389867389506349575862923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139593244926337566383908615 209389867389506349575862923)
          ·
            refine ⟨314084801084259524363794385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209389867389506349575862923 314084801084259524363794385)
            ·
              refine ⟨235563600813194643272845789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314084801084259524363794385 235563600813194643272845789)
              ·
                refine ⟨88336350304947991227317171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235563600813194643272845789 88336350304947991227317171)
                ·
                  refine ⟨132504525457421986840975757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88336350304947991227317171 132504525457421986840975757)
                  ·
                    refine ⟨49689197046533245065365909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132504525457421986840975757 49689197046533245065365909)
                    ·
                      refine ⟨2329181111556245862439027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49689197046533245065365909 2329181111556245862439027)
                      ·
                        rfl

theorem cell23_4536064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_4536064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536064 prefixEnd_4536064 := by exact prefixLift 4536064
  have htrace : WordTrace (prefixWord ++ tailWord_4536064) baseStart_4536064 baseEnd_4536064 := by
    simpa [prefixWord, tailWord_4536064, baseEnd_4536064] using wordTrace_append hprefix tailTrace_4536064
  have hstable : (prefixWord ++ tailWord_4536064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536064).length < 2 ^ (prefixWord ++ tailWord_4536064).sum := by decide
  have hdescent : baseEnd_4536064 < baseStart_4536064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536068 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4536068 : Nat := 118140960795 + 4536068 * 2 ^ 59
def prefixEnd_4536068 : Nat := 4983230072969 + 3 ^ 40 * 4536068 * 2
def baseEnd_4536068 : Nat := 2329183165478863846789009

theorem tailTrace_4536068 : CollatzResearch.WordTrace tailWord_4536068 prefixEnd_4536068 2329183165478863846789009 := by
  unfold tailWord_4536068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82721995865303904791296429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110295994487071873055061905 82721995865303904791296429)
  ·
    refine ⟨31020748449488964296736161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82721995865303904791296429 31020748449488964296736161)
    ·
      refine ⟨23265561337116723222552121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31020748449488964296736161 23265561337116723222552121)
      ·
        refine ⟨17449171002837542416914091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23265561337116723222552121 17449171002837542416914091)
        ·
          refine ⟨26173756504256313625371137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17449171002837542416914091 26173756504256313625371137)
          ·
            refine ⟨19630317378192235219028353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26173756504256313625371137 19630317378192235219028353)
            ·
              refine ⟨14722738033644176414271265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19630317378192235219028353 14722738033644176414271265)
              ·
                refine ⟨11042053525233132310703449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14722738033644176414271265 11042053525233132310703449)
                ·
                  refine ⟨8281540143924849233027587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11042053525233132310703449 8281540143924849233027587)
                  ·
                    refine ⟨12422310215887273849541381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8281540143924849233027587 12422310215887273849541381)
                    ·
                      refine ⟨2329183165478863846789009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12422310215887273849541381 2329183165478863846789009)
                      ·
                        rfl

theorem cell23_4536068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4536068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536068 prefixEnd_4536068 := by exact prefixLift 4536068
  have htrace : WordTrace (prefixWord ++ tailWord_4536068) baseStart_4536068 baseEnd_4536068 := by
    simpa [prefixWord, tailWord_4536068, baseEnd_4536068] using wordTrace_append hprefix tailTrace_4536068
  have hstable : (prefixWord ++ tailWord_4536068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536068).length < 2 ^ (prefixWord ++ tailWord_4536068).sum := by decide
  have hdescent : baseEnd_4536068 < baseStart_4536068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536125 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 6]
def baseStart_4536125 : Nat := 118140960795 + 4536125 * 2 ^ 59
def prefixEnd_4536125 : Nat := 4983230072969 + 3 ^ 40 * 4536125 * 2
def baseEnd_4536125 : Nat := 258801381541796680419583

theorem tailTrace_4536125 : CollatzResearch.WordTrace tailWord_4536125 prefixEnd_4536125 258801381541796680419583 := by
  unfold tailWord_4536125
  simp only [CollatzResearch.WordTrace]
  refine ⟨165446070691401308317417829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110297380460934205544945219 165446070691401308317417829)
  ·
    refine ⟨31021138254637745309515843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165446070691401308317417829 31021138254637745309515843)
    ·
      refine ⟨46531707381956617964273765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31021138254637745309515843 46531707381956617964273765)
      ·
        refine ⟨8724695134116865868301331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46531707381956617964273765 8724695134116865868301331)
        ·
          refine ⟨13087042701175298802451997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724695134116865868301331 13087042701175298802451997)
          ·
            refine ⟨4907641012940737050919499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13087042701175298802451997 4907641012940737050919499)
            ·
              refine ⟨7361461519411105576379249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907641012940737050919499 7361461519411105576379249)
              ·
                refine ⟨5521096139558329182284437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361461519411105576379249 5521096139558329182284437)
                ·
                  refine ⟨258801381541796680419583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5521096139558329182284437 258801381541796680419583)
                  ·
                    rfl

theorem cell23_4536125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_4536125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536125 prefixEnd_4536125 := by exact prefixLift 4536125
  have htrace : WordTrace (prefixWord ++ tailWord_4536125) baseStart_4536125 baseEnd_4536125 := by
    simpa [prefixWord, tailWord_4536125, baseEnd_4536125] using wordTrace_append hprefix tailTrace_4536125
  have hstable : (prefixWord ++ tailWord_4536125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536125).length < 2 ^ (prefixWord ++ tailWord_4536125).sum := by decide
  have hdescent : baseEnd_4536125 < baseStart_4536125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536161 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_4536161 : Nat := 118140960795 + 4536161 * 2 ^ 59
def prefixEnd_4536161 : Nat := 4983230072969 + 3 ^ 40 * 4536161 * 2
def baseEnd_4536161 : Nat := 2329230919179731982926081

theorem tailTrace_4536161 : CollatzResearch.WordTrace tailWord_4536161 prefixEnd_4536161 2329230919179731982926081 := by
  unfold tailWord_4536161
  simp only [CollatzResearch.WordTrace]
  refine ⟨165447383719270886465728337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110298255812847257643818891 165447383719270886465728337)
  ·
    refine ⟨124085537789453164849296253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165447383719270886465728337 124085537789453164849296253)
    ·
      refine ⟨46532076671044936818486095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124085537789453164849296253 46532076671044936818486095)
      ·
        refine ⟨69798115006567405227729143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46532076671044936818486095 69798115006567405227729143)
        ·
          refine ⟨104697172509851107841593715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69798115006567405227729143 104697172509851107841593715)
          ·
            refine ⟨157045758764776661762390573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104697172509851107841593715 157045758764776661762390573)
            ·
              refine ⟨58892159536791248160896465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157045758764776661762390573 58892159536791248160896465)
              ·
                refine ⟨44169119652593436120672349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58892159536791248160896465 44169119652593436120672349)
                ·
                  refine ⟨16563419869722538545252131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44169119652593436120672349 16563419869722538545252131)
                  ·
                    refine ⟨24845129804583807817878197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16563419869722538545252131 24845129804583807817878197)
                    ·
                      refine ⟨2329230919179731982926081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24845129804583807817878197 2329230919179731982926081)
                      ·
                        rfl

theorem cell23_4536161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_4536161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536161 prefixEnd_4536161 := by exact prefixLift 4536161
  have htrace : WordTrace (prefixWord ++ tailWord_4536161) baseStart_4536161 baseEnd_4536161 := by
    simpa [prefixWord, tailWord_4536161, baseEnd_4536161] using wordTrace_append hprefix tailTrace_4536161
  have hstable : (prefixWord ++ tailWord_4536161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536161).length < 2 ^ (prefixWord ++ tailWord_4536161).sum := by decide
  have hdescent : baseEnd_4536161 < baseStart_4536161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536168 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4536168 : Nat := 118140960795 + 4536168 * 2 ^ 59
def prefixEnd_4536168 : Nat := 4983230072969 + 3 ^ 40 * 4536168 * 2
def baseEnd_4536168 : Nat := 776411504514771151846183

theorem tailTrace_4536168 : CollatzResearch.WordTrace tailWord_4536168 prefixEnd_4536168 776411504514771151846183 := by
  unfold tailWord_4536168
  simp only [CollatzResearch.WordTrace]
  refine ⟨82723819515122763330616579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110298426020163684440822105 82723819515122763330616579)
  ·
    refine ⟨124085729272684144995924869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82723819515122763330616579 124085729272684144995924869)
    ·
      refine ⟨23266074238628277186735913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124085729272684144995924869 23266074238628277186735913)
      ·
        refine ⟨17449555678971207890051935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23266074238628277186735913 17449555678971207890051935)
        ·
          refine ⟨26174333518456811835077903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17449555678971207890051935 26174333518456811835077903)
          ·
            refine ⟨39261500277685217752616855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26174333518456811835077903 39261500277685217752616855)
            ·
              refine ⟨58892250416527826628925283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39261500277685217752616855 58892250416527826628925283)
              ·
                refine ⟨88338375624791739943387925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58892250416527826628925283 88338375624791739943387925)
                ·
                  refine ⟨4140861357412112809846309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88338375624791739943387925 4140861357412112809846309)
                  ·
                    refine ⟨776411504514771151846183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140861357412112809846309 776411504514771151846183)
                    ·
                      rfl

theorem cell23_4536168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4536168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536168 prefixEnd_4536168 := by exact prefixLift 4536168
  have htrace : WordTrace (prefixWord ++ tailWord_4536168) baseStart_4536168 baseEnd_4536168 := by
    simpa [prefixWord, tailWord_4536168, baseEnd_4536168] using wordTrace_append hprefix tailTrace_4536168
  have hstable : (prefixWord ++ tailWord_4536168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536168).length < 2 ^ (prefixWord ++ tailWord_4536168).sum := by decide
  have hdescent : baseEnd_4536168 < baseStart_4536168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536171 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_4536171 : Nat := 118140960795 + 4536171 * 2 ^ 59
def prefixEnd_4536171 : Nat := 4983230072969 + 3 ^ 40 * 4536171 * 2
def baseEnd_4536171 : Nat := 2329236053986276943801035

theorem tailTrace_4536171 : CollatzResearch.WordTrace tailWord_4536171 prefixEnd_4536171 2329236053986276943801035 := by
  unfold tailWord_4536171
  simp only [CollatzResearch.WordTrace]
  refine ⟨165447748449234658173592367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110298498966156438782394911 165447748449234658173592367)
  ·
    refine ⟨248171622673851987260388551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165447748449234658173592367 248171622673851987260388551)
    ·
      refine ⟨372257434010777980890582827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248171622673851987260388551 372257434010777980890582827)
      ·
        refine ⟨558386151016166971335874241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372257434010777980890582827 558386151016166971335874241)
        ·
          refine ⟨418789613262125228501905681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558386151016166971335874241 418789613262125228501905681)
          ·
            refine ⟨314092209946593921376429261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418789613262125228501905681 314092209946593921376429261)
            ·
              refine ⟨117784578729972720516160973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314092209946593921376429261 117784578729972720516160973)
              ·
                refine ⟨44169217023739770193560365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117784578729972720516160973 44169217023739770193560365)
                ·
                  refine ⟨16563456383902413822585137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44169217023739770193560365 16563456383902413822585137)
                  ·
                    refine ⟨12422592287926810366938853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16563456383902413822585137 12422592287926810366938853)
                    ·
                      refine ⟨2329236053986276943801035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12422592287926810366938853 2329236053986276943801035)
                      ·
                        rfl

theorem cell23_4536171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_4536171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536171 prefixEnd_4536171 := by exact prefixLift 4536171
  have htrace : WordTrace (prefixWord ++ tailWord_4536171) baseStart_4536171 baseEnd_4536171 := by
    simpa [prefixWord, tailWord_4536171, baseEnd_4536171] using wordTrace_append hprefix tailTrace_4536171
  have hstable : (prefixWord ++ tailWord_4536171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536171).length < 2 ^ (prefixWord ++ tailWord_4536171).sum := by decide
  have hdescent : baseEnd_4536171 < baseStart_4536171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536178 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_4536178 : Nat := 118140960795 + 4536178 * 2 ^ 59
def prefixEnd_4536178 : Nat := 4983230072969 + 3 ^ 40 * 4536178 * 2
def baseEnd_4536178 : Nat := 2329239648350858416413503

theorem tailTrace_4536178 : CollatzResearch.WordTrace tailWord_4536178 prefixEnd_4536178 2329239648350858416413503 := by
  unfold tailWord_4536178
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362000940052324592274297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110298669173472865579398125 41362000940052324592274297)
  ·
    refine ⟨31021500705039243444205723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41362000940052324592274297 31021500705039243444205723)
    ·
      refine ⟨46532251057558865166308585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31021500705039243444205723 46532251057558865166308585)
      ·
        refine ⟨34899188293169148874731439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46532251057558865166308585 34899188293169148874731439)
        ·
          refine ⟨52348782439753723312097159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34899188293169148874731439 52348782439753723312097159)
          ·
            refine ⟨78523173659630584968145739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52348782439753723312097159 78523173659630584968145739)
            ·
              refine ⟨117784760489445877452218609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78523173659630584968145739 117784760489445877452218609)
              ·
                refine ⟨88338570367084408089163957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117784760489445877452218609 88338570367084408089163957)
                ·
                  refine ⟨8281740971914163258359121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88338570367084408089163957 8281740971914163258359121)
                  ·
                    refine ⟨6211305728935622443769341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8281740971914163258359121 6211305728935622443769341)
                    ·
                      refine ⟨2329239648350858416413503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6211305728935622443769341 2329239648350858416413503)
                      ·
                        rfl

theorem cell23_4536178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_4536178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536178 prefixEnd_4536178 := by exact prefixLift 4536178
  have htrace : WordTrace (prefixWord ++ tailWord_4536178) baseStart_4536178 baseEnd_4536178 := by
    simpa [prefixWord, tailWord_4536178, baseEnd_4536178] using wordTrace_append hprefix tailTrace_4536178
  have hstable : (prefixWord ++ tailWord_4536178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536178).length < 2 ^ (prefixWord ++ tailWord_4536178).sum := by decide
  have hdescent : baseEnd_4536178 < baseStart_4536178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536201 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_4536201 : Nat := 118140960795 + 4536201 * 2 ^ 59
def prefixEnd_4536201 : Nat := 4983230072969 + 3 ^ 40 * 4536201 * 2
def baseEnd_4536201 : Nat := 2329251458405911826425897

theorem tailTrace_4536201 : CollatzResearch.WordTrace tailWord_4536201 prefixEnd_4536201 2329251458405911826425897 := by
  unfold tailWord_4536201
  simp only [CollatzResearch.WordTrace]
  refine ⟨165448842639125973297184457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110299228426083982198122971 165448842639125973297184457)
  ·
    refine ⟨124086631979344479972888343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165448842639125973297184457 124086631979344479972888343)
    ·
      refine ⟨186129947969016719959332515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124086631979344479972888343 186129947969016719959332515)
      ·
        refine ⟨279194921953525079938998773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186129947969016719959332515 279194921953525079938998773)
        ·
          refine ⟨26174523933142976244281135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 279194921953525079938998773 26174523933142976244281135)
          ·
            refine ⟨39261785899714464366421703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26174523933142976244281135 39261785899714464366421703)
            ·
              refine ⟨58892678849571696549632555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39261785899714464366421703 58892678849571696549632555)
              ·
                refine ⟨88339018274357544824448833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58892678849571696549632555 88339018274357544824448833)
                ·
                  refine ⟨66254263705768158618336625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88339018274357544824448833 66254263705768158618336625)
                  ·
                    refine ⟨49690697779326118963752469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66254263705768158618336625 49690697779326118963752469)
                    ·
                      refine ⟨2329251458405911826425897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49690697779326118963752469 2329251458405911826425897)
                      ·
                        rfl

theorem cell23_4536201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_4536201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536201 prefixEnd_4536201 := by exact prefixLift 4536201
  have htrace : WordTrace (prefixWord ++ tailWord_4536201) baseStart_4536201 baseEnd_4536201 := by
    simpa [prefixWord, tailWord_4536201, baseEnd_4536201] using wordTrace_append hprefix tailTrace_4536201
  have hstable : (prefixWord ++ tailWord_4536201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536201).length < 2 ^ (prefixWord ++ tailWord_4536201).sum := by decide
  have hdescent : baseEnd_4536201 < baseStart_4536201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536202 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_4536202 : Nat := 118140960795 + 4536202 * 2 ^ 59
def prefixEnd_4536202 : Nat := 4983230072969 + 3 ^ 40 * 4536202 * 2
def baseEnd_4536202 : Nat := 776417323962188774171131

theorem tailTrace_4536202 : CollatzResearch.WordTrace tailWord_4536202 prefixEnd_4536202 776417323962188774171131 := by
  unfold tailWord_4536202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362219778030587616992715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110299252741414900311980573 41362219778030587616992715)
  ·
    refine ⟨62043329667045881425489073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41362219778030587616992715 62043329667045881425489073)
    ·
      refine ⟨46532497250284411069116805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62043329667045881425489073 46532497250284411069116805)
      ·
        refine ⟨8724843234428327075459401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46532497250284411069116805 8724843234428327075459401)
        ·
          refine ⟨6543632425821245306594551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8724843234428327075459401 6543632425821245306594551)
          ·
            refine ⟨9815448638731867959891827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543632425821245306594551 9815448638731867959891827)
            ·
              refine ⟨14723172958097801939837741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9815448638731867959891827 14723172958097801939837741)
              ·
                refine ⟨5521189859286675727439153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14723172958097801939837741 5521189859286675727439153)
                ·
                  refine ⟨4140892394465006795579365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521189859286675727439153 4140892394465006795579365)
                  ·
                    refine ⟨776417323962188774171131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140892394465006795579365 776417323962188774171131)
                    ·
                      rfl

theorem cell23_4536202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_4536202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536202 prefixEnd_4536202 := by exact prefixLift 4536202
  have htrace : WordTrace (prefixWord ++ tailWord_4536202) baseStart_4536202 baseEnd_4536202 := by
    simpa [prefixWord, tailWord_4536202, baseEnd_4536202] using wordTrace_append hprefix tailTrace_4536202
  have hstable : (prefixWord ++ tailWord_4536202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536202).length < 2 ^ (prefixWord ++ tailWord_4536202).sum := by decide
  have hdescent : baseEnd_4536202 < baseStart_4536202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536212 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4536212 : Nat := 118140960795 + 4536212 * 2 ^ 59
def prefixEnd_4536212 : Nat := 4983230072969 + 3 ^ 40 * 4536212 * 2
def baseEnd_4536212 : Nat := 2329257106693111283388347

theorem tailTrace_4536212 : CollatzResearch.WordTrace tailWord_4536212 prefixEnd_4536212 2329257106693111283388347 := by
  unfold tailWord_4536212
  simp only [CollatzResearch.WordTrace]
  refine ⟨82724621921043061087917445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110299495894724081450556593 82724621921043061087917445)
  ·
    refine ⟨15510866610195573953984521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82724621921043061087917445 15510866610195573953984521)
    ·
      refine ⟨11633149957646680465488391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15510866610195573953984521 11633149957646680465488391)
      ·
        refine ⟨17449724936470020698232587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11633149957646680465488391 17449724936470020698232587)
        ·
          refine ⟨26174587404705031047348881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17449724936470020698232587 26174587404705031047348881)
          ·
            refine ⟨19630940553528773285511661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26174587404705031047348881 19630940553528773285511661)
            ·
              refine ⟨7361602707573289982066873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19630940553528773285511661 7361602707573289982066873)
              ·
                refine ⟨5521202030679967486550155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361602707573289982066873 5521202030679967486550155)
                ·
                  refine ⟨8281803046019951229825233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521202030679967486550155 8281803046019951229825233)
                  ·
                    refine ⟨6211352284514963422368925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8281803046019951229825233 6211352284514963422368925)
                    ·
                      refine ⟨2329257106693111283388347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6211352284514963422368925 2329257106693111283388347)
                      ·
                        rfl

theorem cell23_4536212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4536212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536212 prefixEnd_4536212 := by exact prefixLift 4536212
  have htrace : WordTrace (prefixWord ++ tailWord_4536212) baseStart_4536212 baseEnd_4536212 := by
    simpa [prefixWord, tailWord_4536212, baseEnd_4536212] using wordTrace_append hprefix tailTrace_4536212
  have hstable : (prefixWord ++ tailWord_4536212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536212).length < 2 ^ (prefixWord ++ tailWord_4536212).sum := by decide
  have hdescent : baseEnd_4536212 < baseStart_4536212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536251 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_4536251 : Nat := 118140960795 + 4536251 * 2 ^ 59
def prefixEnd_4536251 : Nat := 4983230072969 + 3 ^ 40 * 4536251 * 2
def baseEnd_4536251 : Nat := 2329277132438636630800667

theorem tailTrace_4536251 : CollatzResearch.WordTrace tailWord_4536251 prefixEnd_4536251 2329277132438636630800667 := by
  unfold tailWord_4536251
  simp only [CollatzResearch.WordTrace]
  refine ⟨165450666288944831836504607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110300444192629887891003071 165450666288944831836504607)
  ·
    refine ⟨248175999433417247754756911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165450666288944831836504607 248175999433417247754756911)
    ·
      refine ⟨372263999150125871632135367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248175999433417247754756911 372263999150125871632135367)
      ·
        refine ⟨558395998725188807448203051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372263999150125871632135367 558395998725188807448203051)
        ·
          refine ⟨837593998087783211172304577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558395998725188807448203051 837593998087783211172304577)
          ·
            refine ⟨628195498565837408379228433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837593998087783211172304577 628195498565837408379228433)
            ·
              refine ⟨471146623924378056284421325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628195498565837408379228433 471146623924378056284421325)
              ·
                refine ⟨176679983971641771106657997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471146623924378056284421325 176679983971641771106657997)
                ·
                  refine ⟨66254993989365664164996749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176679983971641771106657997 66254993989365664164996749)
                  ·
                    refine ⟨24845622746012124061873781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66254993989365664164996749 24845622746012124061873781)
                    ·
                      refine ⟨2329277132438636630800667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24845622746012124061873781 2329277132438636630800667)
                      ·
                        rfl

theorem cell23_4536251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_4536251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536251 prefixEnd_4536251 := by exact prefixLift 4536251
  have htrace : WordTrace (prefixWord ++ tailWord_4536251) baseStart_4536251 baseEnd_4536251 := by
    simpa [prefixWord, tailWord_4536251, baseEnd_4536251] using wordTrace_append hprefix tailTrace_4536251
  have hstable : (prefixWord ++ tailWord_4536251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536251).length < 2 ^ (prefixWord ++ tailWord_4536251).sum := by decide
  have hdescent : baseEnd_4536251 < baseStart_4536251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536305 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 7]
def baseStart_4536305 : Nat := 118140960795 + 4536305 * 2 ^ 59
def prefixEnd_4536305 : Nat := 4983230072969 + 3 ^ 40 * 4536305 * 2
def baseEnd_4536305 : Nat := 258811651154886602169491

theorem tailTrace_4536305 : CollatzResearch.WordTrace tailWord_4536305 prefixEnd_4536305 258811651154886602169491 := by
  unfold tailWord_4536305
  simp only [CollatzResearch.WordTrace]
  refine ⟨165452635830749199058970369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110301757220499466039313579 165452635830749199058970369)
  ·
    refine ⟨124089476873061899294227777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165452635830749199058970369 124089476873061899294227777)
    ·
      refine ⟨93067107654796424470670833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124089476873061899294227777 93067107654796424470670833)
      ·
        refine ⟨69800330741097318353003125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93067107654796424470670833 69800330741097318353003125)
        ·
          refine ⟨6543781006977873595594043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69800330741097318353003125 6543781006977873595594043)
          ·
            refine ⟨9815671510466810393391065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543781006977873595594043 9815671510466810393391065)
            ·
              refine ⟨7361753632850107795043299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9815671510466810393391065 7361753632850107795043299)
              ·
                refine ⟨11042630449275161692564949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7361753632850107795043299 11042630449275161692564949)
                ·
                  refine ⟨258811651154886602169491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11042630449275161692564949 258811651154886602169491)
                  ·
                    rfl

theorem cell23_4536305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_4536305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536305 prefixEnd_4536305 := by exact prefixLift 4536305
  have htrace : WordTrace (prefixWord ++ tailWord_4536305) baseStart_4536305 baseEnd_4536305 := by
    simpa [prefixWord, tailWord_4536305, baseEnd_4536305] using wordTrace_append hprefix tailTrace_4536305
  have hstable : (prefixWord ++ tailWord_4536305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536305).length < 2 ^ (prefixWord ++ tailWord_4536305).sum := by decide
  have hdescent : baseEnd_4536305 < baseStart_4536305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536355 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4]
def baseStart_4536355 : Nat := 118140960795 + 4536355 * 2 ^ 59
def prefixEnd_4536355 : Nat := 4983230072969 + 3 ^ 40 * 4536355 * 2
def baseEnd_4536355 : Nat := 2329330534426704223900189

theorem tailTrace_4536355 : CollatzResearch.WordTrace tailWord_4536355 prefixEnd_4536355 2329330534426704223900189 := by
  unfold tailWord_4536355
  simp only [CollatzResearch.WordTrace]
  refine ⟨165454459480568057598290519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110302972987045371732193679 165454459480568057598290519)
  ·
    refine ⟨248181689220852086397435779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165454459480568057598290519 248181689220852086397435779)
    ·
      refine ⟨372272533831278129596153669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248181689220852086397435779 372272533831278129596153669)
      ·
        refine ⟨69801100093364649299278813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372272533831278129596153669 69801100093364649299278813)
        ·
          refine ⟨26175412535011743487229555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69801100093364649299278813 26175412535011743487229555)
          ·
            refine ⟨39263118802517615230844333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26175412535011743487229555 39263118802517615230844333)
            ·
              refine ⟨14723669550944105711566625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39263118802517615230844333 14723669550944105711566625)
              ·
                refine ⟨11042752163208079283674969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14723669550944105711566625 11042752163208079283674969)
                ·
                  refine ⟨8282064122406059462756227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11042752163208079283674969 8282064122406059462756227)
                  ·
                    refine ⟨12423096183609089194134341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8282064122406059462756227 12423096183609089194134341)
                    ·
                      refine ⟨2329330534426704223900189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12423096183609089194134341 2329330534426704223900189)
                      ·
                        rfl

theorem cell23_4536355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_4536355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536355 prefixEnd_4536355 := by exact prefixLift 4536355
  have htrace : WordTrace (prefixWord ++ tailWord_4536355) baseStart_4536355 baseEnd_4536355 := by
    simpa [prefixWord, tailWord_4536355, baseEnd_4536355] using wordTrace_append hprefix tailTrace_4536355
  have hstable : (prefixWord ++ tailWord_4536355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536355).length < 2 ^ (prefixWord ++ tailWord_4536355).sum := by decide
  have hdescent : baseEnd_4536355 < baseStart_4536355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536412 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 6]
def baseStart_4536412 : Nat := 118140960795 + 4536412 * 2 ^ 59
def prefixEnd_4536412 : Nat := 4983230072969 + 3 ^ 40 * 4536412 * 2
def baseEnd_4536412 : Nat := 258817755869334500098603

theorem tailTrace_4536412 : CollatzResearch.WordTrace tailWord_4536412 prefixEnd_4536412 258817755869334500098603 := by
  unfold tailWord_4536412
  simp only [CollatzResearch.WordTrace]
  refine ⟨82728269220680778166557745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110304358960907704222076993 82728269220680778166557745)
  ·
    refine ⟨62046201915510583624918309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82728269220680778166557745 62046201915510583624918309)
    ·
      refine ⟨11633662859158234429672183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62046201915510583624918309 11633662859158234429672183)
      ·
        refine ⟨17450494288737351644508275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11633662859158234429672183 17450494288737351644508275)
        ·
          refine ⟨26175741433106027466762413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17450494288737351644508275 26175741433106027466762413)
          ·
            refine ⟨9815903037414760300035905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26175741433106027466762413 9815903037414760300035905)
            ·
              refine ⟨7361927278061070225026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9815903037414760300035905 7361927278061070225026929)
              ·
                refine ⟨5521445458545802668770197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361927278061070225026929 5521445458545802668770197)
                ·
                  refine ⟨258817755869334500098603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5521445458545802668770197 258817755869334500098603)
                  ·
                    rfl

theorem cell23_4536412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_4536412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536412 prefixEnd_4536412 := by exact prefixLift 4536412
  have htrace : WordTrace (prefixWord ++ tailWord_4536412) baseStart_4536412 baseEnd_4536412 := by
    simpa [prefixWord, tailWord_4536412, baseEnd_4536412] using wordTrace_append hprefix tailTrace_4536412
  have hstable : (prefixWord ++ tailWord_4536412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536412).length < 2 ^ (prefixWord ++ tailWord_4536412).sum := by decide
  have hdescent : baseEnd_4536412 < baseStart_4536412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536416 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 1, 4]
def baseStart_4536416 : Nat := 118140960795 + 4536416 * 2 ^ 59
def prefixEnd_4536416 : Nat := 4983230072969 + 3 ^ 40 * 4536416 * 2
def baseEnd_4536416 : Nat := 776453952248876161745803

theorem tailTrace_4536416 : CollatzResearch.WordTrace tailWord_4536416 prefixEnd_4536416 776453952248876161745803 := by
  unfold tailWord_4536416
  simp only [CollatzResearch.WordTrace]
  refine ⟨82728342166673532508130551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110304456222231376677507401 82728342166673532508130551)
  ·
    refine ⟨124092513250010298762195827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82728342166673532508130551 124092513250010298762195827)
    ·
      refine ⟨186138769875015448143293741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124092513250010298762195827 186138769875015448143293741)
      ·
        refine ⟨69802038703130793053735153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186138769875015448143293741 69802038703130793053735153)
        ·
          refine ⟨52351529027348094790301365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69802038703130793053735153 52351529027348094790301365)
          ·
            refine ⟨4907955846313883886590753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52351529027348094790301365 4907955846313883886590753)
            ·
              refine ⟨3680966884735412914943065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907955846313883886590753 3680966884735412914943065)
              ·
                refine ⟨2760725163551559686207299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680966884735412914943065 2760725163551559686207299)
                ·
                  refine ⟨4141087745327339529310949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760725163551559686207299 4141087745327339529310949)
                  ·
                    refine ⟨776453952248876161745803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141087745327339529310949 776453952248876161745803)
                    ·
                      rfl

theorem cell23_4536416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 4].length) (baseStart_4536416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536416 prefixEnd_4536416 := by exact prefixLift 4536416
  have htrace : WordTrace (prefixWord ++ tailWord_4536416) baseStart_4536416 baseEnd_4536416 := by
    simpa [prefixWord, tailWord_4536416, baseEnd_4536416] using wordTrace_append hprefix tailTrace_4536416
  have hstable : (prefixWord ++ tailWord_4536416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536416).length < 2 ^ (prefixWord ++ tailWord_4536416).sum := by decide
  have hdescent : baseEnd_4536416 < baseStart_4536416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536449 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_4536449 : Nat := 118140960795 + 4536449 * 2 ^ 59
def prefixEnd_4536449 : Nat := 4983230072969 + 3 ^ 40 * 4536449 * 2
def baseEnd_4536449 : Nat := 2329378801608226856124757

theorem tailTrace_4536449 : CollatzResearch.WordTrace tailWord_4536449 prefixEnd_4536449 2329378801608226856124757 := by
  unfold tailWord_4536449
  simp only [CollatzResearch.WordTrace]
  refine ⟨165457887942227511652212401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110305258628151674434808267 165457887942227511652212401)
  ·
    refine ⟨124093415956670633739159301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165457887942227511652212401 124093415956670633739159301)
    ·
      refine ⟨23267515491875743826092369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124093415956670633739159301 23267515491875743826092369)
      ·
        refine ⟨17450636618906807869569277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23267515491875743826092369 17450636618906807869569277)
        ·
          refine ⟨6543988732090052951088479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17450636618906807869569277 6543988732090052951088479)
          ·
            refine ⟨9815983098135079426632719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543988732090052951088479 9815983098135079426632719)
            ·
              refine ⟨14723974647202619139949079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9815983098135079426632719 14723974647202619139949079)
              ·
                refine ⟨22085961970803928709923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14723974647202619139949079 22085961970803928709923619)
                ·
                  refine ⟨33128942956205893064885429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22085961970803928709923619 33128942956205893064885429)
                  ·
                    refine ⟨3105838402144302474833009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33128942956205893064885429 3105838402144302474833009)
                    ·
                      refine ⟨2329378801608226856124757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105838402144302474833009 2329378801608226856124757)
                      ·
                        rfl

theorem cell23_4536449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_4536449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536449 prefixEnd_4536449 := by exact prefixLift 4536449
  have htrace : WordTrace (prefixWord ++ tailWord_4536449) baseStart_4536449 baseEnd_4536449 := by
    simpa [prefixWord, tailWord_4536449, baseEnd_4536449] using wordTrace_append hprefix tailTrace_4536449
  have hstable : (prefixWord ++ tailWord_4536449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536449).length < 2 ^ (prefixWord ++ tailWord_4536449).sum := by decide
  have hdescent : baseEnd_4536449 < baseStart_4536449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536455 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 1, 6]
def baseStart_4536455 : Nat := 118140960795 + 4536455 * 2 ^ 59
def prefixEnd_4536455 : Nat := 4983230072969 + 3 ^ 40 * 4536455 * 2
def baseEnd_4536455 : Nat := 776460627497384610883243

theorem tailTrace_4536455 : CollatzResearch.WordTrace tailWord_4536455 prefixEnd_4536455 776460627497384610883243 := by
  unfold tailWord_4536455
  simp only [CollatzResearch.WordTrace]
  refine ⟨165458106780205774676930819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110305404520137183117953879 165458106780205774676930819)
  ·
    refine ⟨248187160170308662015396229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165458106780205774676930819 248187160170308662015396229)
    ·
      refine ⟨46535092531932874127886793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248187160170308662015396229 46535092531932874127886793)
      ·
        refine ⟨34901319398949655595915095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46535092531932874127886793 34901319398949655595915095)
        ·
          refine ⟨52351979098424483393872643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34901319398949655595915095 52351979098424483393872643)
          ·
            refine ⟨78527968647636725090808965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52351979098424483393872643 78527968647636725090808965)
            ·
              refine ⟨14723994121431885954526681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78527968647636725090808965 14723994121431885954526681)
              ·
                refine ⟨11042995591073914465895011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14723994121431885954526681 11042995591073914465895011)
                ·
                  refine ⟨16564493386610871698842517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11042995591073914465895011 16564493386610871698842517)
                  ·
                    refine ⟨776460627497384610883243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16564493386610871698842517 776460627497384610883243)
                    ·
                      rfl

theorem cell23_4536455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_4536455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536455 prefixEnd_4536455 := by exact prefixLift 4536455
  have htrace : WordTrace (prefixWord ++ tailWord_4536455) baseStart_4536455 baseEnd_4536455 := by
    simpa [prefixWord, tailWord_4536455, baseEnd_4536455] using wordTrace_append hprefix tailTrace_4536455
  have hstable : (prefixWord ++ tailWord_4536455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536455).length < 2 ^ (prefixWord ++ tailWord_4536455).sum := by decide
  have hdescent : baseEnd_4536455 < baseStart_4536455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536456 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4536456 : Nat := 118140960795 + 4536456 * 2 ^ 59
def prefixEnd_4536456 : Nat := 4983230072969 + 3 ^ 40 * 4536456 * 2
def baseEnd_4536456 : Nat := 2329382395972808328737225

theorem tailTrace_4536456 : CollatzResearch.WordTrace tailWord_4536456 prefixEnd_4536456 2329382395972808328737225 := by
  unfold tailWord_4536456
  simp only [CollatzResearch.WordTrace]
  refine ⟨82729071626601075923858611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110305428835468101231811481 82729071626601075923858611)
  ·
    refine ⟨124093607439901613885787917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82729071626601075923858611 124093607439901613885787917)
    ·
      refine ⟨46535102789963105207170469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124093607439901613885787917 46535102789963105207170469)
      ·
        refine ⟨8725331773118082226344463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46535102789963105207170469 8725331773118082226344463)
        ·
          refine ⟨13087997659677123339516695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8725331773118082226344463 13087997659677123339516695)
          ·
            refine ⟨19631996489515685009275043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13087997659677123339516695 19631996489515685009275043)
            ·
              refine ⟨29447994734273527513912565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19631996489515685009275043 29447994734273527513912565)
              ·
                refine ⟨2760749506338143204429303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29447994734273527513912565 2760749506338143204429303)
                ·
                  refine ⟨4141124259507214806643955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760749506338143204429303 4141124259507214806643955)
                  ·
                    refine ⟨6211686389260822209965933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4141124259507214806643955 6211686389260822209965933)
                    ·
                      refine ⟨2329382395972808328737225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6211686389260822209965933 2329382395972808328737225)
                      ·
                        rfl

theorem cell23_4536456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4536456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536456 prefixEnd_4536456 := by exact prefixLift 4536456
  have htrace : WordTrace (prefixWord ++ tailWord_4536456) baseStart_4536456 baseEnd_4536456 := by
    simpa [prefixWord, tailWord_4536456, baseEnd_4536456] using wordTrace_append hprefix tailTrace_4536456
  have hstable : (prefixWord ++ tailWord_4536456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536456).length < 2 ^ (prefixWord ++ tailWord_4536456).sum := by decide
  have hdescent : baseEnd_4536456 < baseStart_4536456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536482 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4536482 : Nat := 118140960795 + 4536482 * 2 ^ 59
def prefixEnd_4536482 : Nat := 4983230072969 + 3 ^ 40 * 4536482 * 2
def baseEnd_4536482 : Nat := 2329395746469825227012105

theorem tailTrace_4536482 : CollatzResearch.WordTrace tailWord_4536482 prefixEnd_4536482 2329395746469825227012105 := by
  unfold tailWord_4536482
  simp only [CollatzResearch.WordTrace]
  refine ⟨41364772887776989572040925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110306061034071972192109133 41364772887776989572040925)
  ·
    refine ⟨15511789832916371089515347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41364772887776989572040925 15511789832916371089515347)
    ·
      refine ⟨23267684749374556634273021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15511789832916371089515347 23267684749374556634273021)
      ·
        refine ⟨8725381781015458737852383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23267684749374556634273021 8725381781015458737852383)
        ·
          refine ⟨13088072671523188106778575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8725381781015458737852383 13088072671523188106778575)
          ·
            refine ⟨19632109007284782160167863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13088072671523188106778575 19632109007284782160167863)
            ·
              refine ⟨29448163510927173240251795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19632109007284782160167863 29448163510927173240251795)
              ·
                refine ⟨44172245266390759860377693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29448163510927173240251795 44172245266390759860377693)
                ·
                  refine ⟨16564591974896534947641635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44172245266390759860377693 16564591974896534947641635)
                  ·
                    refine ⟨24846887962344802421462453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16564591974896534947641635 24846887962344802421462453)
                    ·
                      refine ⟨2329395746469825227012105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24846887962344802421462453 2329395746469825227012105)
                      ·
                        rfl

theorem cell23_4536482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4536482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536482 prefixEnd_4536482 := by exact prefixLift 4536482
  have htrace : WordTrace (prefixWord ++ tailWord_4536482) baseStart_4536482 baseEnd_4536482 := by
    simpa [prefixWord, tailWord_4536482, baseEnd_4536482] using wordTrace_append hprefix tailTrace_4536482
  have hstable : (prefixWord ++ tailWord_4536482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536482).length < 2 ^ (prefixWord ++ tailWord_4536482).sum := by decide
  have hdescent : baseEnd_4536482 < baseStart_4536482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536530 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4536530 : Nat := 118140960795 + 4536530 * 2 ^ 59
def prefixEnd_4536530 : Nat := 4983230072969 + 3 ^ 40 * 4536530 * 2
def baseEnd_4536530 : Nat := 2329420393541241039211885

theorem tailTrace_4536530 : CollatzResearch.WordTrace tailWord_4536530 prefixEnd_4536530 2329420393541241039211885 := by
  unfold tailWord_4536530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41365210563733515621477761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110307228169956041657274029 41365210563733515621477761)
  ·
    refine ⟨31023907922800136716108321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41365210563733515621477761 31023907922800136716108321)
    ·
      refine ⟨23267930942100102537081241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31023907922800136716108321 23267930942100102537081241)
      ·
        refine ⟨17450948206575076902810931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23267930942100102537081241 17450948206575076902810931)
        ·
          refine ⟨26176422309862615354216397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17450948206575076902810931 26176422309862615354216397)
          ·
            refine ⟨9816158366198480757831149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26176422309862615354216397 9816158366198480757831149)
            ·
              refine ⟨3681059387324430284186681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9816158366198480757831149 3681059387324430284186681)
              ·
                refine ⟨2760794540493322713140011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3681059387324430284186681 2760794540493322713140011)
                ·
                  refine ⟨4141191810739984069710017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760794540493322713140011 4141191810739984069710017)
                  ·
                    refine ⟨3105893858054988052282513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141191810739984069710017 3105893858054988052282513)
                    ·
                      refine ⟨2329420393541241039211885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105893858054988052282513 2329420393541241039211885)
                      ·
                        rfl

theorem cell23_4536530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4536530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536530 prefixEnd_4536530 := by exact prefixLift 4536530
  have htrace : WordTrace (prefixWord ++ tailWord_4536530) baseStart_4536530 baseEnd_4536530 := by
    simpa [prefixWord, tailWord_4536530, baseEnd_4536530] using wordTrace_append hprefix tailTrace_4536530
  have hstable : (prefixWord ++ tailWord_4536530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536530).length < 2 ^ (prefixWord ++ tailWord_4536530).sum := by decide
  have hdescent : baseEnd_4536530 < baseStart_4536530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536535 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_4536535 : Nat := 118140960795 + 4536535 * 2 ^ 59
def prefixEnd_4536535 : Nat := 4983230072969 + 3 ^ 40 * 4536535 * 2
def baseEnd_4536535 : Nat := 2329422960944513519649361

theorem tailTrace_4536535 : CollatzResearch.WordTrace tailWord_4536535 prefixEnd_4536535 2329422960944513519649361 := by
  unfold tailWord_4536535
  simp only [CollatzResearch.WordTrace]
  refine ⟨165461024619915948339843059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110307349746610632226562039 165461024619915948339843059)
  ·
    refine ⟨248191536929873922509764589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165461024619915948339843059 248191536929873922509764589)
    ·
      refine ⟨93071826348702720941161721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248191536929873922509764589 93071826348702720941161721)
      ·
        refine ⟨69803869761527040705871291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93071826348702720941161721 69803869761527040705871291)
        ·
          refine ⟨104705804642290561058806937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69803869761527040705871291 104705804642290561058806937)
          ·
            refine ⟨78529353481717920794105203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104705804642290561058806937 78529353481717920794105203)
            ·
              refine ⟨117794030222576881191157805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78529353481717920794105203 117794030222576881191157805)
              ·
                refine ⟨44172761333466330446684177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117794030222576881191157805 44172761333466330446684177)
                ·
                  refine ⟨33129571000099747835013133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44172761333466330446684177 33129571000099747835013133)
                  ·
                    refine ⟨12423589125037405438129925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33129571000099747835013133 12423589125037405438129925)
                    ·
                      refine ⟨2329422960944513519649361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12423589125037405438129925 2329422960944513519649361)
                      ·
                        rfl

theorem cell23_4536535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_4536535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536535 prefixEnd_4536535 := by exact prefixLift 4536535
  have htrace : WordTrace (prefixWord ++ tailWord_4536535) baseStart_4536535 baseEnd_4536535 := by
    simpa [prefixWord, tailWord_4536535, baseEnd_4536535] using wordTrace_append hprefix tailTrace_4536535
  have hstable : (prefixWord ++ tailWord_4536535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536535).length < 2 ^ (prefixWord ++ tailWord_4536535).sum := by decide
  have hdescent : baseEnd_4536535 < baseStart_4536535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536540 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4536540 : Nat := 118140960795 + 4536540 * 2 ^ 59
def prefixEnd_4536540 : Nat := 4983230072969 + 3 ^ 40 * 4536540 * 2
def baseEnd_4536540 : Nat := 776475176115928666695613

theorem tailTrace_4536540 : CollatzResearch.WordTrace tailWord_4536540 prefixEnd_4536540 776475176115928666695613 := by
  unfold tailWord_4536540
  simp only [CollatzResearch.WordTrace]
  refine ⟨82730603492448917096887537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110307471323265222795850049 82730603492448917096887537)
  ·
    refine ⟨62047952619336687822665653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82730603492448917096887537 62047952619336687822665653)
    ·
      refine ⟨5816995558062814483374905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62047952619336687822665653 5816995558062814483374905)
      ·
        refine ⟨4362746668547110862531179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5816995558062814483374905 4362746668547110862531179)
        ·
          refine ⟨6544120002820666293796769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362746668547110862531179 6544120002820666293796769)
          ·
            refine ⟨4908090002115499720347577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6544120002820666293796769 4908090002115499720347577)
            ·
              refine ⟨3681067501586624790260683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4908090002115499720347577 3681067501586624790260683)
              ·
                refine ⟨5521601252379937185391025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681067501586624790260683 5521601252379937185391025)
                ·
                  refine ⟨4141200939284952889043269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521601252379937185391025 4141200939284952889043269)
                  ·
                    refine ⟨776475176115928666695613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141200939284952889043269 776475176115928666695613)
                    ·
                      rfl

theorem cell23_4536540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4536540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536540 prefixEnd_4536540 := by exact prefixLift 4536540
  have htrace : WordTrace (prefixWord ++ tailWord_4536540) baseStart_4536540 baseEnd_4536540 := by
    simpa [prefixWord, tailWord_4536540, baseEnd_4536540] using wordTrace_append hprefix tailTrace_4536540
  have hstable : (prefixWord ++ tailWord_4536540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536540).length < 2 ^ (prefixWord ++ tailWord_4536540).sum := by decide
  have hdescent : baseEnd_4536540 < baseStart_4536540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536545 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_4536545 : Nat := 118140960795 + 4536545 * 2 ^ 59
def prefixEnd_4536545 : Nat := 4983230072969 + 3 ^ 40 * 4536545 * 2
def baseEnd_4536545 : Nat := 776476031917019493508105

theorem tailTrace_4536545 : CollatzResearch.WordTrace tailWord_4536545 prefixEnd_4536545 776476031917019493508105 := by
  unfold tailWord_4536545
  simp only [CollatzResearch.WordTrace]
  refine ⟨165461389349879720047707089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110307592899919813365138059 165461389349879720047707089)
  ·
    refine ⟨124096042012409790035780317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165461389349879720047707089 124096042012409790035780317)
    ·
      refine ⟨46536015754653671263417619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124096042012409790035780317 46536015754653671263417619)
      ·
        refine ⟨69804023631980506895126429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46536015754653671263417619 69804023631980506895126429)
        ·
          refine ⟨26176508861992690085672411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69804023631980506895126429 26176508861992690085672411)
          ·
            refine ⟨39264763292989035128508617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26176508861992690085672411 39264763292989035128508617)
            ·
              refine ⟨29448572469741776346381463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39264763292989035128508617 29448572469741776346381463)
              ·
                refine ⟨44172858704612664519572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29448572469741776346381463 44172858704612664519572195)
                ·
                  refine ⟨66259288056918996779358293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44172858704612664519572195 66259288056918996779358293)
                  ·
                    refine ⟨776476031917019493508105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66259288056918996779358293 776476031917019493508105)
                    ·
                      rfl

theorem cell23_4536545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_4536545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536545 prefixEnd_4536545 := by exact prefixLift 4536545
  have htrace : WordTrace (prefixWord ++ tailWord_4536545) baseStart_4536545 baseEnd_4536545 := by
    simpa [prefixWord, tailWord_4536545, baseEnd_4536545] using wordTrace_append hprefix tailTrace_4536545
  have hstable : (prefixWord ++ tailWord_4536545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536545).length < 2 ^ (prefixWord ++ tailWord_4536545).sum := by decide
  have hdescent : baseEnd_4536545 < baseStart_4536545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536555 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_4536555 : Nat := 118140960795 + 4536555 * 2 ^ 59
def prefixEnd_4536555 : Nat := 4983230072969 + 3 ^ 40 * 4536555 * 2
def baseEnd_4536555 : Nat := 2329433230557603441399269

theorem tailTrace_4536555 : CollatzResearch.WordTrace tailWord_4536555 prefixEnd_4536555 2329433230557603441399269 := by
  unfold tailWord_4536555
  simp only [CollatzResearch.WordTrace]
  refine ⟨165461754079843491755571119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110307836053228994503714079 165461754079843491755571119)
  ·
    refine ⟨248192631119765237633356679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165461754079843491755571119 248192631119765237633356679)
    ·
      refine ⟨372288946679647856450035019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248192631119765237633356679 372288946679647856450035019)
      ·
        refine ⟨558433420019471784675052529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372288946679647856450035019 558433420019471784675052529)
        ·
          refine ⟨418825065014603838506289397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558433420019471784675052529 418825065014603838506289397)
          ·
            refine ⟨39264849845119109859964631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 418825065014603838506289397 39264849845119109859964631)
            ·
              refine ⟨58897274767678664789946947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39264849845119109859964631 58897274767678664789946947)
              ·
                refine ⟨88345912151517997184920421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58897274767678664789946947 88345912151517997184920421)
                ·
                  refine ⟨16564858528409624472172579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88345912151517997184920421 16564858528409624472172579)
                  ·
                    refine ⟨24847287792614436708258869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16564858528409624472172579 24847287792614436708258869)
                    ·
                      refine ⟨2329433230557603441399269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24847287792614436708258869 2329433230557603441399269)
                      ·
                        rfl

theorem cell23_4536555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_4536555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536555 prefixEnd_4536555 := by exact prefixLift 4536555
  have htrace : WordTrace (prefixWord ++ tailWord_4536555) baseStart_4536555 baseEnd_4536555 := by
    simpa [prefixWord, tailWord_4536555, baseEnd_4536555] using wordTrace_append hprefix tailTrace_4536555
  have hstable : (prefixWord ++ tailWord_4536555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536555).length < 2 ^ (prefixWord ++ tailWord_4536555).sum := by decide
  have hdescent : baseEnd_4536555 < baseStart_4536555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536569 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 4, 2, 2]
def baseStart_4536569 : Nat := 118140960795 + 4536569 * 2 ^ 59
def prefixEnd_4536569 : Nat := 4983230072969 + 3 ^ 40 * 4536569 * 2
def baseEnd_4536569 : Nat := 2329440419286766386624205

theorem tailTrace_4536569 : CollatzResearch.WordTrace tailWord_4536569 prefixEnd_4536569 2329440419286766386624205 := by
  unfold tailWord_4536569
  simp only [CollatzResearch.WordTrace]
  refine ⟨165462264701792772146580761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110308176467861848097720507 165462264701792772146580761)
  ·
    refine ⟨124096698526344579109935571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165462264701792772146580761 124096698526344579109935571)
    ·
      refine ⟨186145047789516868664903357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124096698526344579109935571 186145047789516868664903357)
      ·
        refine ⟨69804392921068825749338759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186145047789516868664903357 69804392921068825749338759)
        ·
          refine ⟨104706589381603238624008139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69804392921068825749338759 104706589381603238624008139)
          ·
            refine ⟨157059884072404857936012209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104706589381603238624008139 157059884072404857936012209)
            ·
              refine ⟨117794913054303643452009157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157059884072404857936012209 117794913054303643452009157)
              ·
                refine ⟨22086546197681933147251717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117794913054303643452009157 22086546197681933147251717)
                ·
                  refine ⟨4141227412065362465109697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22086546197681933147251717 4141227412065362465109697)
                  ·
                    refine ⟨3105920559049021848832273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141227412065362465109697 3105920559049021848832273)
                    ·
                      refine ⟨2329440419286766386624205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105920559049021848832273 2329440419286766386624205)
                      ·
                        rfl

theorem cell23_4536569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_4536569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536569 prefixEnd_4536569 := by exact prefixLift 4536569
  have htrace : WordTrace (prefixWord ++ tailWord_4536569) baseStart_4536569 baseEnd_4536569 := by
    simpa [prefixWord, tailWord_4536569, baseEnd_4536569] using wordTrace_append hprefix tailTrace_4536569
  have hstable : (prefixWord ++ tailWord_4536569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536569).length < 2 ^ (prefixWord ++ tailWord_4536569).sum := by decide
  have hdescent : baseEnd_4536569 < baseStart_4536569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536572 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_4536572 : Nat := 118140960795 + 4536572 * 2 ^ 59
def prefixEnd_4536572 : Nat := 4983230072969 + 3 ^ 40 * 4536572 * 2
def baseEnd_4536572 : Nat := 2329441959728729874886691

theorem tailTrace_4536572 : CollatzResearch.WordTrace tailWord_4536572 prefixEnd_4536572 2329441959728729874886691 := by
  unfold tailWord_4536572
  simp only [CollatzResearch.WordTrace]
  refine ⟨82731187060390951829469985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110308249413854602439293313 82731187060390951829469985)
  ·
    refine ⟨62048390295293213872102489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82731187060390951829469985 62048390295293213872102489)
    ·
      refine ⟨46536292721469910404076867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62048390295293213872102489 46536292721469910404076867)
      ·
        refine ⟨69804439082204865606115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46536292721469910404076867 69804439082204865606115301)
        ·
          refine ⟨13088332327913412301146619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69804439082204865606115301 13088332327913412301146619)
          ·
            refine ⟨19632498491870118451719929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13088332327913412301146619 19632498491870118451719929)
            ·
              refine ⟨14724373868902588838789947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19632498491870118451719929 14724373868902588838789947)
              ·
                refine ⟨22086560803353883258184921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14724373868902588838789947 22086560803353883258184921)
                ·
                  refine ⟨16564920602515412443638691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22086560803353883258184921 16564920602515412443638691)
                  ·
                    refine ⟨24847380903773118665458037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16564920602515412443638691 24847380903773118665458037)
                    ·
                      refine ⟨2329441959728729874886691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24847380903773118665458037 2329441959728729874886691)
                      ·
                        rfl

theorem cell23_4536572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_4536572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536572 prefixEnd_4536572 := by exact prefixLift 4536572
  have htrace : WordTrace (prefixWord ++ tailWord_4536572) baseStart_4536572 baseEnd_4536572 := by
    simpa [prefixWord, tailWord_4536572, baseEnd_4536572] using wordTrace_append hprefix tailTrace_4536572
  have hstable : (prefixWord ++ tailWord_4536572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536572).length < 2 ^ (prefixWord ++ tailWord_4536572).sum := by decide
  have hdescent : baseEnd_4536572 < baseStart_4536572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536586 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_4536586 : Nat := 118140960795 + 4536586 * 2 ^ 59
def prefixEnd_4536586 : Nat := 4983230072969 + 3 ^ 40 * 4536586 * 2
def baseEnd_4536586 : Nat := 2329449148457892820111627

theorem tailTrace_4536586 : CollatzResearch.WordTrace tailWord_4536586 prefixEnd_4536586 2329449148457892820111627 := by
  unfold tailWord_4536586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41365721185682796012487403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110308589828487456033299741 41365721185682796012487403)
  ·
    refine ⟨62048581778524194018731105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41365721185682796012487403 62048581778524194018731105)
    ·
      refine ⟨46536436333893145514048329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62048581778524194018731105 46536436333893145514048329)
      ·
        refine ⟨34902327250419859135536247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46536436333893145514048329 34902327250419859135536247)
        ·
          refine ⟨52353490875629788703304371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34902327250419859135536247 52353490875629788703304371)
          ·
            refine ⟨78530236313444683054956557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52353490875629788703304371 78530236313444683054956557)
            ·
              refine ⟨29448838617541756145608709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78530236313444683054956557 29448838617541756145608709)
              ·
                refine ⟨5521657240789079277301633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29448838617541756145608709 5521657240789079277301633)
                ·
                  refine ⟨4141242930591809457976225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521657240789079277301633 4141242930591809457976225)
                  ·
                    refine ⟨3105932197943857093482169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141242930591809457976225 3105932197943857093482169)
                    ·
                      refine ⟨2329449148457892820111627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105932197943857093482169 2329449148457892820111627)
                      ·
                        rfl

theorem cell23_4536586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_4536586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536586 prefixEnd_4536586 := by exact prefixLift 4536586
  have htrace : WordTrace (prefixWord ++ tailWord_4536586) baseStart_4536586 baseEnd_4536586 := by
    simpa [prefixWord, tailWord_4536586, baseEnd_4536586] using wordTrace_append hprefix tailTrace_4536586
  have hstable : (prefixWord ++ tailWord_4536586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536586).length < 2 ^ (prefixWord ++ tailWord_4536586).sum := by decide
  have hdescent : baseEnd_4536586 < baseStart_4536586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536626 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_4536626 : Nat := 118140960795 + 4536626 * 2 ^ 59
def prefixEnd_4536626 : Nat := 4983230072969 + 3 ^ 40 * 4536626 * 2
def baseEnd_4536626 : Nat := 258829965298230295956827

theorem tailTrace_4536626 : CollatzResearch.WordTrace tailWord_4536626 prefixEnd_4536626 258829965298230295956827 := by
  unfold tailWord_4536626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41366085915646567720351433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110309562441724180587603821 41366085915646567720351433)
  ·
    refine ⟨31024564436734925790263575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41366085915646567720351433 31024564436734925790263575)
    ·
      refine ⟨46536846655102388685395363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31024564436734925790263575 46536846655102388685395363)
      ·
        refine ⟨69805269982653583028093045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46536846655102388685395363 69805269982653583028093045)
        ·
          refine ⟨6544244060873773408883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69805269982653583028093045 6544244060873773408883723)
          ·
            refine ⟨9816366091310660113325585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6544244060873773408883723 9816366091310660113325585)
            ·
              refine ⟨7362274568482995084994189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9816366091310660113325585 7362274568482995084994189)
              ·
                refine ⟨2760852963181123156872821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7362274568482995084994189 2760852963181123156872821)
                ·
                  refine ⟨258829965298230295956827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760852963181123156872821 258829965298230295956827)
                  ·
                    rfl

theorem cell23_4536626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_4536626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536626 prefixEnd_4536626 := by exact prefixLift 4536626
  have htrace : WordTrace (prefixWord ++ tailWord_4536626) baseStart_4536626 baseEnd_4536626 := by
    simpa [prefixWord, tailWord_4536626, baseEnd_4536626] using wordTrace_append hprefix tailTrace_4536626
  have hstable : (prefixWord ++ tailWord_4536626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536626).length < 2 ^ (prefixWord ++ tailWord_4536626).sum := by decide
  have hdescent : baseEnd_4536626 < baseStart_4536626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536679 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_4536679 : Nat := 118140960795 + 4536679 * 2 ^ 59
def prefixEnd_4536679 : Nat := 4983230072969 + 3 ^ 40 * 4536679 * 2
def baseEnd_4536679 : Nat := 2329496902158760956248699

theorem tailTrace_4536679 : CollatzResearch.WordTrace tailWord_4536679 prefixEnd_4536679 2329496902158760956248699 := by
  unfold tailWord_4536679
  simp only [CollatzResearch.WordTrace]
  refine ⟨165466276731394260933085091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110310851154262840622056727 165466276731394260933085091)
  ·
    refine ⟨248199415097091391399627637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165466276731394260933085091 248199415097091391399627637)
    ·
      refine ⟨23268695165352317943715091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 248199415097091391399627637 23268695165352317943715091)
      ·
        refine ⟨34903042748028476915572637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23268695165352317943715091 34903042748028476915572637)
        ·
          refine ⟨13088641030510678843339739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34903042748028476915572637 13088641030510678843339739)
          ·
            refine ⟨19632961545766018265009609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13088641030510678843339739 19632961545766018265009609)
            ·
              refine ⟨14724721159324513698757207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19632961545766018265009609 14724721159324513698757207)
              ·
                refine ⟨22087081738986770548135811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14724721159324513698757207 22087081738986770548135811)
                ·
                  refine ⟨33130622608480155822203717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22087081738986770548135811 33130622608480155822203717)
                  ·
                    refine ⟨6211991739090029216663197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33130622608480155822203717 6211991739090029216663197)
                    ·
                      refine ⟨2329496902158760956248699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6211991739090029216663197 2329496902158760956248699)
                      ·
                        rfl

theorem cell23_4536679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_4536679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536679 prefixEnd_4536679 := by exact prefixLift 4536679
  have htrace : WordTrace (prefixWord ++ tailWord_4536679) baseStart_4536679 baseEnd_4536679 := by
    simpa [prefixWord, tailWord_4536679, baseEnd_4536679] using wordTrace_append hprefix tailTrace_4536679
  have hstable : (prefixWord ++ tailWord_4536679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536679).length < 2 ^ (prefixWord ++ tailWord_4536679).sum := by decide
  have hdescent : baseEnd_4536679 < baseStart_4536679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536716 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 6]
def baseStart_4536716 : Nat := 118140960795 + 4536716 * 2 ^ 59
def prefixEnd_4536716 : Nat := 4983230072969 + 3 ^ 40 * 4536716 * 2
def baseEnd_4536716 : Nat := 258835100104775256831781

theorem tailTrace_4536716 : CollatzResearch.WordTrace tailWord_4536716 prefixEnd_4536716 258835100104775256831781 := by
  unfold tailWord_4536716
  simp only [CollatzResearch.WordTrace]
  refine ⟨82733813116130108126091001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110311750821506810834788001 82733813116130108126091001)
  ·
    refine ⟨62050359837097581094568251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82733813116130108126091001 62050359837097581094568251)
    ·
      refine ⟨93075539755646371641852377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62050359837097581094568251 93075539755646371641852377)
      ·
        refine ⟨69806654816734778731389283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93075539755646371641852377 69806654816734778731389283)
        ·
          refine ⟨104709982225102168097083925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69806654816734778731389283 104709982225102168097083925)
          ·
            refine ⟨4908280416801664129550809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104709982225102168097083925 4908280416801664129550809)
            ·
              refine ⟨3681210312601248097163107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4908280416801664129550809 3681210312601248097163107)
              ·
                refine ⟨5521815468901872145744661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681210312601248097163107 5521815468901872145744661)
                ·
                  refine ⟨258835100104775256831781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5521815468901872145744661 258835100104775256831781)
                  ·
                    rfl

theorem cell23_4536716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_4536716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536716 prefixEnd_4536716 := by exact prefixLift 4536716
  have htrace : WordTrace (prefixWord ++ tailWord_4536716) baseStart_4536716 baseEnd_4536716 := by
    simpa [prefixWord, tailWord_4536716, baseEnd_4536716] using wordTrace_append hprefix tailTrace_4536716
  have hstable : (prefixWord ++ tailWord_4536716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536716).length < 2 ^ (prefixWord ++ tailWord_4536716).sum := by decide
  have hdescent : baseEnd_4536716 < baseStart_4536716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536736 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2]
def baseStart_4536736 : Nat := 118140960795 + 4536736 * 2 ^ 59
def prefixEnd_4536736 : Nat := 4983230072969 + 3 ^ 40 * 4536736 * 2
def baseEnd_4536736 : Nat := 2329526170556067233235937

theorem tailTrace_4536736 : CollatzResearch.WordTrace tailWord_4536736 prefixEnd_4536736 2329526170556067233235937 := by
  unfold tailWord_4536736
  simp only [CollatzResearch.WordTrace]
  refine ⟨82734177846093879833955031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110312237128125173111940041 82734177846093879833955031)
  ·
    refine ⟨124101266769140819750932547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82734177846093879833955031 124101266769140819750932547)
    ·
      refine ⟨186151900153711229626398821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124101266769140819750932547 186151900153711229626398821)
      ·
        refine ⟨34903481278820855554949779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186151900153711229626398821 34903481278820855554949779)
        ·
          refine ⟨52355221918231283332424669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34903481278820855554949779 52355221918231283332424669)
          ·
            refine ⟨19633208219336731249659251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52355221918231283332424669 19633208219336731249659251)
            ·
              refine ⟨29449812329005096874488877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19633208219336731249659251 29449812329005096874488877)
              ·
                refine ⟨11043679623376911327933329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29449812329005096874488877 11043679623376911327933329)
                ·
                  refine ⟨8282759717532683495949997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11043679623376911327933329 8282759717532683495949997)
                  ·
                    refine ⟨3106034894074756310981249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8282759717532683495949997 3106034894074756310981249)
                    ·
                      refine ⟨2329526170556067233235937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106034894074756310981249 2329526170556067233235937)
                      ·
                        rfl

theorem cell23_4536736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_4536736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536736 prefixEnd_4536736 := by exact prefixLift 4536736
  have htrace : WordTrace (prefixWord ++ tailWord_4536736) baseStart_4536736 baseEnd_4536736 := by
    simpa [prefixWord, tailWord_4536736, baseEnd_4536736] using wordTrace_append hprefix tailTrace_4536736
  have hstable : (prefixWord ++ tailWord_4536736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536736).length < 2 ^ (prefixWord ++ tailWord_4536736).sum := by decide
  have hdescent : baseEnd_4536736 < baseStart_4536736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536762 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_4536762 : Nat := 118140960795 + 4536762 * 2 ^ 59
def prefixEnd_4536762 : Nat := 4983230072969 + 3 ^ 40 * 4536762 * 2
def baseEnd_4536762 : Nat := 2329539521053084131510817

theorem tailTrace_4536762 : CollatzResearch.WordTrace tailWord_4536762 prefixEnd_4536762 2329539521053084131510817 := by
  unfold tailWord_4536762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41367325997523391527089135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110312869326729044072237693 41367325997523391527089135)
  ·
    refine ⟨62050988996285087290633703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41367325997523391527089135 62050988996285087290633703)
    ·
      refine ⟨93076483494427630935950555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62050988996285087290633703 93076483494427630935950555)
      ·
        refine ⟨139614725241641446403925833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93076483494427630935950555 139614725241641446403925833)
        ·
          refine ⟨104711043931231084802944375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139614725241641446403925833 104711043931231084802944375)
          ·
            refine ⟨157066565896846627204416563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104711043931231084802944375 157066565896846627204416563)
            ·
              refine ⟨235599848845269940806624845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157066565896846627204416563 235599848845269940806624845)
              ·
                refine ⟨88349943316976227802484317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235599848845269940806624845 88349943316976227802484317)
                ·
                  refine ⟨33131228743866085425931619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88349943316976227802484317 33131228743866085425931619)
                  ·
                    refine ⟨49696843115799128138897429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33131228743866085425931619 49696843115799128138897429)
                    ·
                      refine ⟨2329539521053084131510817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49696843115799128138897429 2329539521053084131510817)
                      ·
                        rfl

theorem cell23_4536762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_4536762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536762 prefixEnd_4536762 := by exact prefixLift 4536762
  have htrace : WordTrace (prefixWord ++ tailWord_4536762) baseStart_4536762 baseEnd_4536762 := by
    simpa [prefixWord, tailWord_4536762, baseEnd_4536762] using wordTrace_append hprefix tailTrace_4536762
  have hstable : (prefixWord ++ tailWord_4536762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536762).length < 2 ^ (prefixWord ++ tailWord_4536762).sum := by decide
  have hdescent : baseEnd_4536762 < baseStart_4536762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536776 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_4536776 : Nat := 118140960795 + 4536776 * 2 ^ 59
def prefixEnd_4536776 : Nat := 4983230072969 + 3 ^ 40 * 4536776 * 2
def baseEnd_4536776 : Nat := 776515569927415692245251

theorem tailTrace_4536776 : CollatzResearch.WordTrace tailWord_4536776 prefixEnd_4536776 776515569927415692245251 := by
  unfold tailWord_4536776
  simp only [CollatzResearch.WordTrace]
  refine ⟨82734907306021423249683091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110313209741361897666244121 82734907306021423249683091)
  ·
    refine ⟨124102360959032134874524637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82734907306021423249683091 124102360959032134874524637)
    ·
      refine ⟨46538385359637050577946739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124102360959032134874524637 46538385359637050577946739)
      ·
        refine ⟨69807578039455575866920109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46538385359637050577946739 69807578039455575866920109)
        ·
          refine ⟨26177841764795840950095041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69807578039455575866920109 26177841764795840950095041)
          ·
            refine ⟨19633381323596880712571281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26177841764795840950095041 19633381323596880712571281)
            ·
              refine ⟨14725035992697660534428461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19633381323596880712571281 14725035992697660534428461)
              ·
                refine ⟨5521888497261622700410673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14725035992697660534428461 5521888497261622700410673)
                ·
                  refine ⟨4141416372946217025308005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521888497261622700410673 4141416372946217025308005)
                  ·
                    refine ⟨776515569927415692245251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141416372946217025308005 776515569927415692245251)
                    ·
                      rfl

theorem cell23_4536776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_4536776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536776 prefixEnd_4536776 := by exact prefixLift 4536776
  have htrace : WordTrace (prefixWord ++ tailWord_4536776) baseStart_4536776 baseEnd_4536776 := by
    simpa [prefixWord, tailWord_4536776, baseEnd_4536776] using wordTrace_append hprefix tailTrace_4536776
  have hstable : (prefixWord ++ tailWord_4536776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536776).length < 2 ^ (prefixWord ++ tailWord_4536776).sum := by decide
  have hdescent : baseEnd_4536776 < baseStart_4536776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536800 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 1, 2, 2]
def baseStart_4536800 : Nat := 118140960795 + 4536800 * 2 ^ 59
def prefixEnd_4536800 : Nat := 4983230072969 + 3 ^ 40 * 4536800 * 2
def baseEnd_4536800 : Nat := 2329559033317954982835643

theorem tailTrace_4536800 : CollatzResearch.WordTrace tailWord_4536800 prefixEnd_4536800 2329559033317954982835643 := by
  unfold tailWord_4536800
  simp only [CollatzResearch.WordTrace]
  refine ⟨82735344981977949299119927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110313793309303932398826569 82735344981977949299119927)
  ·
    refine ⟨124103017472966923948679891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82735344981977949299119927 124103017472966923948679891)
    ·
      refine ⟨186154526209450385923019837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124103017472966923948679891 186154526209450385923019837)
      ·
        refine ⟨69807947328543894721132439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186154526209450385923019837 69807947328543894721132439)
        ·
          refine ⟨104711920992815842081698659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69807947328543894721132439 104711920992815842081698659)
          ·
            refine ⟨157067881489223763122547989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104711920992815842081698659 157067881489223763122547989)
            ·
              refine ⟨7362556944807363896369437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157067881489223763122547989 7362556944807363896369437)
              ·
                refine ⟨2760958854302761461138539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7362556944807363896369437 2760958854302761461138539)
                ·
                  refine ⟨4141438281454142191707809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760958854302761461138539 4141438281454142191707809)
                  ·
                    refine ⟨3106078711090606643780857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141438281454142191707809 3106078711090606643780857)
                    ·
                      refine ⟨2329559033317954982835643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106078711090606643780857 2329559033317954982835643)
                      ·
                        rfl

theorem cell23_4536800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_4536800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536800 prefixEnd_4536800 := by exact prefixLift 4536800
  have htrace : WordTrace (prefixWord ++ tailWord_4536800) baseStart_4536800 baseEnd_4536800 := by
    simpa [prefixWord, tailWord_4536800, baseEnd_4536800] using wordTrace_append hprefix tailTrace_4536800
  have hstable : (prefixWord ++ tailWord_4536800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536800).length < 2 ^ (prefixWord ++ tailWord_4536800).sum := by decide
  have hdescent : baseEnd_4536800 < baseStart_4536800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536803 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4536803 : Nat := 118140960795 + 4536803 * 2 ^ 59
def prefixEnd_4536803 : Nat := 4983230072969 + 3 ^ 40 * 4536803 * 2
def baseEnd_4536803 : Nat := 2329560573759918471098129

theorem tailTrace_4536803 : CollatzResearch.WordTrace tailWord_4536803 prefixEnd_4536803 2329560573759918471098129 := by
  unfold tailWord_4536803
  simp only [CollatzResearch.WordTrace]
  refine ⟨165470799382945030110599063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110313866255296686740399375 165470799382945030110599063)
  ·
    refine ⟨248206199074417545165898595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165470799382945030110599063 248206199074417545165898595)
    ·
      refine ⟨372309298611626317748847893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248206199074417545165898595 372309298611626317748847893)
      ·
        refine ⟨17451998372419983644477245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 372309298611626317748847893 17451998372419983644477245)
        ·
          refine ⟨6544499389657493866678967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17451998372419983644477245 6544499389657493866678967)
          ·
            refine ⟨9816749084486240800018451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6544499389657493866678967 9816749084486240800018451)
            ·
              refine ⟨14725123626729361200027677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9816749084486240800018451 14725123626729361200027677)
              ·
                refine ⟨5521921360023510450010379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14725123626729361200027677 5521921360023510450010379)
                ·
                  refine ⟨8282882040035265675015569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521921360023510450010379 8282882040035265675015569)
                  ·
                    refine ⟨6212161530026449256261677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8282882040035265675015569 6212161530026449256261677)
                    ·
                      refine ⟨2329560573759918471098129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212161530026449256261677 2329560573759918471098129)
                      ·
                        rfl

theorem cell23_4536803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4536803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536803 prefixEnd_4536803 := by exact prefixLift 4536803
  have htrace : WordTrace (prefixWord ++ tailWord_4536803) baseStart_4536803 baseEnd_4536803 := by
    simpa [prefixWord, tailWord_4536803, baseEnd_4536803] using wordTrace_append hprefix tailTrace_4536803
  have hstable : (prefixWord ++ tailWord_4536803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536803).length < 2 ^ (prefixWord ++ tailWord_4536803).sum := by decide
  have hdescent : baseEnd_4536803 < baseStart_4536803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536816 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3]
def baseStart_4536816 : Nat := 118140960795 + 4536816 * 2 ^ 59
def prefixEnd_4536816 : Nat := 4983230072969 + 3 ^ 40 * 4536816 * 2
def baseEnd_4536816 : Nat := 2329567249008426920235569

theorem tailTrace_4536816 : CollatzResearch.WordTrace tailWord_4536816 prefixEnd_4536816 2329567249008426920235569 := by
  unfold tailWord_4536816
  simp only [CollatzResearch.WordTrace]
  refine ⟨82735636765948966665411151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110314182354598622220548201 82735636765948966665411151)
  ·
    refine ⟨124103455148923449998116727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82735636765948966665411151 124103455148923449998116727)
    ·
      refine ⟨186155182723385174997175091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124103455148923449998116727 186155182723385174997175091)
      ·
        refine ⟨279232774085077762495762637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186155182723385174997175091 279232774085077762495762637)
        ·
          refine ⟨104712290281904160935910989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279232774085077762495762637 104712290281904160935910989)
          ·
            refine ⟨39267108855714060350966621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104712290281904160935910989 39267108855714060350966621)
            ·
              refine ⟨14725165820892772631612483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39267108855714060350966621 14725165820892772631612483)
              ·
                refine ⟨22087748731339158947418725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14725165820892772631612483 22087748731339158947418725)
                ·
                  refine ⟨4141452887126092302641011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22087748731339158947418725 4141452887126092302641011)
                  ·
                    refine ⟨6212179330689138453961517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4141452887126092302641011 6212179330689138453961517)
                    ·
                      refine ⟨2329567249008426920235569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212179330689138453961517 2329567249008426920235569)
                      ·
                        rfl

theorem cell23_4536816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_4536816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536816 prefixEnd_4536816 := by exact prefixLift 4536816
  have htrace : WordTrace (prefixWord ++ tailWord_4536816) baseStart_4536816 baseEnd_4536816 := by
    simpa [prefixWord, tailWord_4536816, baseEnd_4536816] using wordTrace_append hprefix tailTrace_4536816
  have hstable : (prefixWord ++ tailWord_4536816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536816).length < 2 ^ (prefixWord ++ tailWord_4536816).sum := by decide
  have hdescent : baseEnd_4536816 < baseStart_4536816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536826 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_4536826 : Nat := 118140960795 + 4536826 * 2 ^ 59
def prefixEnd_4536826 : Nat := 4983230072969 + 3 ^ 40 * 4536826 * 2
def baseEnd_4536826 : Nat := 2329572383814971881110523

theorem tailTrace_4536826 : CollatzResearch.WordTrace tailWord_4536826 prefixEnd_4536826 2329572383814971881110523 := by
  unfold tailWord_4536826
  simp only [CollatzResearch.WordTrace]
  refine ⟨41367909565465426259671583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110314425507907803359124221 41367909565465426259671583)
  ·
    refine ⟨62051864348198139389507375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41367909565465426259671583 62051864348198139389507375)
    ·
      refine ⟨93077796522297209084261063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62051864348198139389507375 93077796522297209084261063)
      ·
        refine ⟨139616694783445813626391595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93077796522297209084261063 139616694783445813626391595)
        ·
          refine ⟨209425042175168720439587393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139616694783445813626391595 209425042175168720439587393)
          ·
            refine ⟨157068781631376540329690545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209425042175168720439587393 157068781631376540329690545)
            ·
              refine ⟨117801586223532405247267909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157068781631376540329690545 117801586223532405247267909)
              ·
                refine ⟨22087797416912325983862733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117801586223532405247267909 22087797416912325983862733)
                ·
                  refine ⟨8282924031342122243948525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22087797416912325983862733 8282924031342122243948525)
                  ·
                    refine ⟨3106096511753295841480697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8282924031342122243948525 3106096511753295841480697)
                    ·
                      refine ⟨2329572383814971881110523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106096511753295841480697 2329572383814971881110523)
                      ·
                        rfl

theorem cell23_4536826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_4536826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536826 prefixEnd_4536826 := by exact prefixLift 4536826
  have htrace : WordTrace (prefixWord ++ tailWord_4536826) baseStart_4536826 baseEnd_4536826 := by
    simpa [prefixWord, tailWord_4536826, baseEnd_4536826] using wordTrace_append hprefix tailTrace_4536826
  have hstable : (prefixWord ++ tailWord_4536826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536826).length < 2 ^ (prefixWord ++ tailWord_4536826).sum := by decide
  have hdescent : baseEnd_4536826 < baseStart_4536826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536833 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_4536833 : Nat := 118140960795 + 4536833 * 2 ^ 59
def prefixEnd_4536833 : Nat := 4983230072969 + 3 ^ 40 * 4536833 * 2
def baseEnd_4536833 : Nat := 2329575978179553353722991

theorem tailTrace_4536833 : CollatzResearch.WordTrace tailWord_4536833 prefixEnd_4536833 2329575978179553353722991 := by
  unfold tailWord_4536833
  simp only [CollatzResearch.WordTrace]
  refine ⟨165471893572836345234191153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110314595715224230156127435 165471893572836345234191153)
  ·
    refine ⟨124103920179627258925643365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165471893572836345234191153 124103920179627258925643365)
    ·
      refine ⟨23269485033680111048558131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124103920179627258925643365 23269485033680111048558131)
      ·
        refine ⟨34904227550520166572837197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23269485033680111048558131 34904227550520166572837197)
        ·
          refine ⟨13089085331445062464813949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34904227550520166572837197 13089085331445062464813949)
          ·
            refine ⟨4908406999291898424305231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13089085331445062464813949 4908406999291898424305231)
            ·
              refine ⟨7362610498937847636457847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908406999291898424305231 7362610498937847636457847)
              ·
                refine ⟨11043915748406771454686771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7362610498937847636457847 11043915748406771454686771)
                ·
                  refine ⟨16565873622610157182030157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11043915748406771454686771 16565873622610157182030157)
                  ·
                    refine ⟨6212202608478808943261309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16565873622610157182030157 6212202608478808943261309)
                    ·
                      refine ⟨2329575978179553353722991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212202608478808943261309 2329575978179553353722991)
                      ·
                        rfl

theorem cell23_4536833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_4536833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536833 prefixEnd_4536833 := by exact prefixLift 4536833
  have htrace : WordTrace (prefixWord ++ tailWord_4536833) baseStart_4536833 baseEnd_4536833 := by
    simpa [prefixWord, tailWord_4536833, baseEnd_4536833] using wordTrace_append hprefix tailTrace_4536833
  have hstable : (prefixWord ++ tailWord_4536833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536833).length < 2 ^ (prefixWord ++ tailWord_4536833).sum := by decide
  have hdescent : baseEnd_4536833 < baseStart_4536833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536843 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 1, 3, 2]
def baseStart_4536843 : Nat := 118140960795 + 4536843 * 2 ^ 59
def prefixEnd_4536843 : Nat := 4983230072969 + 3 ^ 40 * 4536843 * 2
def baseEnd_4536843 : Nat := 2329581112986098314597945

theorem tailTrace_4536843 : CollatzResearch.WordTrace tailWord_4536843 prefixEnd_4536843 2329581112986098314597945 := by
  unfold tailWord_4536843
  simp only [CollatzResearch.WordTrace]
  refine ⟨165472258302800116942055183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110314838868533411294703455 165472258302800116942055183)
  ·
    refine ⟨248208387454200175413082775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165472258302800116942055183 248208387454200175413082775)
    ·
      refine ⟨372312581181300263119624163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248208387454200175413082775 372312581181300263119624163)
      ·
        refine ⟨558468871771950394679436245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372312581181300263119624163 558468871771950394679436245)
        ·
          refine ⟨13089114182155087375299287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 558468871771950394679436245 13089114182155087375299287)
          ·
            refine ⟨19633671273232631062948931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13089114182155087375299287 19633671273232631062948931)
            ·
              refine ⟨29450506909848946594423397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19633671273232631062948931 29450506909848946594423397)
              ·
                refine ⟨5521970045596677486454387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29450506909848946594423397 5521970045596677486454387)
                ·
                  refine ⟨8282955068395016229681581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521970045596677486454387 8282955068395016229681581)
                  ·
                    refine ⟨3106108150648131086130593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8282955068395016229681581 3106108150648131086130593)
                    ·
                      refine ⟨2329581112986098314597945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106108150648131086130593 2329581112986098314597945)
                      ·
                        rfl

theorem cell23_4536843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3, 2].length) (baseStart_4536843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536843 prefixEnd_4536843 := by exact prefixLift 4536843
  have htrace : WordTrace (prefixWord ++ tailWord_4536843) baseStart_4536843 baseEnd_4536843 := by
    simpa [prefixWord, tailWord_4536843, baseEnd_4536843] using wordTrace_append hprefix tailTrace_4536843
  have hstable : (prefixWord ++ tailWord_4536843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536843).length < 2 ^ (prefixWord ++ tailWord_4536843).sum := by decide
  have hdescent : baseEnd_4536843 < baseStart_4536843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536869 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_4536869 : Nat := 118140960795 + 4536869 * 2 ^ 59
def prefixEnd_4536869 : Nat := 4983230072969 + 3 ^ 40 * 4536869 * 2
def baseEnd_4536869 : Nat := 2329594463483115212872825

theorem tailTrace_4536869 : CollatzResearch.WordTrace tailWord_4536869 prefixEnd_4536869 2329594463483115212872825 := by
  unfold tailWord_4536869
  simp only [CollatzResearch.WordTrace]
  refine ⟨165473206600705923382501661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110315471067137282255001107 165473206600705923382501661)
  ·
    refine ⟨62052452475264721268438123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165473206600705923382501661 62052452475264721268438123)
    ·
      refine ⟨93078678712897081902657185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62052452475264721268438123 93078678712897081902657185)
      ·
        refine ⟨69809009034672811426992889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93078678712897081902657185 69809009034672811426992889)
        ·
          refine ⟨52356756776004608570244667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69809009034672811426992889 52356756776004608570244667)
          ·
            refine ⟨78535135164006912855367001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52356756776004608570244667 78535135164006912855367001)
            ·
              refine ⟨58901351373005184641525251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78535135164006912855367001 58901351373005184641525251)
              ·
                refine ⟨88352027059507776962287877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58901351373005184641525251 88352027059507776962287877)
                ·
                  refine ⟨16566005073657708180428977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88352027059507776962287877 16566005073657708180428977)
                  ·
                    refine ⟨12424503805243281135321733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16566005073657708180428977 12424503805243281135321733)
                    ·
                      refine ⟨2329594463483115212872825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12424503805243281135321733 2329594463483115212872825)
                      ·
                        rfl

theorem cell23_4536869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_4536869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536869 prefixEnd_4536869 := by exact prefixLift 4536869
  have htrace : WordTrace (prefixWord ++ tailWord_4536869) baseStart_4536869 baseEnd_4536869 := by
    simpa [prefixWord, tailWord_4536869, baseEnd_4536869] using wordTrace_append hprefix tailTrace_4536869
  have hstable : (prefixWord ++ tailWord_4536869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536869).length < 2 ^ (prefixWord ++ tailWord_4536869).sum := by decide
  have hdescent : baseEnd_4536869 < baseStart_4536869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536890 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_4536890 : Nat := 118140960795 + 4536890 * 2 ^ 59
def prefixEnd_4536890 : Nat := 4983230072969 + 3 ^ 40 * 4536890 * 2
def baseEnd_4536890 : Nat := 2329605246576859630710229

theorem tailTrace_4536890 : CollatzResearch.WordTrace tailWord_4536890 prefixEnd_4536890 2329605246576859630710229 := by
  unfold tailWord_4536890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41368493133407460992254031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110315981689086562646010749 41368493133407460992254031)
  ·
    refine ⟨62052739700111191488381047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41368493133407460992254031 62052739700111191488381047)
    ·
      refine ⟨93079109550166787232571571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62052739700111191488381047 93079109550166787232571571)
      ·
        refine ⟨139618664325250180848857357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93079109550166787232571571 139618664325250180848857357)
        ·
          refine ⟨52356999121968817818321509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139618664325250180848857357 52356999121968817818321509)
          ·
            refine ⟨9816937335369153340935283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52356999121968817818321509 9816937335369153340935283)
            ·
              refine ⟨14725406003053730011402925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9816937335369153340935283 14725406003053730011402925)
              ·
                refine ⟨5522027251145148754276097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14725406003053730011402925 5522027251145148754276097)
                ·
                  refine ⟨4141520438358861565707073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5522027251145148754276097 4141520438358861565707073)
                  ·
                    refine ⟨3106140328769146174280305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141520438358861565707073 3106140328769146174280305)
                    ·
                      refine ⟨2329605246576859630710229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106140328769146174280305 2329605246576859630710229)
                      ·
                        rfl

theorem cell23_4536890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_4536890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536890 prefixEnd_4536890 := by exact prefixLift 4536890
  have htrace : WordTrace (prefixWord ++ tailWord_4536890) baseStart_4536890 baseEnd_4536890 := by
    simpa [prefixWord, tailWord_4536890, baseEnd_4536890] using wordTrace_append hprefix tailTrace_4536890
  have hstable : (prefixWord ++ tailWord_4536890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536890).length < 2 ^ (prefixWord ++ tailWord_4536890).sum := by decide
  have hdescent : baseEnd_4536890 < baseStart_4536890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536894 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4536894 : Nat := 118140960795 + 4536894 * 2 ^ 59
def prefixEnd_4536894 : Nat := 4983230072969 + 3 ^ 40 * 4536894 * 2
def baseEnd_4536894 : Nat := 2329607300499477615060211

theorem tailTrace_4536894 : CollatzResearch.WordTrace tailWord_4536894 prefixEnd_4536894 2329607300499477615060211 := by
  unfold tailWord_4536894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20684264803201919081520217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110316078950410235101441157 20684264803201919081520217)
  ·
    refine ⟨15513198602401439311140163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20684264803201919081520217 15513198602401439311140163)
    ·
      refine ⟨23269797903602158966710245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15513198602401439311140163 23269797903602158966710245)
      ·
        refine ⟨4363087106925404806258171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23269797903602158966710245 4363087106925404806258171)
        ·
          refine ⟨6544630660388107209387257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4363087106925404806258171 6544630660388107209387257)
          ·
            refine ⟨4908472995291080407040443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6544630660388107209387257 4908472995291080407040443)
            ·
              refine ⟨7362709492936620610560665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908472995291080407040443 7362709492936620610560665)
              ·
                refine ⟨5522032119702465457920499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7362709492936620610560665 5522032119702465457920499)
                ·
                  refine ⟨8283048179553698186880749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5522032119702465457920499 8283048179553698186880749)
                  ·
                    refine ⟨3106143067332636820080281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8283048179553698186880749 3106143067332636820080281)
                    ·
                      refine ⟨2329607300499477615060211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106143067332636820080281 2329607300499477615060211)
                      ·
                        rfl

theorem cell23_4536894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4536894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536894 prefixEnd_4536894 := by exact prefixLift 4536894
  have htrace : WordTrace (prefixWord ++ tailWord_4536894) baseStart_4536894 baseEnd_4536894 := by
    simpa [prefixWord, tailWord_4536894, baseEnd_4536894] using wordTrace_append hprefix tailTrace_4536894
  have hstable : (prefixWord ++ tailWord_4536894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536894).length < 2 ^ (prefixWord ++ tailWord_4536894).sum := by decide
  have hdescent : baseEnd_4536894 < baseStart_4536894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536919 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_4536919 : Nat := 118140960795 + 4536919 * 2 ^ 59
def prefixEnd_4536919 : Nat := 4983230072969 + 3 ^ 40 * 4536919 * 2
def baseEnd_4536919 : Nat := 2329620137515840017247595

theorem tailTrace_4536919 : CollatzResearch.WordTrace tailWord_4536919 prefixEnd_4536919 2329620137515840017247595 := by
  unfold tailWord_4536919
  simp only [CollatzResearch.WordTrace]
  refine ⟨165475030250524781921821811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110316686833683187947881207 165475030250524781921821811)
  ·
    refine ⟨248212545375787172882732717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165475030250524781921821811 248212545375787172882732717)
    ·
      refine ⟨93079704515920189831024769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248212545375787172882732717 93079704515920189831024769)
      ·
        refine ⟨69809778386940142373268577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93079704515920189831024769 69809778386940142373268577)
        ·
          refine ⟨52357333790205106779951433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69809778386940142373268577 52357333790205106779951433)
          ·
            refine ⟨39268000342653830084963575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52357333790205106779951433 39268000342653830084963575)
            ·
              refine ⟨58902000513980745127445363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39268000342653830084963575 58902000513980745127445363)
              ·
                refine ⟨88353000770971117691168045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58902000513980745127445363 88353000770971117691168045)
                ·
                  refine ⟨33132375289114169134188017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88353000770971117691168045 33132375289114169134188017)
                  ·
                    refine ⟨24849281466835626850641013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33132375289114169134188017 24849281466835626850641013)
                    ·
                      refine ⟨2329620137515840017247595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24849281466835626850641013 2329620137515840017247595)
                      ·
                        rfl

theorem cell23_4536919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_4536919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536919 prefixEnd_4536919 := by exact prefixLift 4536919
  have htrace : WordTrace (prefixWord ++ tailWord_4536919) baseStart_4536919 baseEnd_4536919 := by
    simpa [prefixWord, tailWord_4536919, baseEnd_4536919] using wordTrace_append hprefix tailTrace_4536919
  have hstable : (prefixWord ++ tailWord_4536919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536919).length < 2 ^ (prefixWord ++ tailWord_4536919).sum := by decide
  have hdescent : baseEnd_4536919 < baseStart_4536919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536956 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_4536956 : Nat := 118140960795 + 4536956 * 2 ^ 59
def prefixEnd_4536956 : Nat := 4983230072969 + 3 ^ 40 * 4536956 * 2
def baseEnd_4536956 : Nat := 776546378766685457494975

theorem tailTrace_4536956 : CollatzResearch.WordTrace tailWord_4536956 prefixEnd_4536956 776546378766685457494975 := by
  unfold tailWord_4536956
  simp only [CollatzResearch.WordTrace]
  refine ⟨82738189875695368620459361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110317586500927158160612481 82738189875695368620459361)
  ·
    refine ⟨62053642406771526465344521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82738189875695368620459361 62053642406771526465344521)
    ·
      refine ⟨46540231805078644849008391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62053642406771526465344521 46540231805078644849008391)
      ·
        refine ⟨69810347707617967273512587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46540231805078644849008391 69810347707617967273512587)
        ·
          refine ⟨104715521561426950910268881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69810347707617967273512587 104715521561426950910268881)
          ·
            refine ⟨78536641171070213182701661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104715521561426950910268881 78536641171070213182701661)
            ·
              refine ⟨29451240439151329943513123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78536641171070213182701661 29451240439151329943513123)
              ·
                refine ⟨44176860658726994915269685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29451240439151329943513123 44176860658726994915269685)
                ·
                  refine ⟨4141580686755655773306533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44176860658726994915269685 4141580686755655773306533)
                  ·
                    refine ⟨776546378766685457494975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141580686755655773306533 776546378766685457494975)
                    ·
                      rfl

theorem cell23_4536956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_4536956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536956 prefixEnd_4536956 := by exact prefixLift 4536956
  have htrace : WordTrace (prefixWord ++ tailWord_4536956) baseStart_4536956 baseEnd_4536956 := by
    simpa [prefixWord, tailWord_4536956, baseEnd_4536956] using wordTrace_append hprefix tailTrace_4536956
  have hstable : (prefixWord ++ tailWord_4536956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536956).length < 2 ^ (prefixWord ++ tailWord_4536956).sum := by decide
  have hdescent : baseEnd_4536956 < baseStart_4536956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536959 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_4536959 : Nat := 118140960795 + 4536959 * 2 ^ 59
def prefixEnd_4536959 : Nat := 4983230072969 + 3 ^ 40 * 4536959 * 2
def baseEnd_4536959 : Nat := 2329640676742019860747411

theorem tailTrace_4536959 : CollatzResearch.WordTrace tailWord_4536959 prefixEnd_4536959 2329640676742019860747411 := by
  unfold tailWord_4536959
  simp only [CollatzResearch.WordTrace]
  refine ⟨165476489170379868753277931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110317659446919912502185287 165476489170379868753277931)
  ·
    refine ⟨248214733755569803129916897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165476489170379868753277931 248214733755569803129916897)
    ·
      refine ⟨186161050316677352347437673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248214733755569803129916897 186161050316677352347437673)
      ·
        refine ⟨139620787737508014260578255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186161050316677352347437673 139620787737508014260578255)
        ·
          refine ⟨209431181606262021390867383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139620787737508014260578255 209431181606262021390867383)
          ·
            refine ⟨314146772409393032086301075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209431181606262021390867383 314146772409393032086301075)
            ·
              refine ⟨471220158614089548129451613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314146772409393032086301075 471220158614089548129451613)
              ·
                refine ⟨176707559480283580548544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471220158614089548129451613 176707559480283580548544355)
                ·
                  refine ⟨265061339220425370822816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176707559480283580548544355 265061339220425370822816533)
                  ·
                    refine ⟨12424750275957439257319525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 265061339220425370822816533 12424750275957439257319525)
                    ·
                      refine ⟨2329640676742019860747411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12424750275957439257319525 2329640676742019860747411)
                      ·
                        rfl

theorem cell23_4536959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_4536959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536959 prefixEnd_4536959 := by exact prefixLift 4536959
  have htrace : WordTrace (prefixWord ++ tailWord_4536959) baseStart_4536959 baseEnd_4536959 := by
    simpa [prefixWord, tailWord_4536959, baseEnd_4536959] using wordTrace_append hprefix tailTrace_4536959
  have hstable : (prefixWord ++ tailWord_4536959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536959).length < 2 ^ (prefixWord ++ tailWord_4536959).sum := by decide
  have hdescent : baseEnd_4536959 < baseStart_4536959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536969 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 8]
def baseStart_4536969 : Nat := 118140960795 + 4536969 * 2 ^ 59
def prefixEnd_4536969 : Nat := 4983230072969 + 3 ^ 40 * 4536969 * 2
def baseEnd_4536969 : Nat := 258849534616507202402485

theorem tailTrace_4536969 : CollatzResearch.WordTrace tailWord_4536969 prefixEnd_4536969 258849534616507202402485 := by
  unfold tailWord_4536969
  simp only [CollatzResearch.WordTrace]
  refine ⟨165476853900343640461141961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110317902600229093640761307 165476853900343640461141961)
  ·
    refine ⟨124107640425257730345856471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165476853900343640461141961 124107640425257730345856471)
    ·
      refine ⟨186161460637886595518784707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124107640425257730345856471 186161460637886595518784707)
      ·
        refine ⟨279242190956829893278177061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186161460637886595518784707 279242190956829893278177061)
        ·
          refine ⟨52357910804405604989658199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279242190956829893278177061 52357910804405604989658199)
          ·
            refine ⟨78536866206608407484487299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52357910804405604989658199 78536866206608407484487299)
            ·
              refine ⟨117805299309912611226730949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78536866206608407484487299 117805299309912611226730949)
              ·
                refine ⟨22088493620608614605012053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117805299309912611226730949 22088493620608614605012053)
                ·
                  refine ⟨258849534616507202402485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22088493620608614605012053 258849534616507202402485)
                  ·
                    rfl

theorem cell23_4536969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_4536969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536969 prefixEnd_4536969 := by exact prefixLift 4536969
  have htrace : WordTrace (prefixWord ++ tailWord_4536969) baseStart_4536969 baseEnd_4536969 := by
    simpa [prefixWord, tailWord_4536969, baseEnd_4536969] using wordTrace_append hprefix tailTrace_4536969
  have hstable : (prefixWord ++ tailWord_4536969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536969).length < 2 ^ (prefixWord ++ tailWord_4536969).sum := by decide
  have hdescent : baseEnd_4536969 < baseStart_4536969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536980 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4536980 : Nat := 118140960795 + 4536980 * 2 ^ 59
def prefixEnd_4536980 : Nat := 4983230072969 + 3 ^ 40 * 4536980 * 2
def baseEnd_4536980 : Nat := 2329651459835764278584815

theorem tailTrace_4536980 : CollatzResearch.WordTrace tailWord_4536980 prefixEnd_4536980 2329651459835764278584815 := by
  unfold tailWord_4536980
  simp only [CollatzResearch.WordTrace]
  refine ⟨82738627551651894669896197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110318170068869192893194929 82738627551651894669896197)
  ·
    refine ⟨15513492665934730250605537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82738627551651894669896197 15513492665934730250605537)
    ·
      refine ⟨11635119499451047687954153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15513492665934730250605537 11635119499451047687954153)
      ·
        refine ⟨8726339624588285765965615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11635119499451047687954153 8726339624588285765965615)
        ·
          refine ⟨13089509436882428648948423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8726339624588285765965615 13089509436882428648948423)
          ·
            refine ⟨19634264155323642973422635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13089509436882428648948423 19634264155323642973422635)
            ·
              refine ⟨29451396232985464460133953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19634264155323642973422635 29451396232985464460133953)
              ·
                refine ⟨22088547174739098345100465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29451396232985464460133953 22088547174739098345100465)
                ·
                  refine ⟨16566410381054323758825349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22088547174739098345100465 16566410381054323758825349)
                  ·
                    refine ⟨3106201946447685704779753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16566410381054323758825349 3106201946447685704779753)
                    ·
                      refine ⟨2329651459835764278584815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106201946447685704779753 2329651459835764278584815)
                      ·
                        rfl

theorem cell23_4536980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4536980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536980 prefixEnd_4536980 := by exact prefixLift 4536980
  have htrace : WordTrace (prefixWord ++ tailWord_4536980) baseStart_4536980 baseEnd_4536980 := by
    simpa [prefixWord, tailWord_4536980, baseEnd_4536980] using wordTrace_append hprefix tailTrace_4536980
  have hstable : (prefixWord ++ tailWord_4536980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536980).length < 2 ^ (prefixWord ++ tailWord_4536980).sum := by decide
  have hdescent : baseEnd_4536980 < baseStart_4536980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536990 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4536990 : Nat := 118140960795 + 4536990 * 2 ^ 59
def prefixEnd_4536990 : Nat := 4983230072969 + 3 ^ 40 * 4536990 * 2
def baseEnd_4536990 : Nat := 776552198214103079819923

theorem tailTrace_4536990 : CollatzResearch.WordTrace tailWord_4536990 prefixEnd_4536990 776552198214103079819923 := by
  unfold tailWord_4536990
  simp only [CollatzResearch.WordTrace]
  refine ⟨20684702479158445130957053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110318413222178374031770949 20684702479158445130957053)
  ·
    refine ⟨7756763429684416924108895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20684702479158445130957053 7756763429684416924108895)
    ·
      refine ⟨11635145144526625386163343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7756763429684416924108895 11635145144526625386163343)
      ·
        refine ⟨17452717716789938079245015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11635145144526625386163343 17452717716789938079245015)
        ·
          refine ⟨26179076575184907118867523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17452717716789938079245015 26179076575184907118867523)
          ·
            refine ⟨39268614862777360678301285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26179076575184907118867523 39268614862777360678301285)
            ·
              refine ⟨7362865286770755127181491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39268614862777360678301285 7362865286770755127181491)
              ·
                refine ⟨11044297930156132690772237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7362865286770755127181491 11044297930156132690772237)
                ·
                  refine ⟨4141611723808549759039589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11044297930156132690772237 4141611723808549759039589)
                  ·
                    refine ⟨776552198214103079819923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141611723808549759039589 776552198214103079819923)
                    ·
                      rfl

theorem cell23_4536990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4536990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536990 prefixEnd_4536990 := by exact prefixLift 4536990
  have htrace : WordTrace (prefixWord ++ tailWord_4536990) baseStart_4536990 baseEnd_4536990 := by
    simpa [prefixWord, tailWord_4536990, baseEnd_4536990] using wordTrace_append hprefix tailTrace_4536990
  have hstable : (prefixWord ++ tailWord_4536990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536990).length < 2 ^ (prefixWord ++ tailWord_4536990).sum := by decide
  have hdescent : baseEnd_4536990 < baseStart_4536990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537023 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 5, 2]
def baseStart_4537023 : Nat := 118140960795 + 4537023 * 2 ^ 59
def prefixEnd_4537023 : Nat := 4983230072969 + 3 ^ 40 * 4537023 * 2
def baseEnd_4537023 : Nat := 2329673539503907610347117

theorem tailTrace_4537023 : CollatzResearch.WordTrace tailWord_4537023 prefixEnd_4537023 2329673539503907610347117 := by
  unfold tailWord_4537023
  simp only [CollatzResearch.WordTrace]
  refine ⟨165478823442148007683607723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110319215628098671789071815 165478823442148007683607723)
  ·
    refine ⟨248218235163222011525411585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165478823442148007683607723 248218235163222011525411585)
    ·
      refine ⟨186163676372416508644058689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248218235163222011525411585 186163676372416508644058689)
      ·
        refine ⟨139622757279312381483044017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186163676372416508644058689 139622757279312381483044017)
        ·
          refine ⟨104717067959484286112283013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139622757279312381483044017 104717067959484286112283013)
          ·
            refine ⟨19634450242403303646053065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104717067959484286112283013 19634450242403303646053065)
            ·
              refine ⟨14725837681802477734539799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19634450242403303646053065 14725837681802477734539799)
              ·
                refine ⟨22088756522703716601809699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14725837681802477734539799 22088756522703716601809699)
                ·
                  refine ⟨33133134784055574902714549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22088756522703716601809699 33133134784055574902714549)
                  ·
                    refine ⟨3106231386005210147129489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33133134784055574902714549 3106231386005210147129489)
                    ·
                      refine ⟨2329673539503907610347117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106231386005210147129489 2329673539503907610347117)
                      ·
                        rfl

theorem cell23_4537023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_4537023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537023 prefixEnd_4537023 := by exact prefixLift 4537023
  have htrace : WordTrace (prefixWord ++ tailWord_4537023) baseStart_4537023 baseEnd_4537023 := by
    simpa [prefixWord, tailWord_4537023, baseEnd_4537023] using wordTrace_append hprefix tailTrace_4537023
  have hstable : (prefixWord ++ tailWord_4537023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537023).length < 2 ^ (prefixWord ++ tailWord_4537023).sum := by decide
  have hdescent : baseEnd_4537023 < baseStart_4537023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537056 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_4537056 : Nat := 118140960795 + 4537056 * 2 ^ 59
def prefixEnd_4537056 : Nat := 4983230072969 + 3 ^ 40 * 4537056 * 2
def baseEnd_4537056 : Nat := 2329690484365505981234465

theorem tailTrace_4537056 : CollatzResearch.WordTrace tailWord_4537056 prefixEnd_4537056 2329690484365505981234465 := by
  unfold tailWord_4537056
  simp only [CollatzResearch.WordTrace]
  refine ⟨82740013525514227159779511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110320018034018969546372681 82740013525514227159779511)
  ·
    refine ⟨124110020288271340739669267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82740013525514227159779511 124110020288271340739669267)
    ·
      refine ⟨186165030432407011109503901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124110020288271340739669267 186165030432407011109503901)
      ·
        refine ⟨69811886412152629166063963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186165030432407011109503901 69811886412152629166063963)
        ·
          refine ⟨104717829618228943749095945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69811886412152629166063963 104717829618228943749095945)
          ·
            refine ⟨78538372213671707811821959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104717829618228943749095945 78538372213671707811821959)
            ·
              refine ⟨117807558320507561717732939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78538372213671707811821959 117807558320507561717732939)
              ·
                refine ⟨176711337480761342576599409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117807558320507561717732939 176711337480761342576599409)
                ·
                  refine ⟨132533503110571006932449557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176711337480761342576599409 132533503110571006932449557)
                  ·
                    refine ⟨6212507958308015949958573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132533503110571006932449557 6212507958308015949958573)
                    ·
                      refine ⟨2329690484365505981234465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212507958308015949958573 2329690484365505981234465)
                      ·
                        rfl

theorem cell23_4537056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_4537056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537056 prefixEnd_4537056 := by exact prefixLift 4537056
  have htrace : WordTrace (prefixWord ++ tailWord_4537056) baseStart_4537056 baseEnd_4537056 := by
    simpa [prefixWord, tailWord_4537056, baseEnd_4537056] using wordTrace_append hprefix tailTrace_4537056
  have hstable : (prefixWord ++ tailWord_4537056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537056).length < 2 ^ (prefixWord ++ tailWord_4537056).sum := by decide
  have hdescent : baseEnd_4537056 < baseStart_4537056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537070 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_4537070 : Nat := 118140960795 + 4537070 * 2 ^ 59
def prefixEnd_4537070 : Nat := 4983230072969 + 3 ^ 40 * 4537070 * 2
def baseEnd_4537070 : Nat := 2329697673094668926459401

theorem tailTrace_4537070 : CollatzResearch.WordTrace tailWord_4537070 prefixEnd_4537070 2329697673094668926459401 := by
  unfold tailWord_4537070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20685067209122216838821083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110320358448651823140379109 20685067209122216838821083)
  ·
    refine ⟨31027600813683325258231625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20685067209122216838821083 31027600813683325258231625)
    ·
      refine ⟨23270700610262493943673719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31027600813683325258231625 23270700610262493943673719)
      ·
        refine ⟨34906050915393740915510579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23270700610262493943673719 34906050915393740915510579)
        ·
          refine ⟨52359076373090611373265869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34906050915393740915510579 52359076373090611373265869)
          ·
            refine ⟨19634653639908979264974701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52359076373090611373265869 19634653639908979264974701)
            ·
              refine ⟨7362995114965867224365513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19634653639908979264974701 7362995114965867224365513)
              ·
                refine ⟨5522246336224400418274135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7362995114965867224365513 5522246336224400418274135)
                ·
                  refine ⟨8283369504336600627411203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5522246336224400418274135 8283369504336600627411203)
                  ·
                    refine ⟨12425054256504900941116805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8283369504336600627411203 12425054256504900941116805)
                    ·
                      refine ⟨2329697673094668926459401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12425054256504900941116805 2329697673094668926459401)
                      ·
                        rfl

theorem cell23_4537070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_4537070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537070 prefixEnd_4537070 := by exact prefixLift 4537070
  have htrace : WordTrace (prefixWord ++ tailWord_4537070) baseStart_4537070 baseEnd_4537070 := by
    simpa [prefixWord, tailWord_4537070, baseEnd_4537070] using wordTrace_append hprefix tailTrace_4537070
  have hstable : (prefixWord ++ tailWord_4537070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537070).length < 2 ^ (prefixWord ++ tailWord_4537070).sum := by decide
  have hdescent : baseEnd_4537070 < baseStart_4537070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537073 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_4537073 : Nat := 118140960795 + 4537073 * 2 ^ 59
def prefixEnd_4537073 : Nat := 4983230072969 + 3 ^ 40 * 4537073 * 2
def baseEnd_4537073 : Nat := 2329699213536632414721887

theorem tailTrace_4537073 : CollatzResearch.WordTrace tailWord_4537073 prefixEnd_4537073 2329699213536632414721887 := by
  unfold tailWord_4537073
  simp only [CollatzResearch.WordTrace]
  refine ⟨165480647091966866222927873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110320431394644577481951915 165480647091966866222927873)
  ·
    refine ⟨124110485318975149667195905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165480647091966866222927873 124110485318975149667195905)
    ·
      refine ⟨93082863989231362250396929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124110485318975149667195905 93082863989231362250396929)
      ·
        refine ⟨69812147991923521687797697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93082863989231362250396929 69812147991923521687797697)
        ·
          refine ⟨52359110993942641265848273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69812147991923521687797697 52359110993942641265848273)
          ·
            refine ⟨39269333245456980949386205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52359110993942641265848273 39269333245456980949386205)
            ·
              refine ⟨14725999967046367856019827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39269333245456980949386205 14725999967046367856019827)
              ·
                refine ⟨22088999950569551784029741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14725999967046367856019827 22088999950569551784029741)
                ·
                  refine ⟨8283374981463581919011153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22088999950569551784029741 8283374981463581919011153)
                  ·
                    refine ⟨6212531236097686439258365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8283374981463581919011153 6212531236097686439258365)
                    ·
                      refine ⟨2329699213536632414721887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212531236097686439258365 2329699213536632414721887)
                      ·
                        rfl

theorem cell23_4537073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_4537073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537073 prefixEnd_4537073 := by exact prefixLift 4537073
  have htrace : WordTrace (prefixWord ++ tailWord_4537073) baseStart_4537073 baseEnd_4537073 := by
    simpa [prefixWord, tailWord_4537073, baseEnd_4537073] using wordTrace_append hprefix tailTrace_4537073
  have hstable : (prefixWord ++ tailWord_4537073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537073).length < 2 ^ (prefixWord ++ tailWord_4537073).sum := by decide
  have hdescent : baseEnd_4537073 < baseStart_4537073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537087 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 1, 2, 2]
def baseStart_4537087 : Nat := 118140960795 + 4537087 * 2 ^ 59
def prefixEnd_4537087 : Nat := 4983230072969 + 3 ^ 40 * 4537087 * 2
def baseEnd_4537087 : Nat := 2329706402265795359946823

theorem tailTrace_4537087 : CollatzResearch.WordTrace tailWord_4537087 prefixEnd_4537087 2329706402265795359946823 := by
  unfold tailWord_4537087
  simp only [CollatzResearch.WordTrace]
  refine ⟨165481157713916146613937515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110320771809277431075958343 165481157713916146613937515)
  ·
    refine ⟨248221736570874219920906273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165481157713916146613937515 248221736570874219920906273)
    ·
      refine ⟨186166302428155664940679705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248221736570874219920906273 186166302428155664940679705)
      ·
        refine ⟨139624726821116748705509779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186166302428155664940679705 139624726821116748705509779)
        ·
          refine ⟨209437090231675123058264669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139624726821116748705509779 209437090231675123058264669)
          ·
            refine ⟨78538908836878171146849251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209437090231675123058264669 78538908836878171146849251)
            ·
              refine ⟨117808363255317256720273877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78538908836878171146849251 117808363255317256720273877)
              ·
                refine ⟨2761133513796498204381419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117808363255317256720273877 2761133513796498204381419)
                ·
                  refine ⟨4141700270694747306572129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761133513796498204381419 4141700270694747306572129)
                  ·
                    refine ⟨3106275203021060479929097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141700270694747306572129 3106275203021060479929097)
                    ·
                      refine ⟨2329706402265795359946823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106275203021060479929097 2329706402265795359946823)
                      ·
                        rfl

theorem cell23_4537087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_4537087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537087 prefixEnd_4537087 := by exact prefixLift 4537087
  have htrace : WordTrace (prefixWord ++ tailWord_4537087) baseStart_4537087 baseEnd_4537087 := by
    simpa [prefixWord, tailWord_4537087, baseEnd_4537087] using wordTrace_append hprefix tailTrace_4537087
  have hstable : (prefixWord ++ tailWord_4537087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537087).length < 2 ^ (prefixWord ++ tailWord_4537087).sum := by decide
  have hdescent : baseEnd_4537087 < baseStart_4537087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537090 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_4537090 : Nat := 118140960795 + 4537090 * 2 ^ 59
def prefixEnd_4537090 : Nat := 4983230072969 + 3 ^ 40 * 4537090 * 2
def baseEnd_4537090 : Nat := 2329707942707758848209309

theorem tailTrace_4537090 : CollatzResearch.WordTrace tailWord_4537090 prefixEnd_4537090 2329707942707758848209309 := by
  unfold tailWord_4537090
  simp only [CollatzResearch.WordTrace]
  refine ⟨41370316783226319531574181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110320844755270185417531149 41370316783226319531574181)
  ·
    refine ⟨7756934396854934912170159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41370316783226319531574181 7756934396854934912170159)
    ·
      refine ⟨11635401595282402368255239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7756934396854934912170159 11635401595282402368255239)
      ·
        refine ⟨17453102392923603552382859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11635401595282402368255239 17453102392923603552382859)
        ·
          refine ⟨26179653589385405328574289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17453102392923603552382859 26179653589385405328574289)
          ·
            refine ⟨19634740192039053996430717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26179653589385405328574289 19634740192039053996430717)
            ·
              refine ⟨7363027572014645248661519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19634740192039053996430717 7363027572014645248661519)
              ·
                refine ⟨11044541358021967872992279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363027572014645248661519 11044541358021967872992279)
                ·
                  refine ⟨16566812037032951809488419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11044541358021967872992279 16566812037032951809488419)
                  ·
                    refine ⟨24850218055549427714232629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16566812037032951809488419 24850218055549427714232629)
                    ·
                      refine ⟨2329707942707758848209309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24850218055549427714232629 2329707942707758848209309)
                      ·
                        rfl

theorem cell23_4537090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_4537090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537090 prefixEnd_4537090 := by exact prefixLift 4537090
  have htrace : WordTrace (prefixWord ++ tailWord_4537090) baseStart_4537090 baseEnd_4537090 := by
    simpa [prefixWord, tailWord_4537090, baseEnd_4537090] using wordTrace_append hprefix tailTrace_4537090
  have hstable : (prefixWord ++ tailWord_4537090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537090).length < 2 ^ (prefixWord ++ tailWord_4537090).sum := by decide
  have hdescent : baseEnd_4537090 < baseStart_4537090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537117 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4537117 : Nat := 118140960795 + 4537117 * 2 ^ 59
def prefixEnd_4537117 : Nat := 4983230072969 + 3 ^ 40 * 4537117 * 2
def baseEnd_4537117 : Nat := 2329721806685430242571685

theorem tailTrace_4537117 : CollatzResearch.WordTrace tailWord_4537117 prefixEnd_4537117 2329721806685430242571685 := by
  unfold tailWord_4537117
  simp only [CollatzResearch.WordTrace]
  refine ⟨165482251903807461737529605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110321501269204974491686403 165482251903807461737529605)
  ·
    refine ⟨31027922231963899075786801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165482251903807461737529605 31027922231963899075786801)
    ·
      refine ⟨23270941673972924306840101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31027922231963899075786801 23270941673972924306840101)
      ·
        refine ⟨4363301563869923307532519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23270941673972924306840101 4363301563869923307532519)
        ·
          refine ⟨6544952345804884961298779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4363301563869923307532519 6544952345804884961298779)
          ·
            refine ⟨9817428518707327441948169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6544952345804884961298779 9817428518707327441948169)
            ·
              refine ⟨7363071389030495581461127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9817428518707327441948169 7363071389030495581461127)
              ·
                refine ⟨11044607083545743372191691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363071389030495581461127 11044607083545743372191691)
                ·
                  refine ⟨16566910625318615058287537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11044607083545743372191691 16566910625318615058287537)
                  ·
                    refine ⟨12425182968988961293715653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16566910625318615058287537 12425182968988961293715653)
                    ·
                      refine ⟨2329721806685430242571685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12425182968988961293715653 2329721806685430242571685)
                      ·
                        rfl

theorem cell23_4537117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4537117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537117 prefixEnd_4537117 := by exact prefixLift 4537117
  have htrace : WordTrace (prefixWord ++ tailWord_4537117) baseStart_4537117 baseEnd_4537117 := by
    simpa [prefixWord, tailWord_4537117, baseEnd_4537117] using wordTrace_append hprefix tailTrace_4537117
  have hstable : (prefixWord ++ tailWord_4537117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537117).length < 2 ^ (prefixWord ++ tailWord_4537117).sum := by decide
  have hdescent : baseEnd_4537117 < baseStart_4537117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537120 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4537120 : Nat := 118140960795 + 4537120 * 2 ^ 59
def prefixEnd_4537120 : Nat := 4983230072969 + 3 ^ 40 * 4537120 * 2
def baseEnd_4537120 : Nat := 2329723347127393730834171

theorem tailTrace_4537120 : CollatzResearch.WordTrace tailWord_4537120 prefixEnd_4537120 2329723347127393730834171 := by
  unfold tailWord_4537120
  simp only [CollatzResearch.WordTrace]
  refine ⟨82741180661398296624944407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110321574215197728833259209 82741180661398296624944407)
  ·
    refine ⟨124111770992097444937416611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82741180661398296624944407 124111770992097444937416611)
    ·
      refine ⟨186167656488146167406124917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124111770992097444937416611 186167656488146167406124917)
      ·
        refine ⟨17453217795763703194324211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186167656488146167406124917 17453217795763703194324211)
        ·
          refine ⟨26179826693645554791486317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17453217795763703194324211 26179826693645554791486317)
          ·
            refine ⟨9817435010117083046807369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26179826693645554791486317 9817435010117083046807369)
            ·
              refine ⟨7363076257587812285105527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9817435010117083046807369 7363076257587812285105527)
              ·
                refine ⟨11044614386381718427658291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363076257587812285105527 11044614386381718427658291)
                ·
                  refine ⟨16566921579572577641487437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11044614386381718427658291 16566921579572577641487437)
                  ·
                    refine ⟨6212595592339716615557789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16566921579572577641487437 6212595592339716615557789)
                    ·
                      refine ⟨2329723347127393730834171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212595592339716615557789 2329723347127393730834171)
                      ·
                        rfl

theorem cell23_4537120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4537120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537120 prefixEnd_4537120 := by exact prefixLift 4537120
  have htrace : WordTrace (prefixWord ++ tailWord_4537120) baseStart_4537120 baseEnd_4537120 := by
    simpa [prefixWord, tailWord_4537120, baseEnd_4537120] using wordTrace_append hprefix tailTrace_4537120
  have hstable : (prefixWord ++ tailWord_4537120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537120).length < 2 ^ (prefixWord ++ tailWord_4537120).sum := by decide
  have hdescent : baseEnd_4537120 < baseStart_4537120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537173 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4537173 : Nat := 118140960795 + 4537173 * 2 ^ 59
def prefixEnd_4537173 : Nat := 4983230072969 + 3 ^ 40 * 4537173 * 2
def baseEnd_4537173 : Nat := 2329750561602082023471427

theorem tailTrace_4537173 : CollatzResearch.WordTrace tailWord_4537173 prefixEnd_4537173 2329750561602082023471427 := by
  unfold tailWord_4537173
  simp only [CollatzResearch.WordTrace]
  refine ⟨165484294391604583301568173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110322862927736388867712115 165484294391604583301568173)
  ·
    refine ⟨62056610396851718738088065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165484294391604583301568173 62056610396851718738088065)
    ·
      refine ⟨46542457797638789053566049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62056610396851718738088065 46542457797638789053566049)
      ·
        refine ⟨34906843348229091790174537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46542457797638789053566049 34906843348229091790174537)
        ·
          refine ⟨26180132511171818842630903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34906843348229091790174537 26180132511171818842630903)
          ·
            refine ⟨39270198766757728263946355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26180132511171818842630903 39270198766757728263946355)
            ·
              refine ⟨58905298150136592395919533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39270198766757728263946355 58905298150136592395919533)
              ·
                refine ⟨22089486806301222148469825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58905298150136592395919533 22089486806301222148469825)
                ·
                  refine ⟨16567115104725916611352369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22089486806301222148469825 16567115104725916611352369)
                  ·
                    refine ⟨12425336328544437458514277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16567115104725916611352369 12425336328544437458514277)
                    ·
                      refine ⟨2329750561602082023471427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12425336328544437458514277 2329750561602082023471427)
                      ·
                        rfl

theorem cell23_4537173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4537173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537173 prefixEnd_4537173 := by exact prefixLift 4537173
  have htrace : WordTrace (prefixWord ++ tailWord_4537173) baseStart_4537173 baseEnd_4537173 := by
    simpa [prefixWord, tailWord_4537173, baseEnd_4537173] using wordTrace_append hprefix tailTrace_4537173
  have hstable : (prefixWord ++ tailWord_4537173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537173).length < 2 ^ (prefixWord ++ tailWord_4537173).sum := by decide
  have hdescent : baseEnd_4537173 < baseStart_4537173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537176 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4537176 : Nat := 118140960795 + 4537176 * 2 ^ 59
def prefixEnd_4537176 : Nat := 4983230072969 + 3 ^ 40 * 4537176 * 2
def baseEnd_4537176 : Nat := 2329752102044045511733913

theorem tailTrace_4537176 : CollatzResearch.WordTrace tailWord_4537176 prefixEnd_4537176 2329752102044045511733913 := by
  unfold tailWord_4537176
  simp only [CollatzResearch.WordTrace]
  refine ⟨82742201905296857406963691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110322935873729143209284921 82742201905296857406963691)
  ·
    refine ⟨124113302857945286110445537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82742201905296857406963691 124113302857945286110445537)
    ·
      refine ⟨93084977143458964582834153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124113302857945286110445537 93084977143458964582834153)
      ·
        refine ⟨69813732857594223437125615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93084977143458964582834153 69813732857594223437125615)
        ·
          refine ⟨104720599286391335155688423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69813732857594223437125615 104720599286391335155688423)
          ·
            refine ⟨157080898929587002733532635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104720599286391335155688423 157080898929587002733532635)
            ·
              refine ⟨235621348394380504100298953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157080898929587002733532635 235621348394380504100298953)
              ·
                refine ⟨176716011295785378075224215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235621348394380504100298953 176716011295785378075224215)
                ·
                  refine ⟨265074016943678067112836323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176716011295785378075224215 265074016943678067112836323)
                  ·
                    refine ⟨397611025415517100669254485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 265074016943678067112836323 397611025415517100669254485)
                    ·
                      refine ⟨2329752102044045511733913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 397611025415517100669254485 2329752102044045511733913)
                      ·
                        rfl

theorem cell23_4537176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4537176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537176 prefixEnd_4537176 := by exact prefixLift 4537176
  have htrace : WordTrace (prefixWord ++ tailWord_4537176) baseStart_4537176 baseEnd_4537176 := by
    simpa [prefixWord, tailWord_4537176, baseEnd_4537176] using wordTrace_append hprefix tailTrace_4537176
  have hstable : (prefixWord ++ tailWord_4537176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537176).length < 2 ^ (prefixWord ++ tailWord_4537176).sum := by decide
  have hdescent : baseEnd_4537176 < baseStart_4537176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537177 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 1, 4, 2]
def baseStart_4537177 : Nat := 118140960795 + 4537177 * 2 ^ 59
def prefixEnd_4537177 : Nat := 4983230072969 + 3 ^ 40 * 4537177 * 2
def baseEnd_4537177 : Nat := 2329752615524700007821409

theorem tailTrace_4537177 : CollatzResearch.WordTrace tailWord_4537177 prefixEnd_4537177 2329752615524700007821409 := by
  unfold tailWord_4537177
  simp only [CollatzResearch.WordTrace]
  refine ⟨165484440283590091984713785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110322960189060061323142523 165484440283590091984713785)
  ·
    refine ⟨124113330212692568988535339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165484440283590091984713785 124113330212692568988535339)
    ·
      refine ⟨186169995319038853482803009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124113330212692568988535339 186169995319038853482803009)
      ·
        refine ⟨139627496489279140112102257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186169995319038853482803009 139627496489279140112102257)
        ·
          refine ⟨104720622366959355084076693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139627496489279140112102257 104720622366959355084076693)
          ·
            refine ⟨4908779173451219769566095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104720622366959355084076693 4908779173451219769566095)
            ·
              refine ⟨7363168760176829654349143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908779173451219769566095 7363168760176829654349143)
              ·
                refine ⟨11044753140265244481523715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363168760176829654349143 11044753140265244481523715)
                ·
                  refine ⟨16567129710397866722285573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11044753140265244481523715 16567129710397866722285573)
                  ·
                    refine ⟨3106336820699600010428545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16567129710397866722285573 3106336820699600010428545)
                    ·
                      refine ⟨2329752615524700007821409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106336820699600010428545 2329752615524700007821409)
                      ·
                        rfl

theorem cell23_4537177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_4537177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537177 prefixEnd_4537177 := by exact prefixLift 4537177
  have htrace : WordTrace (prefixWord ++ tailWord_4537177) baseStart_4537177 baseEnd_4537177 := by
    simpa [prefixWord, tailWord_4537177, baseEnd_4537177] using wordTrace_append hprefix tailTrace_4537177
  have hstable : (prefixWord ++ tailWord_4537177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537177).length < 2 ^ (prefixWord ++ tailWord_4537177).sum := by decide
  have hdescent : baseEnd_4537177 < baseStart_4537177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537200 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 5]
def baseStart_4537200 : Nat := 118140960795 + 4537200 * 2 ^ 59
def prefixEnd_4537200 : Nat := 4983230072969 + 3 ^ 40 * 4537200 * 2
def baseEnd_4537200 : Nat := 258862713953305935314867

theorem tailTrace_4537200 : CollatzResearch.WordTrace tailWord_4537200 prefixEnd_4537200 258862713953305935314867 := by
  unfold tailWord_4537200
  simp only [CollatzResearch.WordTrace]
  refine ⟨82742639581253383456400527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110323519441671177941867369 82742639581253383456400527)
  ·
    refine ⟨124113959371880075184600791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82742639581253383456400527 124113959371880075184600791)
    ·
      refine ⟨186170939057820112776901187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124113959371880075184600791 186170939057820112776901187)
      ·
        refine ⟨279256408586730169165351781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186170939057820112776901187 279256408586730169165351781)
        ·
          refine ⟨52360576610011906718503459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279256408586730169165351781 52360576610011906718503459)
          ·
            refine ⟨78540864915017860077755189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52360576610011906718503459 78540864915017860077755189)
            ·
              refine ⟨7363206085782924382289549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78540864915017860077755189 7363206085782924382289549)
              ·
                refine ⟨2761202282168596643358581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7363206085782924382289549 2761202282168596643358581)
                ·
                  refine ⟨258862713953305935314867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2761202282168596643358581 258862713953305935314867)
                  ·
                    rfl

theorem cell23_4537200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 5].length) (baseStart_4537200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537200 prefixEnd_4537200 := by exact prefixLift 4537200
  have htrace : WordTrace (prefixWord ++ tailWord_4537200) baseStart_4537200 baseEnd_4537200 := by
    simpa [prefixWord, tailWord_4537200, baseEnd_4537200] using wordTrace_append hprefix tailTrace_4537200
  have hstable : (prefixWord ++ tailWord_4537200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537200).length < 2 ^ (prefixWord ++ tailWord_4537200).sum := by decide
  have hdescent : baseEnd_4537200 < baseStart_4537200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537213 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4537213 : Nat := 118140960795 + 4537213 * 2 ^ 59
def prefixEnd_4537213 : Nat := 4983230072969 + 3 ^ 40 * 4537213 * 2
def baseEnd_4537213 : Nat := 776590366942753955657081

theorem tailTrace_4537213 : CollatzResearch.WordTrace tailWord_4537213 prefixEnd_4537213 776590366942753955657081 := by
  unfold tailWord_4537213
  simp only [CollatzResearch.WordTrace]
  refine ⟨165485753311459670133024293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110323835540973113422016195 165485753311459670133024293)
  ·
    refine ⟨31028578745898688149942055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165485753311459670133024293 31028578745898688149942055)
    ·
      refine ⟨46542868118848032224913083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31028578745898688149942055 46542868118848032224913083)
      ·
        refine ⟨69814302178272048337369625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46542868118848032224913083 69814302178272048337369625)
        ·
          refine ⟨52360726633704036253027219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69814302178272048337369625 52360726633704036253027219)
          ·
            refine ⟨78541089950556054379540829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52360726633704036253027219 78541089950556054379540829)
            ·
              refine ⟨29452908731458520392327811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78541089950556054379540829 29452908731458520392327811)
              ·
                refine ⟨44179363097187780588491717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29452908731458520392327811 44179363097187780588491717)
                ·
                  refine ⟨8283630580722708860342197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44179363097187780588491717 8283630580722708860342197)
                  ·
                    refine ⟨776590366942753955657081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8283630580722708860342197 776590366942753955657081)
                    ·
                      rfl

theorem cell23_4537213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4537213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537213 prefixEnd_4537213 := by exact prefixLift 4537213
  have htrace : WordTrace (prefixWord ++ tailWord_4537213) baseStart_4537213 baseEnd_4537213 := by
    simpa [prefixWord, tailWord_4537213, baseEnd_4537213] using wordTrace_append hprefix tailTrace_4537213
  have hstable : (prefixWord ++ tailWord_4537213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537213).length < 2 ^ (prefixWord ++ tailWord_4537213).sum := by decide
  have hdescent : baseEnd_4537213 < baseStart_4537213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537220 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_4537220 : Nat := 118140960795 + 4537220 * 2 ^ 59
def prefixEnd_4537220 : Nat := 4983230072969 + 3 ^ 40 * 4537220 * 2
def baseEnd_4537220 : Nat := 2329774695192843339583711

theorem tailTrace_4537220 : CollatzResearch.WordTrace tailWord_4537220 prefixEnd_4537220 2329774695192843339583711 := by
  unfold tailWord_4537220
  simp only [CollatzResearch.WordTrace]
  refine ⟨82743004311217155164264557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110324005748289540219019409 82743004311217155164264557)
  ·
    refine ⟨31028626616706433186599209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82743004311217155164264557 31028626616706433186599209)
    ·
      refine ⟨23271469962529824889949407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31028626616706433186599209 23271469962529824889949407)
      ·
        refine ⟨34907204943794737334924111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23271469962529824889949407 34907204943794737334924111)
        ·
          refine ⟨52360807415692106002386167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34907204943794737334924111 52360807415692106002386167)
          ·
            refine ⟨78541211123538159003579251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52360807415692106002386167 78541211123538159003579251)
            ·
              refine ⟨117811816685307238505368877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78541211123538159003579251 117811816685307238505368877)
              ·
                refine ⟨44179431256990214439513329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117811816685307238505368877 44179431256990214439513329)
                ·
                  refine ⟨33134573442742660829634997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44179431256990214439513329 33134573442742660829634997)
                  ·
                    refine ⟨3106366260257124452778281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33134573442742660829634997 3106366260257124452778281)
                    ·
                      refine ⟨2329774695192843339583711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106366260257124452778281 2329774695192843339583711)
                      ·
                        rfl

theorem cell23_4537220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_4537220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537220 prefixEnd_4537220 := by exact prefixLift 4537220
  have htrace : WordTrace (prefixWord ++ tailWord_4537220) baseStart_4537220 baseEnd_4537220 := by
    simpa [prefixWord, tailWord_4537220, baseEnd_4537220] using wordTrace_append hprefix tailTrace_4537220
  have hstable : (prefixWord ++ tailWord_4537220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537220).length < 2 ^ (prefixWord ++ tailWord_4537220).sum := by decide
  have hdescent : baseEnd_4537220 < baseStart_4537220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537223 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4537223 : Nat := 118140960795 + 4537223 * 2 ^ 59
def prefixEnd_4537223 : Nat := 4983230072969 + 3 ^ 40 * 4537223 * 2
def baseEnd_4537223 : Nat := 2329776235634806827846197

theorem tailTrace_4537223 : CollatzResearch.WordTrace tailWord_4537223 prefixEnd_4537223 2329776235634806827846197 := by
  unfold tailWord_4537223
  simp only [CollatzResearch.WordTrace]
  refine ⟨165486118041423441840888323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110324078694282294560592215 165486118041423441840888323)
  ·
    refine ⟨248229177062135162761332485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165486118041423441840888323 248229177062135162761332485)
    ·
      refine ⟨46542970699150343017749841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248229177062135162761332485 46542970699150343017749841)
      ·
        refine ⟨34907228024362757263312381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46542970699150343017749841 34907228024362757263312381)
        ·
          refine ⟨13090210509136033973742143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34907228024362757263312381 13090210509136033973742143)
          ·
            refine ⟨19635315763704050960613215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13090210509136033973742143 19635315763704050960613215)
            ·
              refine ⟨29452973645556076440919823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19635315763704050960613215 29452973645556076440919823)
              ·
                refine ⟨44179460468334114661379735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29452973645556076440919823 44179460468334114661379735)
                ·
                  refine ⟨66269190702501171992069603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44179460468334114661379735 66269190702501171992069603)
                  ·
                    refine ⟨99403786053751757988104405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66269190702501171992069603 99403786053751757988104405)
                    ·
                      refine ⟨2329776235634806827846197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99403786053751757988104405 2329776235634806827846197)
                      ·
                        rfl

theorem cell23_4537223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4537223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537223 prefixEnd_4537223 := by exact prefixLift 4537223
  have htrace : WordTrace (prefixWord ++ tailWord_4537223) baseStart_4537223 baseEnd_4537223 := by
    simpa [prefixWord, tailWord_4537223, baseEnd_4537223] using wordTrace_append hprefix tailTrace_4537223
  have hstable : (prefixWord ++ tailWord_4537223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537223).length < 2 ^ (prefixWord ++ tailWord_4537223).sum := by decide
  have hdescent : baseEnd_4537223 < baseStart_4537223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537233 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_4537233 : Nat := 118140960795 + 4537233 * 2 ^ 59
def prefixEnd_4537233 : Nat := 4983230072969 + 3 ^ 40 * 4537233 * 2
def baseEnd_4537233 : Nat := 2329781370441351788721151

theorem tailTrace_4537233 : CollatzResearch.WordTrace tailWord_4537233 prefixEnd_4537233 2329781370441351788721151 := by
  unfold tailWord_4537233
  simp only [CollatzResearch.WordTrace]
  refine ⟨165486482771387213548752353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110324321847591475699168235 165486482771387213548752353)
  ·
    refine ⟨124114862078540410161564265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165486482771387213548752353 124114862078540410161564265)
    ·
      refine ⟨93086146558905307621173199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124114862078540410161564265 93086146558905307621173199)
      ·
        refine ⟨139629219838357961431759799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93086146558905307621173199 139629219838357961431759799)
        ·
          refine ⟨209443829757536942147639699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139629219838357961431759799 209443829757536942147639699)
          ·
            refine ⟨314165744636305413221459549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209443829757536942147639699 314165744636305413221459549)
            ·
              refine ⟨117812154238614529958047331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314165744636305413221459549 117812154238614529958047331)
              ·
                refine ⟨176718231357921794937070997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117812154238614529958047331 176718231357921794937070997)
                ·
                  refine ⟨8283667094902584137675203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176718231357921794937070997 8283667094902584137675203)
                  ·
                    refine ⟨12425500642353876206512805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8283667094902584137675203 12425500642353876206512805)
                    ·
                      refine ⟨2329781370441351788721151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12425500642353876206512805 2329781370441351788721151)
                      ·
                        rfl

theorem cell23_4537233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_4537233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537233 prefixEnd_4537233 := by exact prefixLift 4537233
  have htrace : WordTrace (prefixWord ++ tailWord_4537233) baseStart_4537233 baseEnd_4537233 := by
    simpa [prefixWord, tailWord_4537233, baseEnd_4537233] using wordTrace_append hprefix tailTrace_4537233
  have hstable : (prefixWord ++ tailWord_4537233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537233).length < 2 ^ (prefixWord ++ tailWord_4537233).sum := by decide
  have hdescent : baseEnd_4537233 < baseStart_4537233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537313 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4537313 : Nat := 118140960795 + 4537313 * 2 ^ 59
def prefixEnd_4537313 : Nat := 4983230072969 + 3 ^ 40 * 4537313 * 2
def baseEnd_4537313 : Nat := 2329822448893711475720783

theorem tailTrace_4537313 : CollatzResearch.WordTrace tailWord_4537313 prefixEnd_4537313 2329822448893711475720783 := by
  unfold tailWord_4537313
  simp only [CollatzResearch.WordTrace]
  refine ⟨165489400611097387211664593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110326267074064924807776395 165489400611097387211664593)
  ·
    refine ⟨124117050458323040408748445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165489400611097387211664593 124117050458323040408748445)
    ·
      refine ⟨46543893921871140153280667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124117050458323040408748445 46543893921871140153280667)
      ·
        refine ⟨69815840882806710229921001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46543893921871140153280667 69815840882806710229921001)
        ·
          refine ⟨52361880662105032672440751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69815840882806710229921001 52361880662105032672440751)
          ·
            refine ⟨78542820993157549008661127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52361880662105032672440751 78542820993157549008661127)
            ·
              refine ⟨117814231489736323512991691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78542820993157549008661127 117814231489736323512991691)
              ·
                refine ⟨176721347234604485269487537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117814231489736323512991691 176721347234604485269487537)
                ·
                  refine ⟨132541010425953363952115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176721347234604485269487537 132541010425953363952115653)
                  ·
                    refine ⟨24851439454866255741021685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132541010425953363952115653 24851439454866255741021685)
                    ·
                      refine ⟨2329822448893711475720783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24851439454866255741021685 2329822448893711475720783)
                      ·
                        rfl

theorem cell23_4537313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4537313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537313 prefixEnd_4537313 := by exact prefixLift 4537313
  have htrace : WordTrace (prefixWord ++ tailWord_4537313) baseStart_4537313 baseEnd_4537313 := by
    simpa [prefixWord, tailWord_4537313, baseEnd_4537313] using wordTrace_append hprefix tailTrace_4537313
  have hstable : (prefixWord ++ tailWord_4537313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537313).length < 2 ^ (prefixWord ++ tailWord_4537313).sum := by decide
  have hdescent : baseEnd_4537313 < baseStart_4537313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537334 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4537334 : Nat := 118140960795 + 4537334 * 2 ^ 59
def prefixEnd_4537334 : Nat := 4983230072969 + 3 ^ 40 * 4537334 * 2
def baseEnd_4537334 : Nat := 2329833231987455893558187

theorem tailTrace_4537334 : CollatzResearch.WordTrace tailWord_4537334 prefixEnd_4537334 2329833231987455893558187 := by
  unfold tailWord_4537334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343135409001331737386191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110326777696014205198786037 10343135409001331737386191)
  ·
    refine ⟨15514703113501997606079287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10343135409001331737386191 15514703113501997606079287)
    ·
      refine ⟨23272054670252996409118931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15514703113501997606079287 23272054670252996409118931)
      ·
        refine ⟨34908082005379494613678397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23272054670252996409118931 34908082005379494613678397)
        ·
          refine ⟨13090530752017310480129399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34908082005379494613678397 13090530752017310480129399)
          ·
            refine ⟨19635796128025965720194099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13090530752017310480129399 19635796128025965720194099)
            ·
              refine ⟨29453694192038948580291149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19635796128025965720194099 29453694192038948580291149)
              ·
                refine ⟨11045135322014605717609181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29453694192038948580291149 11045135322014605717609181)
                ·
                  refine ⟨4141925745755477144103443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11045135322014605717609181 4141925745755477144103443)
                  ·
                    refine ⟨6212888618633215716155165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4141925745755477144103443 6212888618633215716155165)
                    ·
                      refine ⟨2329833231987455893558187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6212888618633215716155165 2329833231987455893558187)
                      ·
                        rfl

theorem cell23_4537334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4537334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537334 prefixEnd_4537334 := by exact prefixLift 4537334
  have htrace : WordTrace (prefixWord ++ tailWord_4537334) baseStart_4537334 baseEnd_4537334 := by
    simpa [prefixWord, tailWord_4537334, baseEnd_4537334] using wordTrace_append hprefix tailTrace_4537334
  have hstable : (prefixWord ++ tailWord_4537334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537334).length < 2 ^ (prefixWord ++ tailWord_4537334).sum := by decide
  have hdescent : baseEnd_4537334 < baseStart_4537334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537362 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4537362 : Nat := 118140960795 + 4537362 * 2 ^ 59
def prefixEnd_4537362 : Nat := 4983230072969 + 3 ^ 40 * 4537362 * 2
def baseEnd_4537362 : Nat := 776615869815260594669353

theorem tailTrace_4537362 : CollatzResearch.WordTrace tailWord_4537362 prefixEnd_4537362 776615869815260594669353 := by
  unfold tailWord_4537362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41372796946979967145049585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110327458525279912386798893 41372796946979967145049585)
  ·
    refine ⟨31029597710234975358787189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41372796946979967145049585 31029597710234975358787189)
    ·
      refine ⟨2909024785334528939886299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31029597710234975358787189 2909024785334528939886299)
      ·
        refine ⟨4363537178001793409829449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909024785334528939886299 4363537178001793409829449)
        ·
          refine ⟨3272652883501345057372087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363537178001793409829449 3272652883501345057372087)
          ·
            refine ⟨4908979325252017586058131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272652883501345057372087 4908979325252017586058131)
            ·
              refine ⟨7363468987878026379087197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908979325252017586058131 7363468987878026379087197)
              ·
                refine ⟨2761300870454259892157699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7363468987878026379087197 2761300870454259892157699)
                ·
                  refine ⟨4141951305681389838236549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761300870454259892157699 4141951305681389838236549)
                  ·
                    refine ⟨776615869815260594669353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141951305681389838236549 776615869815260594669353)
                    ·
                      rfl

theorem cell23_4537362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4537362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537362 prefixEnd_4537362 := by exact prefixLift 4537362
  have htrace : WordTrace (prefixWord ++ tailWord_4537362) baseStart_4537362 baseEnd_4537362 := by
    simpa [prefixWord, tailWord_4537362, baseEnd_4537362] using wordTrace_append hprefix tailTrace_4537362
  have hstable : (prefixWord ++ tailWord_4537362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537362).length < 2 ^ (prefixWord ++ tailWord_4537362).sum := by decide
  have hdescent : baseEnd_4537362 < baseStart_4537362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537367 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 4, 4]
def baseStart_4537367 : Nat := 118140960795 + 4537367 * 2 ^ 59
def prefixEnd_4537367 : Nat := 4983230072969 + 3 ^ 40 * 4537367 * 2
def baseEnd_4537367 : Nat := 776616725616351421481845

theorem tailTrace_4537367 : CollatzResearch.WordTrace tailWord_4537367 prefixEnd_4537367 776616725616351421481845 := by
  unfold tailWord_4537367
  simp only [CollatzResearch.WordTrace]
  refine ⟨165491370152901754434130355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110327580101934502956086903 165491370152901754434130355)
  ·
    refine ⟨248237055229352631651195533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165491370152901754434130355 248237055229352631651195533)
    ·
      refine ⟨93088895711007236869198325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248237055229352631651195533 93088895711007236869198325)
      ·
        refine ⟨8727083972906928456487343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93088895711007236869198325 8727083972906928456487343)
        ·
          refine ⟨13090625959360392684731015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8727083972906928456487343 13090625959360392684731015)
          ·
            refine ⟨19635938939040589027096523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13090625959360392684731015 19635938939040589027096523)
            ·
              refine ⟨29453908408560883540644785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19635938939040589027096523 29453908408560883540644785)
              ·
                refine ⟨22090431306420662655483589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29453908408560883540644785 22090431306420662655483589)
                ·
                  refine ⟨4141955869953874247903173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22090431306420662655483589 4141955869953874247903173)
                  ·
                    refine ⟨776616725616351421481845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141955869953874247903173 776616725616351421481845)
                    ·
                      rfl

theorem cell23_4537367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_4537367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537367 prefixEnd_4537367 := by exact prefixLift 4537367
  have htrace : WordTrace (prefixWord ++ tailWord_4537367) baseStart_4537367 baseEnd_4537367 := by
    simpa [prefixWord, tailWord_4537367, baseEnd_4537367] using wordTrace_append hprefix tailTrace_4537367
  have hstable : (prefixWord ++ tailWord_4537367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537367).length < 2 ^ (prefixWord ++ tailWord_4537367).sum := by decide
  have hdescent : baseEnd_4537367 < baseStart_4537367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537370 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_4537370 : Nat := 118140960795 + 4537370 * 2 ^ 59
def prefixEnd_4537370 : Nat := 4983230072969 + 3 ^ 40 * 4537370 * 2
def baseEnd_4537370 : Nat := 2329851717291017752708021

theorem tailTrace_4537370 : CollatzResearch.WordTrace tailWord_4537370 prefixEnd_4537370 2329851717291017752708021 := by
  unfold tailWord_4537370
  simp only [CollatzResearch.WordTrace]
  refine ⟨41372869892972721486622391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110327653047927257297659709 41372869892972721486622391)
  ·
    refine ⟨62059304839459082229933587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41372869892972721486622391 62059304839459082229933587)
    ·
      refine ⟨93088957259188623344900381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62059304839459082229933587 93088957259188623344900381)
      ·
        refine ⟨34908358972195733754337643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93088957259188623344900381 34908358972195733754337643)
        ·
          refine ⟨52362538458293600631506465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34908358972195733754337643 52362538458293600631506465)
          ·
            refine ⟨39271903843720200473629849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52362538458293600631506465 39271903843720200473629849)
            ·
              refine ⟨29453927882790150355222387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39271903843720200473629849 29453927882790150355222387)
              ·
                refine ⟨44180891824185225532833581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29453927882790150355222387 44180891824185225532833581)
                ·
                  refine ⟨16567834434069459574812593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44180891824185225532833581 16567834434069459574812593)
                  ·
                    refine ⟨12425875825552094681109445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16567834434069459574812593 12425875825552094681109445)
                    ·
                      refine ⟨2329851717291017752708021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12425875825552094681109445 2329851717291017752708021)
                      ·
                        rfl

theorem cell23_4537370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_4537370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537370 prefixEnd_4537370 := by exact prefixLift 4537370
  have htrace : WordTrace (prefixWord ++ tailWord_4537370) baseStart_4537370 baseEnd_4537370 := by
    simpa [prefixWord, tailWord_4537370, baseEnd_4537370] using wordTrace_append hprefix tailTrace_4537370
  have hstable : (prefixWord ++ tailWord_4537370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537370).length < 2 ^ (prefixWord ++ tailWord_4537370).sum := by decide
  have hdescent : baseEnd_4537370 < baseStart_4537370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537377 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4537377 : Nat := 118140960795 + 4537377 * 2 ^ 59
def prefixEnd_4537377 : Nat := 4983230072969 + 3 ^ 40 * 4537377 * 2
def baseEnd_4537377 : Nat := 2329855311655599225320489

theorem tailTrace_4537377 : CollatzResearch.WordTrace tailWord_4537377 prefixEnd_4537377 2329855311655599225320489 := by
  unfold tailWord_4537377
  simp only [CollatzResearch.WordTrace]
  refine ⟨165491734882865526141994385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110327823255243684094662923 165491734882865526141994385)
  ·
    refine ⟨124118801162149144606495789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165491734882865526141994385 124118801162149144606495789)
    ·
      refine ⟨46544550435805929227435921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124118801162149144606495789 46544550435805929227435921)
      ·
        refine ⟨34908412826854446920576941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46544550435805929227435921 34908412826854446920576941)
        ·
          refine ⟨13090654810070417595216353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34908412826854446920576941 13090654810070417595216353)
          ·
            refine ⟨9817991107552813196412265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13090654810070417595216353 9817991107552813196412265)
            ·
              refine ⟨7363493330664609897309199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9817991107552813196412265 7363493330664609897309199)
              ·
                refine ⟨11045239995996914845963799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363493330664609897309199 11045239995996914845963799)
                ·
                  refine ⟨16567859993995372268945699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11045239995996914845963799 16567859993995372268945699)
                  ·
                    refine ⟨24851789990993058403418549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16567859993995372268945699 24851789990993058403418549)
                    ·
                      refine ⟨2329855311655599225320489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24851789990993058403418549 2329855311655599225320489)
                      ·
                        rfl

theorem cell23_4537377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4537377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537377 prefixEnd_4537377 := by exact prefixLift 4537377
  have htrace : WordTrace (prefixWord ++ tailWord_4537377) baseStart_4537377 baseEnd_4537377 := by
    simpa [prefixWord, tailWord_4537377, baseEnd_4537377] using wordTrace_append hprefix tailTrace_4537377
  have hstable : (prefixWord ++ tailWord_4537377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537377).length < 2 ^ (prefixWord ++ tailWord_4537377).sum := by decide
  have hdescent : baseEnd_4537377 < baseStart_4537377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537380 : List Nat := [2, 3, 1, 4, 1, 1, 11]
def baseStart_4537380 : Nat := 118140960795 + 4537380 * 2 ^ 59
def prefixEnd_4537380 : Nat := 4983230072969 + 3 ^ 40 * 4537380 * 2
def baseEnd_4537380 : Nat := 28763664840710650784975

theorem tailTrace_4537380 : CollatzResearch.WordTrace tailWord_4537380 prefixEnd_4537380 28763664840710650784975 := by
  unfold tailWord_4537380
  simp only [CollatzResearch.WordTrace]
  refine ⟨82745922150927328827176797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110327896201236438436235729 82745922150927328827176797)
  ·
    refine ⟨31029720806597748310191299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82745922150927328827176797 31029720806597748310191299)
    ·
      refine ⟨46544581209896622465286949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31029720806597748310191299 46544581209896622465286949)
      ·
        refine ⟨8727108976855616712241303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46544581209896622465286949 8727108976855616712241303)
        ·
          refine ⟨13090663465283425068361955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8727108976855616712241303 13090663465283425068361955)
          ·
            refine ⟨19635995197925137602542933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13090663465283425068361955 19635995197925137602542933)
            ·
              refine ⟨28763664840710650784975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19635995197925137602542933 28763664840710650784975)
              ·
                rfl

theorem cell23_4537380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 11].length) (baseStart_4537380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537380 prefixEnd_4537380 := by exact prefixLift 4537380
  have htrace : WordTrace (prefixWord ++ tailWord_4537380) baseStart_4537380 baseEnd_4537380 := by
    simpa [prefixWord, tailWord_4537380, baseEnd_4537380] using wordTrace_append hprefix tailTrace_4537380
  have hstable : (prefixWord ++ tailWord_4537380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537380).length < 2 ^ (prefixWord ++ tailWord_4537380).sum := by decide
  have hdescent : baseEnd_4537380 < baseStart_4537380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537401 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 2, 4]
def baseStart_4537401 : Nat := 118140960795 + 4537401 * 2 ^ 59
def prefixEnd_4537401 : Nat := 4983230072969 + 3 ^ 40 * 4537401 * 2
def baseEnd_4537401 : Nat := 776622545063769043806793

theorem tailTrace_4537401 : CollatzResearch.WordTrace tailWord_4537401 prefixEnd_4537401 776622545063769043806793 := by
  unfold tailWord_4537401
  simp only [CollatzResearch.WordTrace]
  refine ⟨165492610234778578240868057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110328406823185718827245371 165492610234778578240868057)
  ·
    refine ⟨124119457676083933680651043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165492610234778578240868057 124119457676083933680651043)
    ·
      refine ⟨186179186514125900520976565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124119457676083933680651043 186179186514125900520976565)
      ·
        refine ⟨17454298735699303173841553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186179186514125900520976565 17454298735699303173841553)
        ·
          refine ⟨13090724051774477380381165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17454298735699303173841553 13090724051774477380381165)
          ·
            refine ⟨4909021519415429017642937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13090724051774477380381165 4909021519415429017642937)
            ·
              refine ⟨3681766139561571763232203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4909021519415429017642937 3681766139561571763232203)
              ·
                refine ⟨5522649209342357644848305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681766139561571763232203 5522649209342357644848305)
                ·
                  refine ⟨4141986907006768233636229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5522649209342357644848305 4141986907006768233636229)
                  ·
                    refine ⟨776622545063769043806793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141986907006768233636229 776622545063769043806793)
                    ·
                      rfl

theorem cell23_4537401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_4537401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537401 prefixEnd_4537401 := by exact prefixLift 4537401
  have htrace : WordTrace (prefixWord ++ tailWord_4537401) baseStart_4537401 baseEnd_4537401 := by
    simpa [prefixWord, tailWord_4537401, baseEnd_4537401] using wordTrace_append hprefix tailTrace_4537401
  have hstable : (prefixWord ++ tailWord_4537401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537401).length < 2 ^ (prefixWord ++ tailWord_4537401).sum := by decide
  have hdescent : baseEnd_4537401 < baseStart_4537401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537440 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_4537440 : Nat := 118140960795 + 4537440 * 2 ^ 59
def prefixEnd_4537440 : Nat := 4983230072969 + 3 ^ 40 * 4537440 * 2
def baseEnd_4537440 : Nat := 776629220312277492944233

theorem tailTrace_4537440 : CollatzResearch.WordTrace tailWord_4537440 prefixEnd_4537440 776629220312277492944233 := by
  unfold tailWord_4537440
  simp only [CollatzResearch.WordTrace]
  refine ⟨82747016340818643950768887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110329355121091525267691849 82747016340818643950768887)
  ·
    refine ⟨124120524511227965926153331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82747016340818643950768887 124120524511227965926153331)
    ·
      refine ⟨186180786766841948889229997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124120524511227965926153331 186180786766841948889229997)
      ·
        refine ⟨69817795037565730833461249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186180786766841948889229997 69817795037565730833461249)
        ·
          refine ⟨52363346278174298125095937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69817795037565730833461249 52363346278174298125095937)
          ·
            refine ⟨39272509708630723593821953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52363346278174298125095937 39272509708630723593821953)
            ·
              refine ⟨29454382281473042695366465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39272509708630723593821953 29454382281473042695366465)
              ·
                refine ⟨22090786711104782021524849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29454382281473042695366465 22090786711104782021524849)
                ·
                  refine ⟨16568090033328586516143637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22090786711104782021524849 16568090033328586516143637)
                  ·
                    refine ⟨776629220312277492944233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16568090033328586516143637 776629220312277492944233)
                    ·
                      rfl

theorem cell23_4537440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_4537440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537440 prefixEnd_4537440 := by exact prefixLift 4537440
  have htrace : WordTrace (prefixWord ++ tailWord_4537440) baseStart_4537440 baseEnd_4537440 := by
    simpa [prefixWord, tailWord_4537440, baseEnd_4537440] using wordTrace_append hprefix tailTrace_4537440
  have hstable : (prefixWord ++ tailWord_4537440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537440).length < 2 ^ (prefixWord ++ tailWord_4537440).sum := by decide
  have hdescent : baseEnd_4537440 < baseStart_4537440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537442 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4537442 : Nat := 118140960795 + 4537442 * 2 ^ 59
def prefixEnd_4537442 : Nat := 4983230072969 + 3 ^ 40 * 4537442 * 2
def baseEnd_4537442 : Nat := 2329888687898141471007691

theorem tailTrace_4537442 : CollatzResearch.WordTrace tailWord_4537442 prefixEnd_4537442 2329888687898141471007691 := by
  unfold tailWord_4537442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41373526406907510560777645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110329403751753361495407053 41373526406907510560777645)
  ·
    refine ⟨15515072402590316460291617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41373526406907510560777645 15515072402590316460291617)
    ·
      refine ⟨11636304301942737345218713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15515072402590316460291617 11636304301942737345218713)
      ·
        refine ⟨8727228226457053008914035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11636304301942737345218713 8727228226457053008914035)
        ·
          refine ⟨13090842339685579513371053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8727228226457053008914035 13090842339685579513371053)
          ·
            refine ⟨4909065877382092317514145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13090842339685579513371053 4909065877382092317514145)
            ·
              refine ⟨3681799408036569238135609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4909065877382092317514145 3681799408036569238135609)
              ·
                refine ⟨2761349556027426928601707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3681799408036569238135609 2761349556027426928601707)
                ·
                  refine ⟨4142024334041140392902561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761349556027426928601707 4142024334041140392902561)
                  ·
                    refine ⟨3106518250530855294676921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142024334041140392902561 3106518250530855294676921)
                    ·
                      refine ⟨2329888687898141471007691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106518250530855294676921 2329888687898141471007691)
                      ·
                        rfl

theorem cell23_4537442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4537442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537442 prefixEnd_4537442 := by exact prefixLift 4537442
  have htrace : WordTrace (prefixWord ++ tailWord_4537442) baseStart_4537442 baseEnd_4537442 := by
    simpa [prefixWord, tailWord_4537442, baseEnd_4537442] using wordTrace_append hprefix tailTrace_4537442
  have hstable : (prefixWord ++ tailWord_4537442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537442).length < 2 ^ (prefixWord ++ tailWord_4537442).sum := by decide
  have hdescent : baseEnd_4537442 < baseStart_4537442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537498 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4537498 : Nat := 118140960795 + 4537498 * 2 ^ 59
def prefixEnd_4537498 : Nat := 4983230072969 + 3 ^ 40 * 4537498 * 2
def baseEnd_4537498 : Nat := 2329917442814793251907433

theorem tailTrace_4537498 : CollatzResearch.WordTrace tailWord_4537498 prefixEnd_4537498 2329917442814793251907433 := by
  unfold tailWord_4537498
  simp only [CollatzResearch.WordTrace]
  refine ⟨41374037028856790951787287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110330765410284775871432765 41374037028856790951787287)
  ·
    refine ⟨62061055543285186427680931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41374037028856790951787287 62061055543285186427680931)
    ·
      refine ⟨93091583314927779641521397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62061055543285186427680931 93091583314927779641521397)
      ·
        refine ⟨8727335935774479341392631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93091583314927779641521397 8727335935774479341392631)
        ·
          refine ⟨13091003903661719012088947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8727335935774479341392631 13091003903661719012088947)
          ·
            refine ⟨19636505855492578518133421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13091003903661719012088947 19636505855492578518133421)
            ·
              refine ⟨7363689695809716944300033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19636505855492578518133421 7363689695809716944300033)
              ·
                refine ⟨5522767271857287708225025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7363689695809716944300033 5522767271857287708225025)
                ·
                  refine ⟨4142075453892965781168769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5522767271857287708225025 4142075453892965781168769)
                  ·
                    refine ⟨3106556590419724335876577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142075453892965781168769 3106556590419724335876577)
                    ·
                      refine ⟨2329917442814793251907433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106556590419724335876577 2329917442814793251907433)
                      ·
                        rfl

theorem cell23_4537498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4537498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537498 prefixEnd_4537498 := by exact prefixLift 4537498
  have htrace : WordTrace (prefixWord ++ tailWord_4537498) baseStart_4537498 baseEnd_4537498 := by
    simpa [prefixWord, tailWord_4537498, baseEnd_4537498] using wordTrace_append hprefix tailTrace_4537498
  have hstable : (prefixWord ++ tailWord_4537498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537498).length < 2 ^ (prefixWord ++ tailWord_4537498).sum := by decide
  have hdescent : baseEnd_4537498 < baseStart_4537498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537507 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 7, 2]
def baseStart_4537507 : Nat := 118140960795 + 4537507 * 2 ^ 59
def prefixEnd_4537507 : Nat := 4983230072969 + 3 ^ 40 * 4537507 * 2
def baseEnd_4537507 : Nat := 2329922064140683716694891

theorem tailTrace_4537507 : CollatzResearch.WordTrace tailWord_4537507 prefixEnd_4537507 2329922064140683716694891 := by
  unfold tailWord_4537507
  simp only [CollatzResearch.WordTrace]
  refine ⟨165496476372394558344226775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110330984248263038896151183 165496476372394558344226775)
  ·
    refine ⟨248244714558591837516340163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165496476372394558344226775 248244714558591837516340163)
    ·
      refine ⟨372367071837887756274510245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248244714558591837516340163 372367071837887756274510245)
      ·
        refine ⟨69818825969603954301470671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372367071837887756274510245 69818825969603954301470671)
        ·
          refine ⟨104728238954405931452206007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69818825969603954301470671 104728238954405931452206007)
          ·
            refine ⟨157092358431608897178309011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104728238954405931452206007 157092358431608897178309011)
            ·
              refine ⟨235638537647413345767463517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157092358431608897178309011 235638537647413345767463517)
              ·
                refine ⟨88364451617780004662798819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235638537647413345767463517 88364451617780004662798819)
                ·
                  refine ⟨132546677426670006994198229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88364451617780004662798819 132546677426670006994198229)
                  ·
                    refine ⟨3106562752187578288926521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 132546677426670006994198229 3106562752187578288926521)
                    ·
                      refine ⟨2329922064140683716694891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106562752187578288926521 2329922064140683716694891)
                      ·
                        rfl

theorem cell23_4537507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_4537507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537507 prefixEnd_4537507 := by exact prefixLift 4537507
  have htrace : WordTrace (prefixWord ++ tailWord_4537507) baseStart_4537507 baseEnd_4537507 := by
    simpa [prefixWord, tailWord_4537507, baseEnd_4537507] using wordTrace_append hprefix tailTrace_4537507
  have hstable : (prefixWord ++ tailWord_4537507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537507).length < 2 ^ (prefixWord ++ tailWord_4537507).sum := by decide
  have hdescent : baseEnd_4537507 < baseStart_4537507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537530 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_4537530 : Nat := 118140960795 + 4537530 * 2 ^ 59
def prefixEnd_4537530 : Nat := 4983230072969 + 3 ^ 40 * 4537530 * 2
def baseEnd_4537530 : Nat := 776644624731912375569095

theorem tailTrace_4537530 : CollatzResearch.WordTrace tailWord_4537530 prefixEnd_4537530 776644624731912375569095 := by
  unfold tailWord_4537530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41374328812827808318078511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110331543500874155514876029 41374328812827808318078511)
  ·
    refine ⟨62061493219241712477117767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41374328812827808318078511 62061493219241712477117767)
    ·
      refine ⟨93092239828862568715676651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62061493219241712477117767 93092239828862568715676651)
      ·
        refine ⟨139638359743293853073514977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93092239828862568715676651 139638359743293853073514977)
        ·
          refine ⟨104728769807470389805136233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139638359743293853073514977 104728769807470389805136233)
          ·
            refine ⟨78546577355602792353852175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104728769807470389805136233 78546577355602792353852175)
            ·
              refine ⟨117819866033404188530778263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78546577355602792353852175 117819866033404188530778263)
              ·
                refine ⟨176729799050106282796167395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117819866033404188530778263 176729799050106282796167395)
                ·
                  refine ⟨265094698575159424194251093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176729799050106282796167395 265094698575159424194251093)
                  ·
                    refine ⟨776644624731912375569095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 265094698575159424194251093 776644624731912375569095)
                    ·
                      rfl

theorem cell23_4537530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_4537530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537530 prefixEnd_4537530 := by exact prefixLift 4537530
  have htrace : WordTrace (prefixWord ++ tailWord_4537530) baseStart_4537530 baseEnd_4537530 := by
    simpa [prefixWord, tailWord_4537530, baseEnd_4537530] using wordTrace_append hprefix tailTrace_4537530
  have hstable : (prefixWord ++ tailWord_4537530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537530).length < 2 ^ (prefixWord ++ tailWord_4537530).sum := by decide
  have hdescent : baseEnd_4537530 < baseStart_4537530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537554 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4537554 : Nat := 118140960795 + 4537554 * 2 ^ 59
def prefixEnd_4537554 : Nat := 4983230072969 + 3 ^ 40 * 4537554 * 2
def baseEnd_4537554 : Nat := 2329946197731445032807175

theorem tailTrace_4537554 : CollatzResearch.WordTrace tailWord_4537554 prefixEnd_4537554 2329946197731445032807175 := by
  unfold tailWord_4537554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41374547650806071342796929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110332127068816190247458477 41374547650806071342796929)
  ·
    refine ⟨31030910738104553507097697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41374547650806071342796929 31030910738104553507097697)
    ·
      refine ⟨23273183053578415130323273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31030910738104553507097697 23273183053578415130323273)
      ·
        refine ⟨17454887290183811347742455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23273183053578415130323273 17454887290183811347742455)
        ·
          refine ⟨26182330935275717021613683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17454887290183811347742455 26182330935275717021613683)
          ·
            refine ⟨39273496402913575532420525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26182330935275717021613683 39273496402913575532420525)
            ·
              refine ⟨14727561151092590824657697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39273496402913575532420525 14727561151092590824657697)
              ·
                refine ⟨11045670863319443118493273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14727561151092590824657697 11045670863319443118493273)
                ·
                  refine ⟨8284253147489582338869955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11045670863319443118493273 8284253147489582338869955)
                  ·
                    refine ⟨12426379721234373508304933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8284253147489582338869955 12426379721234373508304933)
                    ·
                      refine ⟨2329946197731445032807175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12426379721234373508304933 2329946197731445032807175)
                      ·
                        rfl

theorem cell23_4537554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4537554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537554 prefixEnd_4537554 := by exact prefixLift 4537554
  have htrace : WordTrace (prefixWord ++ tailWord_4537554) baseStart_4537554 baseEnd_4537554 := by
    simpa [prefixWord, tailWord_4537554, baseEnd_4537554] using wordTrace_append hprefix tailTrace_4537554
  have hstable : (prefixWord ++ tailWord_4537554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537554).length < 2 ^ (prefixWord ++ tailWord_4537554).sum := by decide
  have hdescent : baseEnd_4537554 < baseStart_4537554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537644 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_4537644 : Nat := 118140960795 + 4537644 * 2 ^ 59
def prefixEnd_4537644 : Nat := 4983230072969 + 3 ^ 40 * 4537644 * 2
def baseEnd_4537644 : Nat := 2329992410990349680681761

theorem tailTrace_4537644 : CollatzResearch.WordTrace tailWord_4537644 prefixEnd_4537644 2329992410990349680681761 := by
  unfold tailWord_4537644
  simp only [CollatzResearch.WordTrace]
  refine ⟨82750736586449115370981993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110334315448598820494642657 82750736586449115370981993)
  ·
    refine ⟨62063052439836836528236495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82750736586449115370981993 62063052439836836528236495)
    ·
      refine ⟨93094578659755254792354743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62063052439836836528236495 93094578659755254792354743)
      ·
        refine ⟨139641867989632882188532115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93094578659755254792354743 139641867989632882188532115)
        ·
          refine ⟨209462801984449323282798173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139641867989632882188532115 209462801984449323282798173)
          ·
            refine ⟨78548550744168496231049315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209462801984449323282798173 78548550744168496231049315)
            ·
              refine ⟨117822826116252744346573973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78548550744168496231049315 117822826116252744346573973)
              ·
                refine ⟨5522944974199347391245655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117822826116252744346573973 5522944974199347391245655)
                ·
                  refine ⟨8284417461299021086868483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5522944974199347391245655 8284417461299021086868483)
                  ·
                    refine ⟨12426626191948531630302725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8284417461299021086868483 12426626191948531630302725)
                    ·
                      refine ⟨2329992410990349680681761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12426626191948531630302725 2329992410990349680681761)
                      ·
                        rfl

theorem cell23_4537644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_4537644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537644 prefixEnd_4537644 := by exact prefixLift 4537644
  have htrace : WordTrace (prefixWord ++ tailWord_4537644) baseStart_4537644 baseEnd_4537644 := by
    simpa [prefixWord, tailWord_4537644, baseEnd_4537644] using wordTrace_append hprefix tailTrace_4537644
  have hstable : (prefixWord ++ tailWord_4537644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537644).length < 2 ^ (prefixWord ++ tailWord_4537644).sum := by decide
  have hdescent : baseEnd_4537644 < baseStart_4537644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537671 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 2, 4]
def baseStart_4537671 : Nat := 118140960795 + 4537671 * 2 ^ 59
def prefixEnd_4537671 : Nat := 4983230072969 + 3 ^ 40 * 4537671 * 2
def baseEnd_4537671 : Nat := 776668758322673691681379

theorem tailTrace_4537671 : CollatzResearch.WordTrace tailWord_4537671 prefixEnd_4537671 776668758322673691681379 := by
  unfold tailWord_4537671
  simp only [CollatzResearch.WordTrace]
  refine ⟨165502457943800414353196867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110334971962533609568797911 165502457943800414353196867)
  ·
    refine ⟨248253686915700621529795301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165502457943800414353196867 248253686915700621529795301)
    ·
      refine ⟨46547566296693866536836619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248253686915700621529795301 46547566296693866536836619)
      ·
        refine ⟨69821349445040799805254929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46547566296693866536836619 69821349445040799805254929)
        ·
          refine ⟨52366012083780599853941197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69821349445040799805254929 52366012083780599853941197)
          ·
            refine ⟨19637254531417724945227949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52366012083780599853941197 19637254531417724945227949)
            ·
              refine ⟨7363970449281646854460481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19637254531417724945227949 7363970449281646854460481)
              ·
                refine ⟨5522977836961235140845361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7363970449281646854460481 5522977836961235140845361)
                ·
                  refine ⟨4142233377720926355634021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5522977836961235140845361 4142233377720926355634021)
                  ·
                    refine ⟨776668758322673691681379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142233377720926355634021 776668758322673691681379)
                    ·
                      rfl

theorem cell23_4537671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_4537671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537671 prefixEnd_4537671 := by exact prefixLift 4537671
  have htrace : WordTrace (prefixWord ++ tailWord_4537671) baseStart_4537671 baseEnd_4537671 := by
    simpa [prefixWord, tailWord_4537671, baseEnd_4537671] using wordTrace_append hprefix tailTrace_4537671
  have hstable : (prefixWord ++ tailWord_4537671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537671).length < 2 ^ (prefixWord ++ tailWord_4537671).sum := by decide
  have hdescent : baseEnd_4537671 < baseStart_4537671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537678 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_4537678 : Nat := 118140960795 + 4537678 * 2 ^ 59
def prefixEnd_4537678 : Nat := 4983230072969 + 3 ^ 40 * 4537678 * 2
def baseEnd_4537678 : Nat := 2330009869332602547656605

theorem tailTrace_4537678 : CollatzResearch.WordTrace tailWord_4537678 prefixEnd_4537678 2330009869332602547656605 := by
  unfold tailWord_4537678
  simp only [CollatzResearch.WordTrace]
  refine ⟨20687839156846881818587711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110335142169850036365801125 20687839156846881818587711)
  ·
    refine ⟨31031758735270322727881567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20687839156846881818587711 31031758735270322727881567)
    ·
      refine ⟨46547638102905484091822351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31031758735270322727881567 46547638102905484091822351)
      ·
        refine ⟨69821457154358226137733527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46547638102905484091822351 69821457154358226137733527)
        ·
          refine ⟨104732185731537339206600291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69821457154358226137733527 104732185731537339206600291)
          ·
            refine ⟨157098278597306008809900437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104732185731537339206600291 157098278597306008809900437)
            ·
              refine ⟨7363981809248719162964083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157098278597306008809900437 7363981809248719162964083)
              ·
                refine ⟨11045972713873078744446125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363981809248719162964083 11045972713873078744446125)
                ·
                  refine ⟨4142239767702404529167297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11045972713873078744446125 4142239767702404529167297)
                  ·
                    refine ⟨3106679825776803396875473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142239767702404529167297 3106679825776803396875473)
                    ·
                      refine ⟨2330009869332602547656605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106679825776803396875473 2330009869332602547656605)
                      ·
                        rfl

theorem cell23_4537678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_4537678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537678 prefixEnd_4537678 := by exact prefixLift 4537678
  have htrace : WordTrace (prefixWord ++ tailWord_4537678) baseStart_4537678 baseEnd_4537678 := by
    simpa [prefixWord, tailWord_4537678, baseEnd_4537678] using wordTrace_append hprefix tailTrace_4537678
  have hstable : (prefixWord ++ tailWord_4537678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537678).length < 2 ^ (prefixWord ++ tailWord_4537678).sum := by decide
  have hdescent : baseEnd_4537678 < baseStart_4537678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537697 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_4537697 : Nat := 118140960795 + 4537697 * 2 ^ 59
def prefixEnd_4537697 : Nat := 4983230072969 + 3 ^ 40 * 4537697 * 2
def baseEnd_4537697 : Nat := 776673208488345991106339

theorem tailTrace_4537697 : CollatzResearch.WordTrace tailWord_4537697 prefixEnd_4537697 776673208488345991106339 := by
  unfold tailWord_4537697
  simp only [CollatzResearch.WordTrace]
  refine ⟨165503406241706220793643345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110335604161137480529095563 165503406241706220793643345)
  ·
    refine ⟨124127554681279665595232509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165503406241706220793643345 124127554681279665595232509)
    ·
      refine ⟨46547833005479874598212191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124127554681279665595232509 46547833005479874598212191)
      ·
        refine ⟨69821749508219811897318287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46547833005479874598212191 69821749508219811897318287)
        ·
          refine ⟨104732624262329717845977431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69821749508219811897318287 104732624262329717845977431)
          ·
            refine ⟨157098936393494576768966147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104732624262329717845977431 157098936393494576768966147)
            ·
              refine ⟨235648404590241865153449221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157098936393494576768966147 235648404590241865153449221)
              ·
                refine ⟨44184075860670349716271729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235648404590241865153449221 44184075860670349716271729)
                ·
                  refine ⟨33138056895502762287203797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44184075860670349716271729 33138056895502762287203797)
                  ·
                    refine ⟨776673208488345991106339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33138056895502762287203797 776673208488345991106339)
                    ·
                      rfl

theorem cell23_4537697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_4537697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537697 prefixEnd_4537697 := by exact prefixLift 4537697
  have htrace : WordTrace (prefixWord ++ tailWord_4537697) baseStart_4537697 baseEnd_4537697 := by
    simpa [prefixWord, tailWord_4537697, baseEnd_4537697] using wordTrace_append hprefix tailTrace_4537697
  have hstable : (prefixWord ++ tailWord_4537697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537697).length < 2 ^ (prefixWord ++ tailWord_4537697).sum := by decide
  have hdescent : baseEnd_4537697 < baseStart_4537697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537698 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4537698 : Nat := 118140960795 + 4537698 * 2 ^ 59
def prefixEnd_4537698 : Nat := 4983230072969 + 3 ^ 40 * 4537698 * 2
def baseEnd_4537698 : Nat := 2330020138945692469406513

theorem tailTrace_4537698 : CollatzResearch.WordTrace tailWord_4537698 prefixEnd_4537698 2330020138945692469406513 := by
  unfold tailWord_4537698
  simp only [CollatzResearch.WordTrace]
  refine ⟨41375860678675649491107437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110335628476468398642953165 41375860678675649491107437)
  ·
    refine ⟨15515947754503368559165289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41375860678675649491107437 15515947754503368559165289)
    ·
      refine ⟨11636960815877526419373967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15515947754503368559165289 11636960815877526419373967)
      ·
        refine ⟨17455441223816289629060951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11636960815877526419373967 17455441223816289629060951)
        ·
          refine ⟨26183161835724434443591427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17455441223816289629060951 26183161835724434443591427)
          ·
            refine ⟨39274742753586651665387141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26183161835724434443591427 39274742753586651665387141)
            ·
              refine ⟨7364014266297497187260089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39274742753586651665387141 7364014266297497187260089)
              ·
                refine ⟨5523010699723122890445067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7364014266297497187260089 5523010699723122890445067)
                ·
                  refine ⟨8284516049584684335667601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523010699723122890445067 8284516049584684335667601)
                  ·
                    refine ⟨6213387037188513251750701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8284516049584684335667601 6213387037188513251750701)
                    ·
                      refine ⟨2330020138945692469406513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6213387037188513251750701 2330020138945692469406513)
                      ·
                        rfl

theorem cell23_4537698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4537698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537698 prefixEnd_4537698 := by exact prefixLift 4537698
  have htrace : WordTrace (prefixWord ++ tailWord_4537698) baseStart_4537698 baseEnd_4537698 := by
    simpa [prefixWord, tailWord_4537698, baseEnd_4537698] using wordTrace_append hprefix tailTrace_4537698
  have hstable : (prefixWord ++ tailWord_4537698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537698).length < 2 ^ (prefixWord ++ tailWord_4537698).sum := by decide
  have hdescent : baseEnd_4537698 < baseStart_4537698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537729 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_4537729 : Nat := 118140960795 + 4537729 * 2 ^ 59
def prefixEnd_4537729 : Nat := 4983230072969 + 3 ^ 40 * 4537729 * 2
def baseEnd_4537729 : Nat := 2330036056845981848118871

theorem tailTrace_4537729 : CollatzResearch.WordTrace tailWord_4537729 prefixEnd_4537729 2330036056845981848118871 := by
  unfold tailWord_4537729
  simp only [CollatzResearch.WordTrace]
  refine ⟨165504573377590290258808241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110336382251726860172538827 165504573377590290258808241)
  ·
    refine ⟨124128430033192717694106181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165504573377590290258808241 124128430033192717694106181)
    ·
      refine ⟨23274080631223634567644909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124128430033192717694106181 23274080631223634567644909)
      ·
        refine ⟨8727780236708862962866841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23274080631223634567644909 8727780236708862962866841)
        ·
          refine ⟨6545835177531647222150131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8727780236708862962866841 6545835177531647222150131)
          ·
            refine ⟨9818752766297470833225197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545835177531647222150131 9818752766297470833225197)
            ·
              refine ⟨3682032287361551562459449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9818752766297470833225197 3682032287361551562459449)
              ·
                refine ⟨2761524215521163671844587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3682032287361551562459449 2761524215521163671844587)
                ·
                  refine ⟨4142286323281745507766881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761524215521163671844587 4142286323281745507766881)
                  ·
                    refine ⟨3106714742461309130825161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142286323281745507766881 3106714742461309130825161)
                    ·
                      refine ⟨2330036056845981848118871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106714742461309130825161 2330036056845981848118871)
                      ·
                        rfl

theorem cell23_4537729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_4537729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537729 prefixEnd_4537729 := by exact prefixLift 4537729
  have htrace : WordTrace (prefixWord ++ tailWord_4537729) baseStart_4537729 baseEnd_4537729 := by
    simpa [prefixWord, tailWord_4537729, baseEnd_4537729] using wordTrace_append hprefix tailTrace_4537729
  have hstable : (prefixWord ++ tailWord_4537729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537729).length < 2 ^ (prefixWord ++ tailWord_4537729).sum := by decide
  have hdescent : baseEnd_4537729 < baseStart_4537729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537747 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_4537747 : Nat := 118140960795 + 4537747 * 2 ^ 59
def prefixEnd_4537747 : Nat := 4983230072969 + 3 ^ 40 * 4537747 * 2
def baseEnd_4537747 : Nat := 2330045299497762777693787

theorem tailTrace_4537747 : CollatzResearch.WordTrace tailWord_4537747 prefixEnd_4537747 2330045299497762777693787 := by
  unfold tailWord_4537747
  simp only [CollatzResearch.WordTrace]
  refine ⟨165505229891525079332963495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110336819927683386221975663 165505229891525079332963495)
  ·
    refine ⟨248257844837287618999445243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165505229891525079332963495 248257844837287618999445243)
    ·
      refine ⟨372386767255931428499167865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248257844837287618999445243 372386767255931428499167865)
      ·
        refine ⟨279290075441948571374375899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372386767255931428499167865 279290075441948571374375899)
        ·
          refine ⟨418935113162922857061563849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279290075441948571374375899 418935113162922857061563849)
          ·
            refine ⟨314201334872192142796172887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418935113162922857061563849 314201334872192142796172887)
            ·
              refine ⟨471302002308288214194259331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314201334872192142796172887 471302002308288214194259331)
              ·
                refine ⟨706953003462432321291388997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471302002308288214194259331 706953003462432321291388997)
                ·
                  refine ⟨132553688149206060242135437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706953003462432321291388997 132553688149206060242135437)
                  ·
                    refine ⟨49707633055952272590800789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132553688149206060242135437 49707633055952272590800789)
                    ·
                      refine ⟨2330045299497762777693787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49707633055952272590800789 2330045299497762777693787)
                      ·
                        rfl

theorem cell23_4537747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_4537747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537747 prefixEnd_4537747 := by exact prefixLift 4537747
  have htrace : WordTrace (prefixWord ++ tailWord_4537747) baseStart_4537747 baseEnd_4537747 := by
    simpa [prefixWord, tailWord_4537747, baseEnd_4537747] using wordTrace_append hprefix tailTrace_4537747
  have hstable : (prefixWord ++ tailWord_4537747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537747).length < 2 ^ (prefixWord ++ tailWord_4537747).sum := by decide
  have hdescent : baseEnd_4537747 < baseStart_4537747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537751 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_4537751 : Nat := 118140960795 + 4537751 * 2 ^ 59
def prefixEnd_4537751 : Nat := 4983230072969 + 3 ^ 40 * 4537751 * 2
def baseEnd_4537751 : Nat := 2330047353420380762043769

theorem tailTrace_4537751 : CollatzResearch.WordTrace tailWord_4537751 prefixEnd_4537751 2330047353420380762043769 := by
  unfold tailWord_4537751
  simp only [CollatzResearch.WordTrace]
  refine ⟨165505375783510588016109107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110336917189007058677406071 165505375783510588016109107)
  ·
    refine ⟨248258063675265882024163661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165505375783510588016109107 248258063675265882024163661)
    ·
      refine ⟨93096773878224705759061373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248258063675265882024163661 93096773878224705759061373)
      ·
        refine ⟨34911290204334264659648015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93096773878224705759061373 34911290204334264659648015)
        ·
          refine ⟨52366935306501396989472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34911290204334264659648015 52366935306501396989472023)
          ·
            refine ⟨78550402959752095484208035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52366935306501396989472023 78550402959752095484208035)
            ·
              refine ⟨117825604439628143226312053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78550402959752095484208035 117825604439628143226312053)
              ·
                refine ⟨11046150416215138427466755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117825604439628143226312053 11046150416215138427466755)
                ·
                  refine ⟨16569225624322707641200133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11046150416215138427466755 16569225624322707641200133)
                  ·
                    refine ⟨3106729804560507682725025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16569225624322707641200133 3106729804560507682725025)
                    ·
                      refine ⟨2330047353420380762043769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106729804560507682725025 2330047353420380762043769)
                      ·
                        rfl

theorem cell23_4537751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_4537751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537751 prefixEnd_4537751 := by exact prefixLift 4537751
  have htrace : WordTrace (prefixWord ++ tailWord_4537751) baseStart_4537751 baseEnd_4537751 := by
    simpa [prefixWord, tailWord_4537751, baseEnd_4537751] using wordTrace_append hprefix tailTrace_4537751
  have hstable : (prefixWord ++ tailWord_4537751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537751).length < 2 ^ (prefixWord ++ tailWord_4537751).sum := by decide
  have hdescent : baseEnd_4537751 < baseStart_4537751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537754 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4537754 : Nat := 118140960795 + 4537754 * 2 ^ 59
def prefixEnd_4537754 : Nat := 4983230072969 + 3 ^ 40 * 4537754 * 2
def baseEnd_4537754 : Nat := 2330048893862344250306255

theorem tailTrace_4537754 : CollatzResearch.WordTrace tailWord_4537754 prefixEnd_4537754 2330048893862344250306255 := by
  unfold tailWord_4537754
  simp only [CollatzResearch.WordTrace]
  refine ⟨41376371300624929882117079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110336990134999813018978877 41376371300624929882117079)
  ·
    refine ⟨62064556950937394823175619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41376371300624929882117079 62064556950937394823175619)
    ·
      refine ⟨93096835426406092234763429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62064556950937394823175619 93096835426406092234763429)
      ·
        refine ⟨17455656642451142294018143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93096835426406092234763429 17455656642451142294018143)
        ·
          refine ⟨26183484963676713441027215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17455656642451142294018143 26183484963676713441027215)
          ·
            refine ⟨39275227445515070161540823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26183484963676713441027215 39275227445515070161540823)
            ·
              refine ⟨58912841168272605242311235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39275227445515070161540823 58912841168272605242311235)
              ·
                refine ⟨88369261752408907863466853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58912841168272605242311235 88369261752408907863466853)
                ·
                  refine ⟨16569236578576670224400035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88369261752408907863466853 16569236578576670224400035)
                  ·
                    refine ⟨24853854867865005336600053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16569236578576670224400035 24853854867865005336600053)
                    ·
                      refine ⟨2330048893862344250306255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24853854867865005336600053 2330048893862344250306255)
                      ·
                        rfl

theorem cell23_4537754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4537754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537754 prefixEnd_4537754 := by exact prefixLift 4537754
  have htrace : WordTrace (prefixWord ++ tailWord_4537754) baseStart_4537754 baseEnd_4537754 := by
    simpa [prefixWord, tailWord_4537754, baseEnd_4537754] using wordTrace_append hprefix tailTrace_4537754
  have hstable : (prefixWord ++ tailWord_4537754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537754).length < 2 ^ (prefixWord ++ tailWord_4537754).sum := by decide
  have hdescent : baseEnd_4537754 < baseStart_4537754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537764 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_4537764 : Nat := 118140960795 + 4537764 * 2 ^ 59
def prefixEnd_4537764 : Nat := 4983230072969 + 3 ^ 40 * 4537764 * 2
def baseEnd_4537764 : Nat := 2330054028668889211181209

theorem tailTrace_4537764 : CollatzResearch.WordTrace tailWord_4537764 prefixEnd_4537764 2330054028668889211181209 := by
  unfold tailWord_4537764
  simp only [CollatzResearch.WordTrace]
  refine ⟨82752924966231745618166173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110337233288308994157554897 82752924966231745618166173)
  ·
    refine ⟨31032346862336904606812315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82752924966231745618166173 31032346862336904606812315)
    ·
      refine ⟨46548520293505356910218473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31032346862336904606812315 46548520293505356910218473)
      ·
        refine ⟨34911390220129017682663855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46548520293505356910218473 34911390220129017682663855)
        ·
          refine ⟨52367085330193526523995783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34911390220129017682663855 52367085330193526523995783)
          ·
            refine ⟨78550627995290289785993675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52367085330193526523995783 78550627995290289785993675)
            ·
              refine ⟨117825941992935434678990513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78550627995290289785993675 117825941992935434678990513)
              ·
                refine ⟨88369456494701576009242885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117825941992935434678990513 88369456494701576009242885)
                ·
                  refine ⟨16569273092756545501733041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88369456494701576009242885 16569273092756545501733041)
                  ·
                    refine ⟨12426954819567409126299781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16569273092756545501733041 12426954819567409126299781)
                    ·
                      refine ⟨2330054028668889211181209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12426954819567409126299781 2330054028668889211181209)
                      ·
                        rfl

theorem cell23_4537764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_4537764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537764 prefixEnd_4537764 := by exact prefixLift 4537764
  have htrace : WordTrace (prefixWord ++ tailWord_4537764) baseStart_4537764 baseEnd_4537764 := by
    simpa [prefixWord, tailWord_4537764, baseEnd_4537764] using wordTrace_append hprefix tailTrace_4537764
  have hstable : (prefixWord ++ tailWord_4537764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537764).length < 2 ^ (prefixWord ++ tailWord_4537764).sum := by decide
  have hdescent : baseEnd_4537764 < baseStart_4537764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537821 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4537821 : Nat := 118140960795 + 4537821 * 2 ^ 59
def prefixEnd_4537821 : Nat := 4983230072969 + 3 ^ 40 * 4537821 * 2
def baseEnd_4537821 : Nat := 776694432355398496056149

theorem tailTrace_4537821 : CollatzResearch.WordTrace tailWord_4537821 prefixEnd_4537821 776694432355398496056149 := by
  unfold tailWord_4537821
  simp only [CollatzResearch.WordTrace]
  refine ⟨165507928893256989971157317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110338619262171326647438211 165507928893256989971157317)
  ·
    refine ⟨31032736667485685619591997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165507928893256989971157317 31032736667485685619591997)
    ·
      refine ⟨11637276250307132107346999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31032736667485685619591997 11637276250307132107346999)
      ·
        refine ⟨17455914375460698161020499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637276250307132107346999 17455914375460698161020499)
        ·
          refine ⟨26183871563191047241530749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17455914375460698161020499 26183871563191047241530749)
          ·
            refine ⟨9818951836196642715574031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26183871563191047241530749 9818951836196642715574031)
            ·
              refine ⟨14728427754294964073361047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9818951836196642715574031 14728427754294964073361047)
              ·
                refine ⟨22092641631442446110041571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14728427754294964073361047 22092641631442446110041571)
                ·
                  refine ⟨33138962447163669165062357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22092641631442446110041571 33138962447163669165062357)
                  ·
                    refine ⟨776694432355398496056149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33138962447163669165062357 776694432355398496056149)
                    ·
                      rfl

theorem cell23_4537821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4537821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537821 prefixEnd_4537821 := by exact prefixLift 4537821
  have htrace : WordTrace (prefixWord ++ tailWord_4537821) baseStart_4537821 baseEnd_4537821 := by
    simpa [prefixWord, tailWord_4537821, baseEnd_4537821] using wordTrace_append hprefix tailTrace_4537821
  have hstable : (prefixWord ++ tailWord_4537821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537821).length < 2 ^ (prefixWord ++ tailWord_4537821).sum := by decide
  have hdescent : baseEnd_4537821 < baseStart_4537821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537858 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4537858 : Nat := 118140960795 + 4537858 * 2 ^ 59
def prefixEnd_4537858 : Nat := 4983230072969 + 3 ^ 40 * 4537858 * 2
def baseEnd_4537858 : Nat := 2330102295850411843405777

theorem tailTrace_4537858 : CollatzResearch.WordTrace tailWord_4537858 prefixEnd_4537858 2330102295850411843405777 := by
  unfold tailWord_4537858
  simp only [CollatzResearch.WordTrace]
  refine ⟨41377319598530736322563557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110339518929415296860169485 41377319598530736322563557)
  ·
    refine ⟨7758247424724513060480667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41377319598530736322563557 7758247424724513060480667)
    ·
      refine ⟨11637371137086769590721001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758247424724513060480667 11637371137086769590721001)
      ·
        refine ⟨8728028352815077193040751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11637371137086769590721001 8728028352815077193040751)
        ·
          refine ⟨13092042529222615789561127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8728028352815077193040751 13092042529222615789561127)
          ·
            refine ⟨19638063793833923684341691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13092042529222615789561127 19638063793833923684341691)
            ·
              refine ⟨29457095690750885526512537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19638063793833923684341691 29457095690750885526512537)
              ·
                refine ⟨22092821768063164144884403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29457095690750885526512537 22092821768063164144884403)
                ·
                  refine ⟨33139232652094746217326605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22092821768063164144884403 33139232652094746217326605)
                  ·
                    refine ⟨12427212244535529831497477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33139232652094746217326605 12427212244535529831497477)
                    ·
                      refine ⟨2330102295850411843405777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12427212244535529831497477 2330102295850411843405777)
                      ·
                        rfl

theorem cell23_4537858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4537858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537858 prefixEnd_4537858 := by exact prefixLift 4537858
  have htrace : WordTrace (prefixWord ++ tailWord_4537858) baseStart_4537858 baseEnd_4537858 := by
    simpa [prefixWord, tailWord_4537858, baseEnd_4537858] using wordTrace_append hprefix tailTrace_4537858
  have hstable : (prefixWord ++ tailWord_4537858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537858).length < 2 ^ (prefixWord ++ tailWord_4537858).sum := by decide
  have hdescent : baseEnd_4537858 < baseStart_4537858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537904 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_4537904 : Nat := 118140960795 + 4537904 * 2 ^ 59
def prefixEnd_4537904 : Nat := 4983230072969 + 3 ^ 40 * 4537904 * 2
def baseEnd_4537904 : Nat := 2330125915960518663430565

theorem tailTrace_4537904 : CollatzResearch.WordTrace tailWord_4537904 prefixEnd_4537904 2330125915960518663430565 := by
  unfold tailWord_4537904
  simp only [CollatzResearch.WordTrace]
  refine ⟨82755478075978147573214383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110340637434637530097619177 82755478075978147573214383)
  ·
    refine ⟨124133217113967221359821575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82755478075978147573214383 124133217113967221359821575)
    ·
      refine ⟨186199825670950832039732363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124133217113967221359821575 186199825670950832039732363)
      ·
        refine ⟨279299738506426248059598545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186199825670950832039732363 279299738506426248059598545)
        ·
          refine ⟨209474803879819686044698909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279299738506426248059598545 209474803879819686044698909)
          ·
            refine ⟨78553051454932382266762091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209474803879819686044698909 78553051454932382266762091)
            ·
              refine ⟨117829577182398573400143137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78553051454932382266762091 117829577182398573400143137)
              ·
                refine ⟨88372182886798930050107353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117829577182398573400143137 88372182886798930050107353)
                ·
                  refine ⟨66279137165099197537580515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88372182886798930050107353 66279137165099197537580515)
                  ·
                    refine ⟨99418705747648796306370773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66279137165099197537580515 99418705747648796306370773)
                    ·
                      refine ⟨2330125915960518663430565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99418705747648796306370773 2330125915960518663430565)
                      ·
                        rfl

theorem cell23_4537904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_4537904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537904 prefixEnd_4537904 := by exact prefixLift 4537904
  have htrace : WordTrace (prefixWord ++ tailWord_4537904) baseStart_4537904 baseEnd_4537904 := by
    simpa [prefixWord, tailWord_4537904, baseEnd_4537904] using wordTrace_append hprefix tailTrace_4537904
  have hstable : (prefixWord ++ tailWord_4537904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537904).length < 2 ^ (prefixWord ++ tailWord_4537904).sum := by decide
  have hdescent : baseEnd_4537904 < baseStart_4537904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4537968 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_4537968 : Nat := 118140960795 + 4537968 * 2 ^ 59
def prefixEnd_4537968 : Nat := 4983230072969 + 3 ^ 40 * 4537968 * 2
def baseEnd_4537968 : Nat := 2330158778722406413030271

theorem tailTrace_4537968 : CollatzResearch.WordTrace tailWord_4537968 prefixEnd_4537968 2330158778722406413030271 := by
  unfold tailWord_4537968
  simp only [CollatzResearch.WordTrace]
  refine ⟨82756645211862217038379279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110342193615816289384505705 82756645211862217038379279)
  ·
    refine ⟨124134967817793325557568919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82756645211862217038379279 124134967817793325557568919)
    ·
      refine ⟨186202451726689988336353379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124134967817793325557568919 186202451726689988336353379)
      ·
        refine ⟨279303677590034982504530069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186202451726689988336353379 279303677590034982504530069)
        ·
          refine ⟨13092359887032889804899847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 279303677590034982504530069 13092359887032889804899847)
          ·
            refine ⟨19638539830549334707349771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13092359887032889804899847 19638539830549334707349771)
            ·
              refine ⟨29457809745824002061024657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19638539830549334707349771 29457809745824002061024657)
              ·
                refine ⟨22093357309368001545768493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29457809745824002061024657 22093357309368001545768493)
                ·
                  refine ⟨8285008991013000579663185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22093357309368001545768493 8285008991013000579663185)
                  ·
                    refine ⟨6213756743259750434747389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8285008991013000579663185 6213756743259750434747389)
                    ·
                      refine ⟨2330158778722406413030271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6213756743259750434747389 2330158778722406413030271)
                      ·
                        rfl

theorem cell23_4537968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_4537968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4537968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4537968 prefixEnd_4537968 := by exact prefixLift 4537968
  have htrace : WordTrace (prefixWord ++ tailWord_4537968) baseStart_4537968 baseEnd_4537968 := by
    simpa [prefixWord, tailWord_4537968, baseEnd_4537968] using wordTrace_append hprefix tailTrace_4537968
  have hstable : (prefixWord ++ tailWord_4537968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4537968).length < 2 ^ (prefixWord ++ tailWord_4537968).sum := by decide
  have hdescent : baseEnd_4537968 < baseStart_4537968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4537968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538002 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4538002 : Nat := 118140960795 + 4538002 * 2 ^ 59
def prefixEnd_4538002 : Nat := 4983230072969 + 3 ^ 40 * 4538002 * 2
def baseEnd_4538002 : Nat := 2330176237064659280005115

theorem tailTrace_4538002 : CollatzResearch.WordTrace tailWord_4538002 prefixEnd_4538002 2330176237064659280005115 := by
  unfold tailWord_4538002
  simp only [CollatzResearch.WordTrace]
  refine ⟨41378632626400314470874065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110343020337067505255664173 41378632626400314470874065)
  ·
    refine ⟨31033974469800235853155549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41378632626400314470874065 31033974469800235853155549)
    ·
      refine ⟨11637740426175088444933331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31033974469800235853155549 11637740426175088444933331)
      ·
        refine ⟨17456610639262632667399997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637740426175088444933331 17456610639262632667399997)
        ·
          refine ⟨6546228989723487250274999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17456610639262632667399997 6546228989723487250274999)
          ·
            refine ⟨9819343484585230875412499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6546228989723487250274999 9819343484585230875412499)
            ·
              refine ⟨14729015226877846313118749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9819343484585230875412499 14729015226877846313118749)
              ·
                refine ⟨5523380710079192367419531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14729015226877846313118749 5523380710079192367419531)
                ·
                  refine ⟨8285071065118788551129297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523380710079192367419531 8285071065118788551129297)
                  ·
                    refine ⟨6213803298839091413346973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8285071065118788551129297 6213803298839091413346973)
                    ·
                      refine ⟨2330176237064659280005115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6213803298839091413346973 2330176237064659280005115)
                      ·
                        rfl

theorem cell23_4538002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4538002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538002 prefixEnd_4538002 := by exact prefixLift 4538002
  have htrace : WordTrace (prefixWord ++ tailWord_4538002) baseStart_4538002 baseEnd_4538002 := by
    simpa [prefixWord, tailWord_4538002, baseEnd_4538002] using wordTrace_append hprefix tailTrace_4538002
  have hstable : (prefixWord ++ tailWord_4538002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538002).length < 2 ^ (prefixWord ++ tailWord_4538002).sum := by decide
  have hdescent : baseEnd_4538002 < baseStart_4538002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538021 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_4538021 : Nat := 118140960795 + 4538021 * 2 ^ 59
def prefixEnd_4538021 : Nat := 4983230072969 + 3 ^ 40 * 4538021 * 2
def baseEnd_4538021 : Nat := 2330185993197094705667527

theorem tailTrace_4538021 : CollatzResearch.WordTrace tailWord_4538021 prefixEnd_4538021 2330185993197094705667527 := by
  unfold tailWord_4538021
  simp only [CollatzResearch.WordTrace]
  refine ⟨165515223492532424128437917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110343482328354949418958611 165515223492532424128437917)
  ·
    refine ⟨62068208809699659048164219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165515223492532424128437917 62068208809699659048164219)
    ·
      refine ⟨93102313214549488572246329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62068208809699659048164219 93102313214549488572246329)
      ·
        refine ⟨69826734910912116429184747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93102313214549488572246329 69826734910912116429184747)
        ·
          refine ⟨104740102366368174643777121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69826734910912116429184747 104740102366368174643777121)
          ·
            refine ⟨78555076774776130982832841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104740102366368174643777121 78555076774776130982832841)
            ·
              refine ⟨58916307581082098237124631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78555076774776130982832841 58916307581082098237124631)
              ·
                refine ⟨88374461371623147355686947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58916307581082098237124631 88374461371623147355686947)
                ·
                  refine ⟨132561692057434721033530421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88374461371623147355686947 132561692057434721033530421)
                  ·
                    refine ⟨12427658630384505096893477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132561692057434721033530421 12427658630384505096893477)
                    ·
                      refine ⟨2330185993197094705667527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12427658630384505096893477 2330185993197094705667527)
                      ·
                        rfl

theorem cell23_4538021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_4538021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538021 prefixEnd_4538021 := by exact prefixLift 4538021
  have htrace : WordTrace (prefixWord ++ tailWord_4538021) baseStart_4538021 baseEnd_4538021 := by
    simpa [prefixWord, tailWord_4538021, baseEnd_4538021] using wordTrace_append hprefix tailTrace_4538021
  have hstable : (prefixWord ++ tailWord_4538021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538021).length < 2 ^ (prefixWord ++ tailWord_4538021).sum := by decide
  have hdescent : baseEnd_4538021 < baseStart_4538021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538031 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 2, 6]
def baseStart_4538031 : Nat := 118140960795 + 4538031 * 2 ^ 59
def prefixEnd_4538031 : Nat := 4983230072969 + 3 ^ 40 * 4538031 * 2
def baseEnd_4538031 : Nat := 776730376001213222180827

theorem tailTrace_4538031 : CollatzResearch.WordTrace tailWord_4538031 prefixEnd_4538031 776730376001213222180827 := by
  unfold tailWord_4538031
  simp only [CollatzResearch.WordTrace]
  refine ⟨165515588222496195836301947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110343725481664130557534631 165515588222496195836301947)
  ·
    refine ⟨248273382333744293754452921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165515588222496195836301947 248273382333744293754452921)
    ·
      refine ⟨186205036750308220315839691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248273382333744293754452921 186205036750308220315839691)
      ·
        refine ⟨279307555125462330473759537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186205036750308220315839691 279307555125462330473759537)
        ·
          refine ⟨209480666344096747855319653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279307555125462330473759537 209480666344096747855319653)
          ·
            refine ⟨39277624939518140222872435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209480666344096747855319653 39277624939518140222872435)
            ·
              refine ⟨58916437409277210334308653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39277624939518140222872435 58916437409277210334308653)
              ·
                refine ⟨22093664028478953875365745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58916437409277210334308653 22093664028478953875365745)
                ·
                  refine ⟨16570248021359215406524309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22093664028478953875365745 16570248021359215406524309)
                  ·
                    refine ⟨776730376001213222180827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16570248021359215406524309 776730376001213222180827)
                    ·
                      rfl

theorem cell23_4538031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_4538031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538031 prefixEnd_4538031 := by exact prefixLift 4538031
  have htrace : WordTrace (prefixWord ++ tailWord_4538031) baseStart_4538031 baseEnd_4538031 := by
    simpa [prefixWord, tailWord_4538031, baseEnd_4538031] using wordTrace_append hprefix tailTrace_4538031
  have hstable : (prefixWord ++ tailWord_4538031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538031).length < 2 ^ (prefixWord ++ tailWord_4538031).sum := by decide
  have hdescent : baseEnd_4538031 < baseStart_4538031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538042 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_4538042 : Nat := 118140960795 + 4538042 * 2 ^ 59
def prefixEnd_4538042 : Nat := 4983230072969 + 3 ^ 40 * 4538042 * 2
def baseEnd_4538042 : Nat := 2330196776290839123504931

theorem tailTrace_4538042 : CollatzResearch.WordTrace tailWord_4538042 prefixEnd_4538042 2330196776290839123504931 := by
  unfold tailWord_4538042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41378997356364086178738095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110343992950304229809968253 41378997356364086178738095)
  ·
    refine ⟨62068496034546129268107143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41378997356364086178738095 62068496034546129268107143)
    ·
      refine ⟨93102744051819193902160715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62068496034546129268107143 93102744051819193902160715)
      ·
        refine ⟨139654116077728790853241073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93102744051819193902160715 139654116077728790853241073)
        ·
          refine ⟨104740587058296593139930805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139654116077728790853241073 104740587058296593139930805)
          ·
            refine ⟨9819430036715305606868513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104740587058296593139930805 9819430036715305606868513)
            ·
              refine ⟨7364572527536479205151385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9819430036715305606868513 7364572527536479205151385)
              ·
                refine ⟨5523429395652359403863539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7364572527536479205151385 5523429395652359403863539)
                ·
                  refine ⟨8285144093478539105795309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523429395652359403863539 8285144093478539105795309)
                  ·
                    refine ⟨3106929035054452164673241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8285144093478539105795309 3106929035054452164673241)
                    ·
                      refine ⟨2330196776290839123504931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106929035054452164673241 2330196776290839123504931)
                      ·
                        rfl

theorem cell23_4538042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_4538042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538042 prefixEnd_4538042 := by exact prefixLift 4538042
  have htrace : WordTrace (prefixWord ++ tailWord_4538042) baseStart_4538042 baseEnd_4538042 := by
    simpa [prefixWord, tailWord_4538042, baseEnd_4538042] using wordTrace_append hprefix tailTrace_4538042
  have hstable : (prefixWord ++ tailWord_4538042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538042).length < 2 ^ (prefixWord ++ tailWord_4538042).sum := by decide
  have hdescent : baseEnd_4538042 < baseStart_4538042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538055 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_4538055 : Nat := 118140960795 + 4538055 * 2 ^ 59
def prefixEnd_4538055 : Nat := 4983230072969 + 3 ^ 40 * 4538055 * 2
def baseEnd_4538055 : Nat := 2330203451539347572642371

theorem tailTrace_4538055 : CollatzResearch.WordTrace tailWord_4538055 prefixEnd_4538055 2330203451539347572642371 := by
  unfold tailWord_4538055
  simp only [CollatzResearch.WordTrace]
  refine ⟨165516463574409247935175619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110344309049606165290117079 165516463574409247935175619)
  ·
    refine ⟨248274695361613871902763429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165516463574409247935175619 248274695361613871902763429)
    ·
      refine ⟨46551505380302600981768143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248274695361613871902763429 46551505380302600981768143)
      ·
        refine ⟨69827258070453901472652215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46551505380302600981768143 69827258070453901472652215)
        ·
          refine ⟨104740887105680852208978323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69827258070453901472652215 104740887105680852208978323)
          ·
            refine ⟨157111330658521278313467485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104740887105680852208978323 157111330658521278313467485)
            ·
              refine ⟨58916748996945479367550307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157111330658521278313467485 58916748996945479367550307)
              ·
                refine ⟨88375123495418219051325461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58916748996945479367550307 88375123495418219051325461)
                ·
                  refine ⟨4142583913847729018030881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88375123495418219051325461 4142583913847729018030881)
                  ·
                    refine ⟨3106937935385796763523161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142583913847729018030881 3106937935385796763523161)
                    ·
                      refine ⟨2330203451539347572642371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106937935385796763523161 2330203451539347572642371)
                      ·
                        rfl

theorem cell23_4538055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_4538055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538055 prefixEnd_4538055 := by exact prefixLift 4538055
  have htrace : WordTrace (prefixWord ++ tailWord_4538055) baseStart_4538055 baseEnd_4538055 := by
    simpa [prefixWord, tailWord_4538055, baseEnd_4538055] using wordTrace_append hprefix tailTrace_4538055
  have hstable : (prefixWord ++ tailWord_4538055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538055).length < 2 ^ (prefixWord ++ tailWord_4538055).sum := by decide
  have hdescent : baseEnd_4538055 < baseStart_4538055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538071 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_4538071 : Nat := 118140960795 + 4538071 * 2 ^ 59
def prefixEnd_4538071 : Nat := 4983230072969 + 3 ^ 40 * 4538071 * 2
def baseEnd_4538071 : Nat := 2330211667229819510042297

theorem tailTrace_4538071 : CollatzResearch.WordTrace tailWord_4538071 prefixEnd_4538071 2330211667229819510042297 := by
  unfold tailWord_4538071
  simp only [CollatzResearch.WordTrace]
  refine ⟨165517047142351282667758067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110344698094900855111838711 165517047142351282667758067)
  ·
    refine ⟨248275570713526924001637101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165517047142351282667758067 248275570713526924001637101)
    ·
      refine ⟨93103339017572596500613913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248275570713526924001637101 93103339017572596500613913)
      ·
        refine ⟨69827504263179447375460435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93103339017572596500613913 69827504263179447375460435)
        ·
          refine ⟨104741256394769171063190653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69827504263179447375460435 104741256394769171063190653)
          ·
            refine ⟨39277971148038439148696495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104741256394769171063190653 39277971148038439148696495)
            ·
              refine ⟨58916956722057658723044743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39277971148038439148696495 58916956722057658723044743)
              ·
                refine ⟨88375435083086488084567115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58916956722057658723044743 88375435083086488084567115)
                ·
                  refine ⟨132563152624629732126850673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88375435083086488084567115 132563152624629732126850673)
                  ·
                    refine ⟨99422364468472299095138005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 132563152624629732126850673 99422364468472299095138005)
                    ·
                      refine ⟨2330211667229819510042297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99422364468472299095138005 2330211667229819510042297)
                      ·
                        rfl

theorem cell23_4538071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_4538071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538071 prefixEnd_4538071 := by exact prefixLift 4538071
  have htrace : WordTrace (prefixWord ++ tailWord_4538071) baseStart_4538071 baseEnd_4538071 := by
    simpa [prefixWord, tailWord_4538071, baseEnd_4538071] using wordTrace_append hprefix tailTrace_4538071
  have hstable : (prefixWord ++ tailWord_4538071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538071).length < 2 ^ (prefixWord ++ tailWord_4538071).sum := by decide
  have hdescent : baseEnd_4538071 < baseStart_4538071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538072 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_4538072 : Nat := 118140960795 + 4538072 * 2 ^ 59
def prefixEnd_4538072 : Nat := 4983230072969 + 3 ^ 40 * 4538072 * 2
def baseEnd_4538072 : Nat := 2330212180710474006129793

theorem tailTrace_4538072 : CollatzResearch.WordTrace tailWord_4538072 prefixEnd_4538072 2330212180710474006129793 := by
  unfold tailWord_4538072
  simp only [CollatzResearch.WordTrace]
  refine ⟨82758541807673829919272235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110344722410231773225696313 82758541807673829919272235)
  ·
    refine ⟨124137812711510744878908353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82758541807673829919272235 124137812711510744878908353)
    ·
      refine ⟨93103359533633058659181265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124137812711510744878908353 93103359533633058659181265)
      ·
        refine ⟨69827519650224793994385949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93103359533633058659181265 69827519650224793994385949)
        ·
          refine ⟨26185319868834297747894731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69827519650224793994385949 26185319868834297747894731)
          ·
            refine ⟨39277979803251446621842097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26185319868834297747894731 39277979803251446621842097)
            ·
              refine ⟨29458484852438584966381573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39277979803251446621842097 29458484852438584966381573)
              ·
                refine ⟨5523465909832234681196545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29458484852438584966381573 5523465909832234681196545)
                ·
                  refine ⟨4142599432374176010897409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5523465909832234681196545 4142599432374176010897409)
                  ·
                    refine ⟨3106949574280632008173057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142599432374176010897409 3106949574280632008173057)
                    ·
                      refine ⟨2330212180710474006129793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106949574280632008173057 2330212180710474006129793)
                      ·
                        rfl

theorem cell23_4538072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_4538072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538072 prefixEnd_4538072 := by exact prefixLift 4538072
  have htrace : WordTrace (prefixWord ++ tailWord_4538072) baseStart_4538072 baseEnd_4538072 := by
    simpa [prefixWord, tailWord_4538072, baseEnd_4538072] using wordTrace_append hprefix tailTrace_4538072
  have hstable : (prefixWord ++ tailWord_4538072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538072).length < 2 ^ (prefixWord ++ tailWord_4538072).sum := by decide
  have hdescent : baseEnd_4538072 < baseStart_4538072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538091 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 7]
def baseStart_4538091 : Nat := 118140960795 + 4538091 * 2 ^ 59
def prefixEnd_4538091 : Nat := 4983230072969 + 3 ^ 40 * 4538091 * 2
def baseEnd_4538091 : Nat := 776740645614303143930735

theorem tailTrace_4538091 : CollatzResearch.WordTrace tailWord_4538091 prefixEnd_4538091 776740645614303143930735 := by
  unfold tailWord_4538091
  simp only [CollatzResearch.WordTrace]
  refine ⟨165517776602278826083486127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110345184401519217388990751 165517776602278826083486127)
  ·
    refine ⟨248276664903418239125229191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165517776602278826083486127 248276664903418239125229191)
    ·
      refine ⟨372414997355127358687843787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248276664903418239125229191 372414997355127358687843787)
      ·
        refine ⟨558622496032691038031765681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372414997355127358687843787 558622496032691038031765681)
        ·
          refine ⟨418966872024518278523824261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558622496032691038031765681 418966872024518278523824261)
          ·
            refine ⟨78556288504597177223217049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 418966872024518278523824261 78556288504597177223217049)
            ·
              refine ⟨58917216378447882917412787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78556288504597177223217049 58917216378447882917412787)
              ·
                refine ⟨88375824567671824376119181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58917216378447882917412787 88375824567671824376119181)
                ·
                  refine ⟨33140934212876934141044693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88375824567671824376119181 33140934212876934141044693)
                  ·
                    refine ⟨776740645614303143930735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33140934212876934141044693 776740645614303143930735)
                    ·
                      rfl

theorem cell23_4538091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_4538091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538091 prefixEnd_4538091 := by exact prefixLift 4538091
  have htrace : WordTrace (prefixWord ++ tailWord_4538091) baseStart_4538091 baseEnd_4538091 := by
    simpa [prefixWord, tailWord_4538091, baseEnd_4538091] using wordTrace_append hprefix tailTrace_4538091
  have hstable : (prefixWord ++ tailWord_4538091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538091).length < 2 ^ (prefixWord ++ tailWord_4538091).sum := by decide
  have hdescent : baseEnd_4538091 < baseStart_4538091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538145 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4538145 : Nat := 118140960795 + 4538145 * 2 ^ 59
def prefixEnd_4538145 : Nat := 4983230072969 + 3 ^ 40 * 4538145 * 2
def baseEnd_4538145 : Nat := 2330249664798252220516957

theorem tailTrace_4538145 : CollatzResearch.WordTrace tailWord_4538145 prefixEnd_4538145 2330249664798252220516957 := by
  unfold tailWord_4538145
  simp only [CollatzResearch.WordTrace]
  refine ⟨165519746144083193305951889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110346497429388795537301259 165519746144083193305951889)
  ·
    refine ⟨124139809608062394979463917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165519746144083193305951889 124139809608062394979463917)
    ·
      refine ⟨46552428603023398117298969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124139809608062394979463917 46552428603023398117298969)
      ·
        refine ⟨34914321452267548587974227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46552428603023398117298969 34914321452267548587974227)
        ·
          refine ⟨52371482178401322881961341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34914321452267548587974227 52371482178401322881961341)
          ·
            refine ⟨19639305816900496080735503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52371482178401322881961341 19639305816900496080735503)
            ·
              refine ⟨29458958725350744121103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19639305816900496080735503 29458958725350744121103255)
              ·
                refine ⟨44188438088026116181654883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29458958725350744121103255 44188438088026116181654883)
                ·
                  refine ⟨66282657132039174272482325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44188438088026116181654883 66282657132039174272482325)
                  ·
                    refine ⟨3106999553064336294022609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66282657132039174272482325 3106999553064336294022609)
                    ·
                      refine ⟨2330249664798252220516957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3106999553064336294022609 2330249664798252220516957)
                      ·
                        rfl

theorem cell23_4538145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4538145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538145 prefixEnd_4538145 := by exact prefixLift 4538145
  have htrace : WordTrace (prefixWord ++ tailWord_4538145) baseStart_4538145 baseEnd_4538145 := by
    simpa [prefixWord, tailWord_4538145, baseEnd_4538145] using wordTrace_append hprefix tailTrace_4538145
  have hstable : (prefixWord ++ tailWord_4538145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538145).length < 2 ^ (prefixWord ++ tailWord_4538145).sum := by decide
  have hdescent : baseEnd_4538145 < baseStart_4538145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538162 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_4538162 : Nat := 118140960795 + 4538162 * 2 ^ 59
def prefixEnd_4538162 : Nat := 4983230072969 + 3 ^ 40 * 4538162 * 2
def baseEnd_4538162 : Nat := 2330258393969378654004379

theorem tailTrace_4538162 : CollatzResearch.WordTrace tailWord_4538162 prefixEnd_4538162 2330258393969378654004379 := by
  unfold tailWord_4538162
  simp only [CollatzResearch.WordTrace]
  refine ⟨41380091546255401302330185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110346910790014403472880493 41380091546255401302330185)
  ·
    refine ⟨31035068659691550976747639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41380091546255401302330185 31035068659691550976747639)
    ·
      refine ⟨46552602989537326465121459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31035068659691550976747639 46552602989537326465121459)
      ·
        refine ⟨69828904484305989697682189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46552602989537326465121459 69828904484305989697682189)
        ·
          refine ⟨26185839181614746136630821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69828904484305989697682189 26185839181614746136630821)
          ·
            refine ⟨4909844846552764900618279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26185839181614746136630821 4909844846552764900618279)
            ·
              refine ⟨7364767269829147350927419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909844846552764900618279 7364767269829147350927419)
              ·
                refine ⟨11047150904743721026391129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7364767269829147350927419 11047150904743721026391129)
                ·
                  refine ⟨8285363178557790769793347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11047150904743721026391129 8285363178557790769793347)
                  ·
                    refine ⟨12428044767836686154690021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8285363178557790769793347 12428044767836686154690021)
                    ·
                      refine ⟨2330258393969378654004379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12428044767836686154690021 2330258393969378654004379)
                      ·
                        rfl

theorem cell23_4538162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_4538162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538162 prefixEnd_4538162 := by exact prefixLift 4538162
  have htrace : WordTrace (prefixWord ++ tailWord_4538162) baseStart_4538162 baseEnd_4538162 := by
    simpa [prefixWord, tailWord_4538162, baseEnd_4538162] using wordTrace_append hprefix tailTrace_4538162
  have hstable : (prefixWord ++ tailWord_4538162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538162).length < 2 ^ (prefixWord ++ tailWord_4538162).sum := by decide
  have hdescent : baseEnd_4538162 < baseStart_4538162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538172 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_4538172 : Nat := 118140960795 + 4538172 * 2 ^ 59
def prefixEnd_4538172 : Nat := 4983230072969 + 3 ^ 40 * 4538172 * 2
def baseEnd_4538172 : Nat := 776754509591974538293111

theorem tailTrace_4538172 : CollatzResearch.WordTrace tailWord_4538172 prefixEnd_4538172 776754509591974538293111 := by
  unfold tailWord_4538172
  simp only [CollatzResearch.WordTrace]
  refine ⟨82760365457492688458592385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110347153943323584611456513 82760365457492688458592385)
  ·
    refine ⟨62070274093119516343944289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82760365457492688458592385 62070274093119516343944289)
    ·
      refine ⟨46552705569839637257958217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62070274093119516343944289 46552705569839637257958217)
      ·
        refine ⟨34914529177379727943468663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46552705569839637257958217 34914529177379727943468663)
        ·
          refine ⟨52371793766069591915202995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34914529177379727943468663 52371793766069591915202995)
          ·
            refine ⟨78557690649104387872804493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52371793766069591915202995 78557690649104387872804493)
            ·
              refine ⟨29459133993414145452301685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78557690649104387872804493 29459133993414145452301685)
              ·
                refine ⟨2761793811882576136153283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29459133993414145452301685 2761793811882576136153283)
                ·
                  refine ⟨4142690717823864204229925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761793811882576136153283 4142690717823864204229925)
                  ·
                    refine ⟨776754509591974538293111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142690717823864204229925 776754509591974538293111)
                    ·
                      rfl

theorem cell23_4538172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_4538172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538172 prefixEnd_4538172 := by exact prefixLift 4538172
  have htrace : WordTrace (prefixWord ++ tailWord_4538172) baseStart_4538172 baseEnd_4538172 := by
    simpa [prefixWord, tailWord_4538172, baseEnd_4538172] using wordTrace_append hprefix tailTrace_4538172
  have hstable : (prefixWord ++ tailWord_4538172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538172).length < 2 ^ (prefixWord ++ tailWord_4538172).sum := by decide
  have hdescent : baseEnd_4538172 < baseStart_4538172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538189 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_4538189 : Nat := 118140960795 + 4538189 * 2 ^ 59
def prefixEnd_4538189 : Nat := 4983230072969 + 3 ^ 40 * 4538189 * 2
def baseEnd_4538189 : Nat := 776757419315683349455585

theorem tailTrace_4538189 : CollatzResearch.WordTrace tailWord_4538189 prefixEnd_4538189 776757419315683349455585 := by
  unfold tailWord_4538189
  simp only [CollatzResearch.WordTrace]
  refine ⟨165521350955923788820553621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110347567303949192547035747 165521350955923788820553621)
  ·
    refine ⟨7758813326058927600963451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165521350955923788820553621 7758813326058927600963451)
    ·
      refine ⟨11638219989088391401445177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758813326058927600963451 11638219989088391401445177)
      ·
        refine ⟨8728664991816293551083883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11638219989088391401445177 8728664991816293551083883)
        ·
          refine ⟨13092997487724440326625825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8728664991816293551083883 13092997487724440326625825)
          ·
            refine ⟨9819748115793330244969369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13092997487724440326625825 9819748115793330244969369)
            ·
              refine ⟨7364811086844997683727027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9819748115793330244969369 7364811086844997683727027)
              ·
                refine ⟨11047216630267496525590541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7364811086844997683727027 11047216630267496525590541)
                ·
                  refine ⟨4142706236350311197096453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11047216630267496525590541 4142706236350311197096453)
                  ·
                    refine ⟨776757419315683349455585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142706236350311197096453 776757419315683349455585)
                    ·
                      rfl

theorem cell23_4538189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_4538189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538189 prefixEnd_4538189 := by exact prefixLift 4538189
  have htrace : WordTrace (prefixWord ++ tailWord_4538189) baseStart_4538189 baseEnd_4538189 := by
    simpa [prefixWord, tailWord_4538189, baseEnd_4538189] using wordTrace_append hprefix tailTrace_4538189
  have hstable : (prefixWord ++ tailWord_4538189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538189).length < 2 ^ (prefixWord ++ tailWord_4538189).sum := by decide
  have hdescent : baseEnd_4538189 < baseStart_4538189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538245 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_4538245 : Nat := 118140960795 + 4538245 * 2 ^ 59
def prefixEnd_4538245 : Nat := 4983230072969 + 3 ^ 40 * 4538245 * 2
def baseEnd_4538245 : Nat := 776767004287900609755499

theorem tailTrace_4538245 : CollatzResearch.WordTrace tailWord_4538245 prefixEnd_4538245 776767004287900609755499 := by
  unfold tailWord_4538245
  simp only [CollatzResearch.WordTrace]
  refine ⟨165523393443720910384592189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110348928962480606923061459 165523393443720910384592189)
  ·
    refine ⟨62071272541395341394222071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165523393443720910384592189 62071272541395341394222071)
    ·
      refine ⟨93106908812093012091333107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62071272541395341394222071 93106908812093012091333107)
      ·
        refine ⟨139660363218139518136999661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93106908812093012091333107 139660363218139518136999661)
        ·
          refine ⟨52372636206802319301374873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139660363218139518136999661 52372636206802319301374873)
          ·
            refine ⟨39279477155101739476031155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52372636206802319301374873 39279477155101739476031155)
            ·
              refine ⟨58919215732652609214046733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39279477155101739476031155 58919215732652609214046733)
              ·
                refine ⟨22094705899744728455267525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58919215732652609214046733 22094705899744728455267525)
                ·
                  refine ⟨4142757356202136585362661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22094705899744728455267525 4142757356202136585362661)
                  ·
                    refine ⟨776767004287900609755499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142757356202136585362661 776767004287900609755499)
                    ·
                      rfl

theorem cell23_4538245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_4538245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538245 prefixEnd_4538245 := by exact prefixLift 4538245
  have htrace : WordTrace (prefixWord ++ tailWord_4538245) baseStart_4538245 baseEnd_4538245 := by
    simpa [prefixWord, tailWord_4538245, baseEnd_4538245] using wordTrace_append hprefix tailTrace_4538245
  have hstable : (prefixWord ++ tailWord_4538245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538245).length < 2 ^ (prefixWord ++ tailWord_4538245).sum := by decide
  have hdescent : baseEnd_4538245 < baseStart_4538245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538269 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_4538269 : Nat := 118140960795 + 4538269 * 2 ^ 59
def prefixEnd_4538269 : Nat := 4983230072969 + 3 ^ 40 * 4538269 * 2
def baseEnd_4538269 : Nat := 2330313336399409735366387

theorem tailTrace_4538269 : CollatzResearch.WordTrace tailWord_4538269 prefixEnd_4538269 2330313336399409735366387 := by
  unfold tailWord_4538269
  simp only [CollatzResearch.WordTrace]
  refine ⟨165524268795633962483465861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110349512530422641655643907 165524268795633962483465861)
  ·
    refine ⟨31035800399181367965649849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165524268795633962483465861 31035800399181367965649849)
    ·
      refine ⟨23276850299386025974237387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31035800399181367965649849 23276850299386025974237387)
      ·
        refine ⟨34915275449079038961356081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23276850299386025974237387 34915275449079038961356081)
        ·
          refine ⟨26186456586809279221017061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34915275449079038961356081 26186456586809279221017061)
          ·
            refine ⟨4909960610026739853940699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26186456586809279221017061 4909960610026739853940699)
            ·
              refine ⟨7364940915040109780911049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909960610026739853940699 7364940915040109780911049)
              ·
                refine ⟨5523705686280082335683287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7364940915040109780911049 5523705686280082335683287)
                ·
                  refine ⟨8285558529420123503524931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523705686280082335683287 8285558529420123503524931)
                  ·
                    refine ⟨12428337794130185255287397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8285558529420123503524931 12428337794130185255287397)
                    ·
                      refine ⟨2330313336399409735366387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12428337794130185255287397 2330313336399409735366387)
                      ·
                        rfl

theorem cell23_4538269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_4538269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538269 prefixEnd_4538269 := by exact prefixLift 4538269
  have htrace : WordTrace (prefixWord ++ tailWord_4538269) baseStart_4538269 baseEnd_4538269 := by
    simpa [prefixWord, tailWord_4538269, baseEnd_4538269] using wordTrace_append hprefix tailTrace_4538269
  have hstable : (prefixWord ++ tailWord_4538269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538269).length < 2 ^ (prefixWord ++ tailWord_4538269).sum := by decide
  have hdescent : baseEnd_4538269 < baseStart_4538269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538288 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_4538288 : Nat := 118140960795 + 4538288 * 2 ^ 59
def prefixEnd_4538288 : Nat := 4983230072969 + 3 ^ 40 * 4538288 * 2
def baseEnd_4538288 : Nat := 776774364177281720342933

theorem tailTrace_4538288 : CollatzResearch.WordTrace tailWord_4538288 prefixEnd_4538288 776774364177281720342933 := by
  unfold tailWord_4538288
  simp only [CollatzResearch.WordTrace]
  refine ⟨82762480891282564364203759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110349974521710085818938345 82762480891282564364203759)
  ·
    refine ⟨124143721336923846546305639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82762480891282564364203759 124143721336923846546305639)
    ·
      refine ⟨186215582005385769819458459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124143721336923846546305639 186215582005385769819458459)
      ·
        refine ⟨279323373008078654729187689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186215582005385769819458459 279323373008078654729187689)
        ·
          refine ⟨209492529756058991046890767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279323373008078654729187689 209492529756058991046890767)
          ·
            refine ⟨314238794634088486570336151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209492529756058991046890767 314238794634088486570336151)
            ·
              refine ⟨471358191951132729855504227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314238794634088486570336151 471358191951132729855504227)
              ·
                refine ⟨707037287926699094783256341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471358191951132729855504227 707037287926699094783256341)
                ·
                  refine ⟨33142372871564020067965141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 707037287926699094783256341 33142372871564020067965141)
                  ·
                    refine ⟨776774364177281720342933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33142372871564020067965141 776774364177281720342933)
                    ·
                      rfl

theorem cell23_4538288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_4538288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538288 prefixEnd_4538288 := by exact prefixLift 4538288
  have htrace : WordTrace (prefixWord ++ tailWord_4538288) baseStart_4538288 baseEnd_4538288 := by
    simpa [prefixWord, tailWord_4538288, baseEnd_4538288] using wordTrace_append hprefix tailTrace_4538288
  have hstable : (prefixWord ++ tailWord_4538288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538288).length < 2 ^ (prefixWord ++ tailWord_4538288).sum := by decide
  have hdescent : baseEnd_4538288 < baseStart_4538288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538292 : List Nat := [2, 5, 2, 1, 2, 11]
def baseStart_4538292 : Nat := 118140960795 + 4538292 * 2 ^ 59
def prefixEnd_4538292 : Nat := 4983230072969 + 3 ^ 40 * 4538292 * 2
def baseEnd_4538292 : Nat := 9589815417508078787567

theorem tailTrace_4538292 : CollatzResearch.WordTrace tailWord_4538292 prefixEnd_4538292 9589815417508078787567 := by
  unfold tailWord_4538292
  simp only [CollatzResearch.WordTrace]
  refine ⟨82762553837275318705776565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110350071783033758274368753 82762553837275318705776565)
  ·
    refine ⟨7758989422244561128666553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82762553837275318705776565 7758989422244561128666553)
    ·
      refine ⟨5819242066683420846499915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7758989422244561128666553 5819242066683420846499915)
      ·
        refine ⟨8728863100025131269749873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5819242066683420846499915 8728863100025131269749873)
        ·
          refine ⟨6546647325018848452312405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8728863100025131269749873 6546647325018848452312405)
          ·
            refine ⟨9589815417508078787567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6546647325018848452312405 9589815417508078787567)
            ·
              rfl

theorem cell23_4538292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 11].length) (baseStart_4538292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538292 prefixEnd_4538292 := by exact prefixLift 4538292
  have htrace : WordTrace (prefixWord ++ tailWord_4538292) baseStart_4538292 baseEnd_4538292 := by
    simpa [prefixWord, tailWord_4538292, baseEnd_4538292] using wordTrace_append hprefix tailTrace_4538292
  have hstable : (prefixWord ++ tailWord_4538292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538292).length < 2 ^ (prefixWord ++ tailWord_4538292).sum := by decide
  have hdescent : baseEnd_4538292 < baseStart_4538292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538353 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_4538353 : Nat := 118140960795 + 4538353 * 2 ^ 59
def prefixEnd_4538353 : Nat := 4983230072969 + 3 ^ 40 * 4538353 * 2
def baseEnd_4538353 : Nat := 2330356468774387406716001

theorem tailTrace_4538353 : CollatzResearch.WordTrace tailWord_4538353 prefixEnd_4538353 2330356468774387406716001 := by
  unfold tailWord_4538353
  simp only [CollatzResearch.WordTrace]
  refine ⟨165527332527329644829523713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110351555018219763219682475 165527332527329644829523713)
  ·
    refine ⟨124145499395497233622142785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165527332527329644829523713 124145499395497233622142785)
    ·
      refine ⟨93109124546622925216607089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124145499395497233622142785 93109124546622925216607089)
      ·
        refine ⟨69831843409967193912455317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93109124546622925216607089 69831843409967193912455317)
        ·
          refine ⟨3273367659842212214646343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69831843409967193912455317 3273367659842212214646343)
          ·
            refine ⟨4910051489763318321969515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273367659842212214646343 4910051489763318321969515)
            ·
              refine ⟨7365077234644977482954273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910051489763318321969515 7365077234644977482954273)
              ·
                refine ⟨5523807925983733112215705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7365077234644977482954273 5523807925983733112215705)
                ·
                  refine ⟨4142855944487799834161779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5523807925983733112215705 4142855944487799834161779)
                  ·
                    refine ⟨6214283916731699751242669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4142855944487799834161779 6214283916731699751242669)
                    ·
                      refine ⟨2330356468774387406716001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6214283916731699751242669 2330356468774387406716001)
                      ·
                        rfl

theorem cell23_4538353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_4538353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538353 prefixEnd_4538353 := by exact prefixLift 4538353
  have htrace : WordTrace (prefixWord ++ tailWord_4538353) baseStart_4538353 baseEnd_4538353 := by
    simpa [prefixWord, tailWord_4538353, baseEnd_4538353] using wordTrace_append hprefix tailTrace_4538353
  have hstable : (prefixWord ++ tailWord_4538353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538353).length < 2 ^ (prefixWord ++ tailWord_4538353).sum := by decide
  have hdescent : baseEnd_4538353 < baseStart_4538353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538365 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 7]
def baseStart_4538365 : Nat := 118140960795 + 4538365 * 2 ^ 59
def prefixEnd_4538365 : Nat := 4983230072969 + 3 ^ 40 * 4538365 * 2
def baseEnd_4538365 : Nat := 258929181171360151085105

theorem tailTrace_4538365 : CollatzResearch.WordTrace tailWord_4538365 prefixEnd_4538365 258929181171360151085105 := by
  unfold tailWord_4538365
  simp only [CollatzResearch.WordTrace]
  refine ⟨165527770203286170878960549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110351846802190780585973699 165527770203286170878960549)
  ·
    refine ⟨31036456913116157039805103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165527770203286170878960549 31036456913116157039805103)
    ·
      refine ⟨46554685369674235559707655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31036456913116157039805103 46554685369674235559707655)
      ·
        refine ⟨69832028054511353339561483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46554685369674235559707655 69832028054511353339561483)
        ·
          refine ⟨104748042081767030009342225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69832028054511353339561483 104748042081767030009342225)
          ·
            refine ⟨78561031561325272507006669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104748042081767030009342225 78561031561325272507006669)
            ·
              refine ⟨29460386835496977190127501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78561031561325272507006669 29460386835496977190127501)
              ·
                refine ⟨11047645063311366446297813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29460386835496977190127501 11047645063311366446297813)
                ·
                  refine ⟨258929181171360151085105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11047645063311366446297813 258929181171360151085105)
                  ·
                    rfl

theorem cell23_4538365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_4538365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538365 prefixEnd_4538365 := by exact prefixLift 4538365
  have htrace : WordTrace (prefixWord ++ tailWord_4538365) baseStart_4538365 baseEnd_4538365 := by
    simpa [prefixWord, tailWord_4538365, baseEnd_4538365] using wordTrace_append hprefix tailTrace_4538365
  have hstable : (prefixWord ++ tailWord_4538365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538365).length < 2 ^ (prefixWord ++ tailWord_4538365).sum := by decide
  have hdescent : baseEnd_4538365 < baseStart_4538365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538415 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_4538415 : Nat := 118140960795 + 4538415 * 2 ^ 59
def prefixEnd_4538415 : Nat := 4983230072969 + 3 ^ 40 * 4538415 * 2
def baseEnd_4538415 : Nat := 2330388304574966164140715

theorem tailTrace_4538415 : CollatzResearch.WordTrace tailWord_4538415 prefixEnd_4538415 2330388304574966164140715 := by
  unfold tailWord_4538415
  simp only [CollatzResearch.WordTrace]
  refine ⟨165529593853105029418280699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110353062568736686278853799 165529593853105029418280699)
  ·
    refine ⟨248294390779657544127421049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165529593853105029418280699 248294390779657544127421049)
    ·
      refine ⟨186220793084743158095565787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248294390779657544127421049 186220793084743158095565787)
      ·
        refine ⟨279331189627114737143348681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186220793084743158095565787 279331189627114737143348681)
        ·
          refine ⟨209498392220336052857511511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279331189627114737143348681 209498392220336052857511511)
          ·
            refine ⟨314247588330504079286267267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209498392220336052857511511 314247588330504079286267267)
            ·
              refine ⟨471371382495756118929400901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314247588330504079286267267 471371382495756118929400901)
              ·
                refine ⟨88382134217954272299262669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471371382495756118929400901 88382134217954272299262669)
                ·
                  refine ⟨33143300331732852112223501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88382134217954272299262669 33143300331732852112223501)
                  ·
                    refine ⟨12428737624399819542083813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33143300331732852112223501 12428737624399819542083813)
                    ·
                      refine ⟨2330388304574966164140715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12428737624399819542083813 2330388304574966164140715)
                      ·
                        rfl

theorem cell23_4538415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_4538415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538415 prefixEnd_4538415 := by exact prefixLift 4538415
  have htrace : WordTrace (prefixWord ++ tailWord_4538415) baseStart_4538415 baseEnd_4538415 := by
    simpa [prefixWord, tailWord_4538415, baseEnd_4538415] using wordTrace_append hprefix tailTrace_4538415
  have hstable : (prefixWord ++ tailWord_4538415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538415).length < 2 ^ (prefixWord ++ tailWord_4538415).sum := by decide
  have hdescent : baseEnd_4538415 < baseStart_4538415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538442 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_4538442 : Nat := 118140960795 + 4538442 * 2 ^ 59
def prefixEnd_4538442 : Nat := 4983230072969 + 3 ^ 40 * 4538442 * 2
def baseEnd_4538442 : Nat := 776800722850879186167697

theorem tailTrace_4538442 : CollatzResearch.WordTrace tailWord_4538442 prefixEnd_4538442 776800722850879186167697 := by
  unfold tailWord_4538442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41382644656001803257378395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110353719082671475353009053 41382644656001803257378395)
  ·
    refine ⟨62073966984002704886067593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41382644656001803257378395 62073966984002704886067593)
    ·
      refine ⟨46555475238002028664550695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62073966984002704886067593 46555475238002028664550695)
      ·
        refine ⟨69833212857003042996826043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46555475238002028664550695 69833212857003042996826043)
        ·
          refine ⟨104749819285504564495239065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69833212857003042996826043 104749819285504564495239065)
          ·
            refine ⟨78562364464128423371429299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104749819285504564495239065 78562364464128423371429299)
            ·
              refine ⟨117843546696192635057143949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78562364464128423371429299 117843546696192635057143949)
              ·
                refine ⟨44191330011072238146428981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117843546696192635057143949 44191330011072238146428981)
                ·
                  refine ⟨4142937188538022326227717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44191330011072238146428981 4142937188538022326227717)
                  ·
                    refine ⟨776800722850879186167697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142937188538022326227717 776800722850879186167697)
                    ·
                      rfl

theorem cell23_4538442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_4538442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538442 prefixEnd_4538442 := by exact prefixLift 4538442
  have htrace : WordTrace (prefixWord ++ tailWord_4538442) baseStart_4538442 baseEnd_4538442 := by
    simpa [prefixWord, tailWord_4538442, baseEnd_4538442] using wordTrace_append hprefix tailTrace_4538442
  have hstable : (prefixWord ++ tailWord_4538442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538442).length < 2 ^ (prefixWord ++ tailWord_4538442).sum := by decide
  have hdescent : baseEnd_4538442 < baseStart_4538442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538455 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 10]
def baseStart_4538455 : Nat := 118140960795 + 4538455 * 2 ^ 59
def prefixEnd_4538455 : Nat := 4983230072969 + 3 ^ 40 * 4538455 * 2
def baseEnd_4538455 : Nat := 258934315977905111960059

theorem tailTrace_4538455 : CollatzResearch.WordTrace tailWord_4538455 prefixEnd_4538455 258934315977905111960059 := by
  unfold tailWord_4538455
  simp only [CollatzResearch.WordTrace]
  refine ⟨165531052772960116249736819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110354035181973410833157879 165531052772960116249736819)
  ·
    refine ⟨248296579159440174374605229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165531052772960116249736819 248296579159440174374605229)
    ·
      refine ⟨93111217184790065390476961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248296579159440174374605229 93111217184790065390476961)
      ·
        refine ⟨69833412888592549042857721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93111217184790065390476961 69833412888592549042857721)
        ·
          refine ⟨52375059666444411782143291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69833412888592549042857721 52375059666444411782143291)
          ·
            refine ⟨78562589499666617673214937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52375059666444411782143291 78562589499666617673214937)
            ·
              refine ⟨58921942124749963254911203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78562589499666617673214937 58921942124749963254911203)
              ·
                refine ⟨88382913187124944882366805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58921942124749963254911203 88382913187124944882366805)
                ·
                  refine ⟨258934315977905111960059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88382913187124944882366805 258934315977905111960059)
                  ·
                    rfl

theorem cell23_4538455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 10].length) (baseStart_4538455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538455 prefixEnd_4538455 := by exact prefixLift 4538455
  have htrace : WordTrace (prefixWord ++ tailWord_4538455) baseStart_4538455 baseEnd_4538455 := by
    simpa [prefixWord, tailWord_4538455, baseEnd_4538455] using wordTrace_append hprefix tailTrace_4538455
  have hstable : (prefixWord ++ tailWord_4538455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538455).length < 2 ^ (prefixWord ++ tailWord_4538455).sum := by decide
  have hdescent : baseEnd_4538455 < baseStart_4538455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538469 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_4538469 : Nat := 118140960795 + 4538469 * 2 ^ 59
def prefixEnd_4538469 : Nat := 4983230072969 + 3 ^ 40 * 4538469 * 2
def baseEnd_4538469 : Nat := 2330416032530308952865467

theorem tailTrace_4538469 : CollatzResearch.WordTrace tailWord_4538469 prefixEnd_4538469 2330416032530308952865467 := by
  unfold tailWord_4538469
  simp only [CollatzResearch.WordTrace]
  refine ⟨165531563394909396640746461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110354375596606264427164307 165531563394909396640746461)
  ·
    refine ⟨62074336273091023740279923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165531563394909396640746461 62074336273091023740279923)
    ·
      refine ⟨93111504409636535610419885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62074336273091023740279923 93111504409636535610419885)
      ·
        refine ⟨34916814153613700853907457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93111504409636535610419885 34916814153613700853907457)
        ·
          refine ⟨26187610615210275640430593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34916814153613700853907457 26187610615210275640430593)
          ·
            refine ⟨19640707961407706730322945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26187610615210275640430593 19640707961407706730322945)
            ·
              refine ⟨14730530971055780047742209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19640707961407706730322945 14730530971055780047742209)
              ·
                refine ⟨11047898228291835035806657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14730530971055780047742209 11047898228291835035806657)
                ·
                  refine ⟨8285923671218876276854993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11047898228291835035806657 8285923671218876276854993)
                  ·
                    refine ⟨6214442753414157207641245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8285923671218876276854993 6214442753414157207641245)
                    ·
                      refine ⟨2330416032530308952865467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6214442753414157207641245 2330416032530308952865467)
                      ·
                        rfl

theorem cell23_4538469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_4538469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538469 prefixEnd_4538469 := by exact prefixLift 4538469
  have htrace : WordTrace (prefixWord ++ tailWord_4538469) baseStart_4538469 baseEnd_4538469 := by
    simpa [prefixWord, tailWord_4538469, baseEnd_4538469] using wordTrace_append hprefix tailTrace_4538469
  have hstable : (prefixWord ++ tailWord_4538469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538469).length < 2 ^ (prefixWord ++ tailWord_4538469).sum := by decide
  have hdescent : baseEnd_4538469 < baseStart_4538469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538476 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_4538476 : Nat := 118140960795 + 4538476 * 2 ^ 59
def prefixEnd_4538476 : Nat := 4983230072969 + 3 ^ 40 * 4538476 * 2
def baseEnd_4538476 : Nat := 776806542298296808492645

theorem tailTrace_4538476 : CollatzResearch.WordTrace tailWord_4538476 prefixEnd_4538476 776806542298296808492645 := by
  unfold tailWord_4538476
  simp only [CollatzResearch.WordTrace]
  refine ⟨82765909352942018418125641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110354545803922691224167521 82765909352942018418125641)
  ·
    refine ⟨62074432014706513813594231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82765909352942018418125641 62074432014706513813594231)
    ·
      refine ⟨93111648022059770720391347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62074432014706513813594231 93111648022059770720391347)
      ·
        refine ⟨139667472033089656080587021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93111648022059770720391347 139667472033089656080587021)
        ·
          refine ⟨52375302012408621030220133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139667472033089656080587021 52375302012408621030220133)
          ·
            refine ⟨9820369127326616443166275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52375302012408621030220133 9820369127326616443166275)
            ·
              refine ⟨14730553690989924664749413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9820369127326616443166275 14730553690989924664749413)
              ·
                refine ⟨2761978817060610874640515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14730553690989924664749413 2761978817060610874640515)
                ·
                  refine ⟨4142968225590916311960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761978817060610874640515 4142968225590916311960773)
                  ·
                    refine ⟨776806542298296808492645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142968225590916311960773 776806542298296808492645)
                    ·
                      rfl

theorem cell23_4538476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_4538476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538476 prefixEnd_4538476 := by exact prefixLift 4538476
  have htrace : WordTrace (prefixWord ++ tailWord_4538476) baseStart_4538476 baseEnd_4538476 := by
    simpa [prefixWord, tailWord_4538476, baseEnd_4538476] using wordTrace_append hprefix tailTrace_4538476
  have hstable : (prefixWord ++ tailWord_4538476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538476).length < 2 ^ (prefixWord ++ tailWord_4538476).sum := by decide
  have hdescent : baseEnd_4538476 < baseStart_4538476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538499 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 3]
def baseStart_4538499 : Nat := 118140960795 + 4538499 * 2 ^ 59
def prefixEnd_4538499 : Nat := 4983230072969 + 3 ^ 40 * 4538499 * 2
def baseEnd_4538499 : Nat := 2330431436949943835490329

theorem tailTrace_4538499 : CollatzResearch.WordTrace tailWord_4538499 prefixEnd_4538499 2330431436949943835490329 := by
  unfold tailWord_4538499
  simp only [CollatzResearch.WordTrace]
  refine ⟨165532657584800711764338551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110355105056533807842892367 165532657584800711764338551)
  ·
    refine ⟨248298986377201067646507827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165532657584800711764338551 248298986377201067646507827)
    ·
      refine ⟨372448479565801601469761741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248298986377201067646507827 372448479565801601469761741)
      ·
        refine ⟨139668179837175600551160653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372448479565801601469761741 139668179837175600551160653)
        ·
          refine ⟨52375567438940850206685245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139668179837175600551160653 52375567438940850206685245)
          ·
            refine ⟨19640837789602818827506967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52375567438940850206685245 19640837789602818827506967)
            ·
              refine ⟨29461256684404228241260451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19640837789602818827506967 29461256684404228241260451)
              ·
                refine ⟨44191885026606342361890677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29461256684404228241260451 44191885026606342361890677)
                ·
                  refine ⟨4142989221244344596427251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44191885026606342361890677 4142989221244344596427251)
                  ·
                    refine ⟨6214483831866516894640877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4142989221244344596427251 6214483831866516894640877)
                    ·
                      refine ⟨2330431436949943835490329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6214483831866516894640877 2330431436949943835490329)
                      ·
                        rfl

theorem cell23_4538499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_4538499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538499 prefixEnd_4538499 := by exact prefixLift 4538499
  have htrace : WordTrace (prefixWord ++ tailWord_4538499) baseStart_4538499 baseEnd_4538499 := by
    simpa [prefixWord, tailWord_4538499, baseEnd_4538499] using wordTrace_append hprefix tailTrace_4538499
  have hstable : (prefixWord ++ tailWord_4538499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538499).length < 2 ^ (prefixWord ++ tailWord_4538499).sum := by decide
  have hdescent : baseEnd_4538499 < baseStart_4538499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538552 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_4538552 : Nat := 118140960795 + 4538552 * 2 ^ 59
def prefixEnd_4538552 : Nat := 4983230072969 + 3 ^ 40 * 4538552 * 2
def baseEnd_4538552 : Nat := 2330458651424632128127585

theorem tailTrace_4538552 : CollatzResearch.WordTrace tailWord_4538552 prefixEnd_4538552 2330458651424632128127585 := by
  unfold tailWord_4538552
  simp only [CollatzResearch.WordTrace]
  refine ⟨82767295326804350908008955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110356393769072467877345273 82767295326804350908008955)
  ·
    refine ⟨124150942990206526362013433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82767295326804350908008955 124150942990206526362013433)
    ·
      refine ⟨93113207242654894771510075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124150942990206526362013433 93113207242654894771510075)
      ·
        refine ⟨139669810863982342157265113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93113207242654894771510075 139669810863982342157265113)
        ·
          refine ⟨104752358147986756617948835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139669810863982342157265113 104752358147986756617948835)
          ·
            refine ⟨157128537221980134926923253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104752358147986756617948835 157128537221980134926923253)
            ·
              refine ⟨14730800364560637649399055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157128537221980134926923253 14730800364560637649399055)
              ·
                refine ⟨22096200546840956474098583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14730800364560637649399055 22096200546840956474098583)
                ·
                  refine ⟨33144300820261434711147875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22096200546840956474098583 33144300820261434711147875)
                  ·
                    refine ⟨49716451230392152066721813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33144300820261434711147875 49716451230392152066721813)
                    ·
                      refine ⟨2330458651424632128127585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49716451230392152066721813 2330458651424632128127585)
                      ·
                        rfl

theorem cell23_4538552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_4538552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538552 prefixEnd_4538552 := by exact prefixLift 4538552
  have htrace : WordTrace (prefixWord ++ tailWord_4538552) baseStart_4538552 baseEnd_4538552 := by
    simpa [prefixWord, tailWord_4538552, baseEnd_4538552] using wordTrace_append hprefix tailTrace_4538552
  have hstable : (prefixWord ++ tailWord_4538552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538552).length < 2 ^ (prefixWord ++ tailWord_4538552).sum := by decide
  have hdescent : baseEnd_4538552 < baseStart_4538552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538592 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_4538592 : Nat := 118140960795 + 4538592 * 2 ^ 59
def prefixEnd_4538592 : Nat := 4983230072969 + 3 ^ 40 * 4538592 * 2
def baseEnd_4538592 : Nat := 776826396883603990542467

theorem tailTrace_4538592 : CollatzResearch.WordTrace tailWord_4538592 prefixEnd_4538592 776826396883603990542467 := by
  unfold tailWord_4538592
  simp only [CollatzResearch.WordTrace]
  refine ⟨82768024786731894323737015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110357366382309192431649353 82768024786731894323737015)
  ·
    refine ⟨124152037180097841485605523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82768024786731894323737015 124152037180097841485605523)
    ·
      refine ⟨186228055770146762228408285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124152037180097841485605523 186228055770146762228408285)
      ·
        refine ⟨69835520913805035835653107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186228055770146762228408285 69835520913805035835653107)
        ·
          refine ⟨104753281370707553753479661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69835520913805035835653107 104753281370707553753479661)
          ·
            refine ⟨39282480514015332657554873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104753281370707553753479661 39282480514015332657554873)
            ·
              refine ⟨29461860385511499493166155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39282480514015332657554873 29461860385511499493166155)
              ·
                refine ⟨44192790578267249239749233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29461860385511499493166155 44192790578267249239749233)
                ·
                  refine ⟨33144592933700436929811925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44192790578267249239749233 33144592933700436929811925)
                  ·
                    refine ⟨776826396883603990542467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33144592933700436929811925 776826396883603990542467)
                    ·
                      rfl

theorem cell23_4538592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_4538592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538592 prefixEnd_4538592 := by exact prefixLift 4538592
  have htrace : WordTrace (prefixWord ++ tailWord_4538592) baseStart_4538592 baseEnd_4538592 := by
    simpa [prefixWord, tailWord_4538592, baseEnd_4538592] using wordTrace_append hprefix tailTrace_4538592
  have hstable : (prefixWord ++ tailWord_4538592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538592).length < 2 ^ (prefixWord ++ tailWord_4538592).sum := by decide
  have hdescent : baseEnd_4538592 < baseStart_4538592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538659 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4538659 : Nat := 118140960795 + 4538659 * 2 ^ 59
def prefixEnd_4538659 : Nat := 4983230072969 + 3 ^ 40 * 4538659 * 2
def baseEnd_4538659 : Nat := 2330513593854663209489593

theorem tailTrace_4538659 : CollatzResearch.WordTrace tailWord_4538659 prefixEnd_4538659 2330513593854663209489593 := by
  unfold tailWord_4538659
  simp only [CollatzResearch.WordTrace]
  refine ⟨165538493264221059090163031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110358995509480706060108687 165538493264221059090163031)
  ·
    refine ⟨248307739896331588635244547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165538493264221059090163031 248307739896331588635244547)
    ·
      refine ⟨372461609844497382952866821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248307739896331588635244547 372461609844497382952866821)
      ·
        refine ⟨69836551845843259303662529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372461609844497382952866821 69836551845843259303662529)
        ·
          refine ⟨52377413884382444477746897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69836551845843259303662529 52377413884382444477746897)
          ·
            refine ⟨39283060413286833358310173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52377413884382444477746897 39283060413286833358310173)
            ·
              refine ⟨14731147654982562509366315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39283060413286833358310173 14731147654982562509366315)
              ·
                refine ⟨22096721482473843764049473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14731147654982562509366315 22096721482473843764049473)
                ·
                  refine ⟨16572541111855382823037105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22096721482473843764049473 16572541111855382823037105)
                  ·
                    refine ⟨12429405833891537117277829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16572541111855382823037105 12429405833891537117277829)
                    ·
                      refine ⟨2330513593854663209489593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12429405833891537117277829 2330513593854663209489593)
                      ·
                        rfl

theorem cell23_4538659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4538659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538659 prefixEnd_4538659 := by exact prefixLift 4538659
  have htrace : WordTrace (prefixWord ++ tailWord_4538659) baseStart_4538659 baseEnd_4538659 := by
    simpa [prefixWord, tailWord_4538659, baseEnd_4538659] using wordTrace_append hprefix tailTrace_4538659
  have hstable : (prefixWord ++ tailWord_4538659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538659).length < 2 ^ (prefixWord ++ tailWord_4538659).sum := by decide
  have hdescent : baseEnd_4538659 < baseStart_4538659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538706 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_4538706 : Nat := 118140960795 + 4538706 * 2 ^ 59
def prefixEnd_4538706 : Nat := 4983230072969 + 3 ^ 40 * 4538706 * 2
def baseEnd_4538706 : Nat := 2330537727445424525601877

theorem tailTrace_4538706 : CollatzResearch.WordTrace tailWord_4538706 prefixEnd_4538706 2330537727445424525601877 := by
  unfold tailWord_4538706
  simp only [CollatzResearch.WordTrace]
  refine ⟨41385051873762696529280993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110360138330033857411415981 41385051873762696529280993)
  ·
    refine ⟨31038788905322022396960745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41385051873762696529280993 31038788905322022396960745)
    ·
      refine ⟨23279091678991516797720559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31038788905322022396960745 23279091678991516797720559)
      ·
        refine ⟨34918637518487275196580839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23279091678991516797720559 34918637518487275196580839)
        ·
          refine ⟨52377956277730912794871259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34918637518487275196580839 52377956277730912794871259)
          ·
            refine ⟨78566934416596369192306889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52377956277730912794871259 78566934416596369192306889)
            ·
              refine ⟨58925200812447276894230167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78566934416596369192306889 58925200812447276894230167)
              ·
                refine ⟨88387801218670915341345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58925200812447276894230167 88387801218670915341345251)
                ·
                  refine ⟨132581701828006373012017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88387801218670915341345251 132581701828006373012017877)
                  ·
                    refine ⟨3107383636593899367469169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 132581701828006373012017877 3107383636593899367469169)
                    ·
                      refine ⟨2330537727445424525601877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107383636593899367469169 2330537727445424525601877)
                      ·
                        rfl

theorem cell23_4538706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_4538706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538706 prefixEnd_4538706 := by exact prefixLift 4538706
  have htrace : WordTrace (prefixWord ++ tailWord_4538706) baseStart_4538706 baseEnd_4538706 := by
    simpa [prefixWord, tailWord_4538706, baseEnd_4538706] using wordTrace_append hprefix tailTrace_4538706
  have hstable : (prefixWord ++ tailWord_4538706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538706).length < 2 ^ (prefixWord ++ tailWord_4538706).sum := by decide
  have hdescent : baseEnd_4538706 < baseStart_4538706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538719 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_4538719 : Nat := 118140960795 + 4538719 * 2 ^ 59
def prefixEnd_4538719 : Nat := 4983230072969 + 3 ^ 40 * 4538719 * 2
def baseEnd_4538719 : Nat := 2330544402693932974739317

theorem tailTrace_4538719 : CollatzResearch.WordTrace tailWord_4538719 prefixEnd_4538719 2330544402693932974739317 := by
  unfold tailWord_4538719
  simp only [CollatzResearch.WordTrace]
  refine ⟨165540681644003689337347211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110360454429335792891564807 165540681644003689337347211)
  ·
    refine ⟨248311022466005534006020817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165540681644003689337347211 248311022466005534006020817)
    ·
      refine ⟨186233266849504150504515613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248311022466005534006020817 186233266849504150504515613)
      ·
        refine ⟨69837475068564056439193355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186233266849504150504515613 69837475068564056439193355)
        ·
          refine ⟨104756212602846084658790033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69837475068564056439193355 104756212602846084658790033)
          ·
            refine ⟨78567159452134563494092525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104756212602846084658790033 78567159452134563494092525)
            ·
              refine ⟨29462684794550461310284697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78567159452134563494092525 29462684794550461310284697)
              ·
                refine ⟨22097013595912845982713523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29462684794550461310284697 22097013595912845982713523)
                ·
                  refine ⟨33145520393869268974070285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22097013595912845982713523 33145520393869268974070285)
                  ·
                    refine ⟨12429570147700975865276357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33145520393869268974070285 12429570147700975865276357)
                    ·
                      refine ⟨2330544402693932974739317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12429570147700975865276357 2330544402693932974739317)
                      ·
                        rfl

theorem cell23_4538719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_4538719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538719 prefixEnd_4538719 := by exact prefixLift 4538719
  have htrace : WordTrace (prefixWord ++ tailWord_4538719) baseStart_4538719 baseEnd_4538719 := by
    simpa [prefixWord, tailWord_4538719, baseEnd_4538719] using wordTrace_append hprefix tailTrace_4538719
  have hstable : (prefixWord ++ tailWord_4538719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538719).length < 2 ^ (prefixWord ++ tailWord_4538719).sum := by decide
  have hdescent : baseEnd_4538719 < baseStart_4538719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538753 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4538753 : Nat := 118140960795 + 4538753 * 2 ^ 59
def prefixEnd_4538753 : Nat := 4983230072969 + 3 ^ 40 * 4538753 * 2
def baseEnd_4538753 : Nat := 2330561861036185841714161

theorem tailTrace_4538753 : CollatzResearch.WordTrace tailWord_4538753 prefixEnd_4538753 2330561861036185841714161 := by
  unfold tailWord_4538753
  simp only [CollatzResearch.WordTrace]
  refine ⟨165541921725880513144084913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110361281150587008762723275 165541921725880513144084913)
  ·
    refine ⟨124156441294410384858063685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165541921725880513144084913 124156441294410384858063685)
    ·
      refine ⟨23279332742701947160886941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124156441294410384858063685 23279332742701947160886941)
      ·
        refine ⟨8729749778513230185332603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23279332742701947160886941 8729749778513230185332603)
        ·
          refine ⟨13094624667769845277998905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8729749778513230185332603 13094624667769845277998905)
          ·
            refine ⟨9820968500827383958499179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13094624667769845277998905 9820968500827383958499179)
            ·
              refine ⟨14731452751241075937748769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9820968500827383958499179 14731452751241075937748769)
              ·
                refine ⟨11048589563430806953311577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14731452751241075937748769 11048589563430806953311577)
                ·
                  refine ⟨8286442172573105214983683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11048589563430806953311577 8286442172573105214983683)
                  ·
                    refine ⟨12429663258859657822475525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8286442172573105214983683 12429663258859657822475525)
                    ·
                      refine ⟨2330561861036185841714161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12429663258859657822475525 2330561861036185841714161)
                      ·
                        rfl

theorem cell23_4538753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4538753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538753 prefixEnd_4538753 := by exact prefixLift 4538753
  have htrace : WordTrace (prefixWord ++ tailWord_4538753) baseStart_4538753 baseEnd_4538753 := by
    simpa [prefixWord, tailWord_4538753, baseEnd_4538753] using wordTrace_append hprefix tailTrace_4538753
  have hstable : (prefixWord ++ tailWord_4538753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538753).length < 2 ^ (prefixWord ++ tailWord_4538753).sum := by decide
  have hdescent : baseEnd_4538753 < baseStart_4538753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538759 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 8]
def baseStart_4538759 : Nat := 118140960795 + 4538759 * 2 ^ 59
def prefixEnd_4538759 : Nat := 4983230072969 + 3 ^ 40 * 4538759 * 2
def baseEnd_4538759 : Nat := 258951660213345868693237

theorem tailTrace_4538759 : CollatzResearch.WordTrace tailWord_4538759 prefixEnd_4538759 258951660213345868693237 := by
  unfold tailWord_4538759
  simp only [CollatzResearch.WordTrace]
  refine ⟨165542140563858776168803331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110361427042572517445868887 165542140563858776168803331)
  ·
    refine ⟨248313210845788164253204997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165542140563858776168803331 248313210845788164253204997)
    ·
      refine ⟨46558727033585280797475937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248313210845788164253204997 46558727033585280797475937)
      ·
        refine ⟨34919045275188960598106953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46558727033585280797475937 34919045275188960598106953)
        ·
          refine ⟨26189283956391720448580215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34919045275188960598106953 26189283956391720448580215)
          ·
            refine ⟨39283925934587580672870323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26189283956391720448580215 39283925934587580672870323)
            ·
              refine ⟨58925888901881371009305485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39283925934587580672870323 58925888901881371009305485)
              ·
                refine ⟨22097208338205514128489557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58925888901881371009305485 22097208338205514128489557)
                ·
                  refine ⟨258951660213345868693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22097208338205514128489557 258951660213345868693237)
                  ·
                    rfl

theorem cell23_4538759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 8].length) (baseStart_4538759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538759 prefixEnd_4538759 := by exact prefixLift 4538759
  have htrace : WordTrace (prefixWord ++ tailWord_4538759) baseStart_4538759 baseEnd_4538759 := by
    simpa [prefixWord, tailWord_4538759, baseEnd_4538759] using wordTrace_append hprefix tailTrace_4538759
  have hstable : (prefixWord ++ tailWord_4538759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538759).length < 2 ^ (prefixWord ++ tailWord_4538759).sum := by decide
  have hdescent : baseEnd_4538759 < baseStart_4538759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538763 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 3, 4]
def baseStart_4538763 : Nat := 118140960795 + 4538763 * 2 ^ 59
def prefixEnd_4538763 : Nat := 4983230072969 + 3 ^ 40 * 4538763 * 2
def baseEnd_4538763 : Nat := 776855665280910267529705

theorem tailTrace_4538763 : CollatzResearch.WordTrace tailWord_4538763 prefixEnd_4538763 776855665280910267529705 := by
  unfold tailWord_4538763
  simp only [CollatzResearch.WordTrace]
  refine ⟨165542286455844284851948943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110361524303896189901299295 165542286455844284851948943)
  ·
    refine ⟨248313429683766427277923415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165542286455844284851948943 248313429683766427277923415)
    ·
      refine ⟨372470144525649640916885123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248313429683766427277923415 372470144525649640916885123)
      ·
        refine ⟨558705216788474461375327685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372470144525649640916885123 558705216788474461375327685)
        ·
          refine ⟨104757228147838961507873941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 558705216788474461375327685 104757228147838961507873941)
          ·
            refine ⟨4910495069429951320681591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104757228147838961507873941 4910495069429951320681591)
            ·
              refine ⟨7365742604144926981022387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910495069429951320681591 7365742604144926981022387)
              ·
                refine ⟨11048613906217390471533581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7365742604144926981022387 11048613906217390471533581)
                ·
                  refine ⟨4143230214831521426825093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11048613906217390471533581 4143230214831521426825093)
                  ·
                    refine ⟨776855665280910267529705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143230214831521426825093 776855665280910267529705)
                    ·
                      rfl

theorem cell23_4538763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 4].length) (baseStart_4538763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538763 prefixEnd_4538763 := by exact prefixLift 4538763
  have htrace : WordTrace (prefixWord ++ tailWord_4538763) baseStart_4538763 baseEnd_4538763 := by
    simpa [prefixWord, tailWord_4538763, baseEnd_4538763] using wordTrace_append hprefix tailTrace_4538763
  have hstable : (prefixWord ++ tailWord_4538763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538763).length < 2 ^ (prefixWord ++ tailWord_4538763).sum := by decide
  have hdescent : baseEnd_4538763 < baseStart_4538763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538819 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 5, 6]
def baseStart_4538819 : Nat := 118140960795 + 4538819 * 2 ^ 59
def prefixEnd_4538819 : Nat := 4983230072969 + 3 ^ 40 * 4538819 * 2
def baseEnd_4538819 : Nat := 776865250253127527829619

theorem tailTrace_4538819 : CollatzResearch.WordTrace tailWord_4538819 prefixEnd_4538819 776865250253127527829619 := by
  unfold tailWord_4538819
  simp only [CollatzResearch.WordTrace]
  refine ⟨165544328943641406415987511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110362885962427604277325007 165544328943641406415987511)
  ·
    refine ⟨248316493415462109623981267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165544328943641406415987511 248316493415462109623981267)
    ·
      refine ⟨372474740123193164435971901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248316493415462109623981267 372474740123193164435971901)
      ·
        refine ⟨139678027546197436663489463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372474740123193164435971901 139678027546197436663489463)
        ·
          refine ⟨209517041319296154995234195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139678027546197436663489463 209517041319296154995234195)
          ·
            refine ⟨314275561978944232492851293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209517041319296154995234195 314275561978944232492851293)
            ·
              refine ⟨117853335742104087184819235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314275561978944232492851293 117853335742104087184819235)
              ·
                refine ⟨176780003613156130777228853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117853335742104087184819235 176780003613156130777228853)
                ·
                  refine ⟨16573125338733387260365205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176780003613156130777228853 16573125338733387260365205)
                  ·
                    refine ⟨776865250253127527829619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16573125338733387260365205 776865250253127527829619)
                    ·
                      rfl

theorem cell23_4538819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_4538819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538819 prefixEnd_4538819 := by exact prefixLift 4538819
  have htrace : WordTrace (prefixWord ++ tailWord_4538819) baseStart_4538819 baseEnd_4538819 := by
    simpa [prefixWord, tailWord_4538819, baseEnd_4538819] using wordTrace_append hprefix tailTrace_4538819
  have hstable : (prefixWord ++ tailWord_4538819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538819).length < 2 ^ (prefixWord ++ tailWord_4538819).sum := by decide
  have hdescent : baseEnd_4538819 < baseStart_4538819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538826 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_4538826 : Nat := 118140960795 + 4538826 * 2 ^ 59
def prefixEnd_4538826 : Nat := 4983230072969 + 3 ^ 40 * 4538826 * 2
def baseEnd_4538826 : Nat := 2330599345123964056101325

theorem tailTrace_4538826 : CollatzResearch.WordTrace tailWord_4538826 prefixEnd_4538826 2330599345123964056101325 := by
  unfold tailWord_4538826
  simp only [CollatzResearch.WordTrace]
  refine ⟨41386146063654011652873083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110363056169744031074328221 41386146063654011652873083)
  ·
    refine ⟨62079219095481017479309625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41386146063654011652873083 62079219095481017479309625)
    ·
      refine ⟨46559414321610763109482219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62079219095481017479309625 46559414321610763109482219)
      ·
        refine ⟨69839121482416144664223329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46559414321610763109482219 69839121482416144664223329)
        ·
          refine ⟨52379341111812108498167497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69839121482416144664223329 52379341111812108498167497)
          ·
            refine ⟨39284505833859081373625623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52379341111812108498167497 39284505833859081373625623)
            ·
              refine ⟨58926758750788622060438435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39284505833859081373625623 58926758750788622060438435)
              ·
                refine ⟨88390138126182933090657653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58926758750788622060438435 88390138126182933090657653)
                ·
                  refine ⟨8286575449329649977249155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88390138126182933090657653 8286575449329649977249155)
                  ·
                    refine ⟨12429863173994474965873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8286575449329649977249155 12429863173994474965873733)
                    ·
                      refine ⟨2330599345123964056101325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12429863173994474965873733 2330599345123964056101325)
                      ·
                        rfl

theorem cell23_4538826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_4538826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538826 prefixEnd_4538826 := by exact prefixLift 4538826
  have htrace : WordTrace (prefixWord ++ tailWord_4538826) baseStart_4538826 baseEnd_4538826 := by
    simpa [prefixWord, tailWord_4538826, baseEnd_4538826] using wordTrace_append hprefix tailTrace_4538826
  have hstable : (prefixWord ++ tailWord_4538826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538826).length < 2 ^ (prefixWord ++ tailWord_4538826).sum := by decide
  have hdescent : baseEnd_4538826 < baseStart_4538826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538877 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_4538877 : Nat := 118140960795 + 4538877 * 2 ^ 59
def prefixEnd_4538877 : Nat := 4983230072969 + 3 ^ 40 * 4538877 * 2
def baseEnd_4538877 : Nat := 2330625532637343356563591

theorem tailTrace_4538877 : CollatzResearch.WordTrace tailWord_4538877 prefixEnd_4538877 2330625532637343356563591 := by
  unfold tailWord_4538877
  simp only [CollatzResearch.WordTrace]
  refine ⟨165546444377431282321598885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110364296251620854881065923 165546444377431282321598885)
  ·
    refine ⟨31039958320768365435299791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165546444377431282321598885 31039958320768365435299791)
    ·
      refine ⟨46559937481152548152949687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31039958320768365435299791 46559937481152548152949687)
      ·
        refine ⟨69839906221728822229424531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46559937481152548152949687 69839906221728822229424531)
        ·
          refine ⟨104759859332593233344136797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69839906221728822229424531 104759859332593233344136797)
          ·
            refine ⟨39284947249722462504051299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104759859332593233344136797 39284947249722462504051299)
            ·
              refine ⟨58927420874583693756076949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39284947249722462504051299 58927420874583693756076949)
              ·
                refine ⟨2762222853496110644816107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58927420874583693756076949 2762222853496110644816107)
                ·
                  refine ⟨4143334280244165967224161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762222853496110644816107 4143334280244165967224161)
                  ·
                    refine ⟨3107500710183124475418121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4143334280244165967224161 3107500710183124475418121)
                    ·
                      refine ⟨2330625532637343356563591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107500710183124475418121 2330625532637343356563591)
                      ·
                        rfl

theorem cell23_4538877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_4538877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538877 prefixEnd_4538877 := by exact prefixLift 4538877
  have htrace : WordTrace (prefixWord ++ tailWord_4538877) baseStart_4538877 baseEnd_4538877 := by
    simpa [prefixWord, tailWord_4538877, baseEnd_4538877] using wordTrace_append hprefix tailTrace_4538877
  have hstable : (prefixWord ++ tailWord_4538877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538877).length < 2 ^ (prefixWord ++ tailWord_4538877).sum := by decide
  have hdescent : baseEnd_4538877 < baseStart_4538877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538887 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 2, 4]
def baseStart_4538887 : Nat := 118140960795 + 4538887 * 2 ^ 59
def prefixEnd_4538887 : Nat := 4983230072969 + 3 ^ 40 * 4538887 * 2
def baseEnd_4538887 : Nat := 776876889147962772479515

theorem tailTrace_4538887 : CollatzResearch.WordTrace tailWord_4538887 prefixEnd_4538887 776876889147962772479515 := by
  unfold tailWord_4538887
  simp only [CollatzResearch.WordTrace]
  refine ⟨165546809107395054029462915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110364539404930036019641943 165546809107395054029462915)
  ·
    refine ⟨248320213661092581044194373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165546809107395054029462915 248320213661092581044194373)
    ·
      refine ⟨46560040061454858945786445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248320213661092581044194373 46560040061454858945786445)
      ·
        refine ⟨17460015023045572104669917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46560040061454858945786445 17460015023045572104669917)
        ·
          refine ⟨6547505633642089539251219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17460015023045572104669917 6547505633642089539251219)
          ·
            refine ⟨9821258450463134308876829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547505633642089539251219 9821258450463134308876829)
            ·
              refine ⟨3682971918923675365828811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9821258450463134308876829 3682971918923675365828811)
              ·
                refine ⟨5524457878385513048743217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682971918923675365828811 5524457878385513048743217)
                ·
                  refine ⟨4143343408789134786557413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5524457878385513048743217 4143343408789134786557413)
                  ·
                    refine ⟨776876889147962772479515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143343408789134786557413 776876889147962772479515)
                    ·
                      rfl

theorem cell23_4538887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_4538887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538887 prefixEnd_4538887 := by exact prefixLift 4538887
  have htrace : WordTrace (prefixWord ++ tailWord_4538887) baseStart_4538887 baseEnd_4538887 := by
    simpa [prefixWord, tailWord_4538887, baseEnd_4538887] using wordTrace_append hprefix tailTrace_4538887
  have hstable : (prefixWord ++ tailWord_4538887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538887).length < 2 ^ (prefixWord ++ tailWord_4538887).sum := by decide
  have hdescent : baseEnd_4538887 < baseStart_4538887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538900 : List Nat := [2, 4, 3, 1, 1, 1, 4, 7]
def baseStart_4538900 : Nat := 118140960795 + 4538900 * 2 ^ 59
def prefixEnd_4538900 : Nat := 4983230072969 + 3 ^ 40 * 4538900 * 2
def baseEnd_4538900 : Nat := 86319901581199880243555

theorem tailTrace_4538900 : CollatzResearch.WordTrace tailWord_4538900 prefixEnd_4538900 86319901581199880243555 := by
  unfold tailWord_4538900
  simp only [CollatzResearch.WordTrace]
  refine ⟨82773641628173978624843077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110364855504231971499790769 82773641628173978624843077)
  ·
    refine ⟨15520057805282620992158077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82773641628173978624843077 15520057805282620992158077)
    ·
      refine ⟨5820021676980982872059279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15520057805282620992158077 5820021676980982872059279)
      ·
        refine ⟨8730032515471474308088919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820021676980982872059279 8730032515471474308088919)
        ·
          refine ⟨13095048773207211462133379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730032515471474308088919 13095048773207211462133379)
          ·
            refine ⟨19642573159810817193200069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13095048773207211462133379 19642573159810817193200069)
            ·
              refine ⟨3682982467464528223725013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19642573159810817193200069 3682982467464528223725013)
              ·
                refine ⟨86319901581199880243555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3682982467464528223725013 86319901581199880243555)
                ·
                  rfl

theorem cell23_4538900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 7].length) (baseStart_4538900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538900 prefixEnd_4538900 := by exact prefixLift 4538900
  have htrace : WordTrace (prefixWord ++ tailWord_4538900) baseStart_4538900 baseEnd_4538900 := by
    simpa [prefixWord, tailWord_4538900, baseEnd_4538900] using wordTrace_append hprefix tailTrace_4538900
  have hstable : (prefixWord ++ tailWord_4538900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538900).length < 2 ^ (prefixWord ++ tailWord_4538900).sum := by decide
  have hdescent : baseEnd_4538900 < baseStart_4538900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538906 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4538906 : Nat := 118140960795 + 4538906 * 2 ^ 59
def prefixEnd_4538906 : Nat := 4983230072969 + 3 ^ 40 * 4538906 * 2
def baseEnd_4538906 : Nat := 2330640423576323743100957

theorem tailTrace_4538906 : CollatzResearch.WordTrace tailWord_4538906 prefixEnd_4538906 2330640423576323743100957 := by
  unfold tailWord_4538906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41386875523581555068601143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110365001396217480182936381 41386875523581555068601143)
  ·
    refine ⟨62080313285372332602901715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41386875523581555068601143 62080313285372332602901715)
    ·
      refine ⟨93120469928058498904352573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62080313285372332602901715 93120469928058498904352573)
      ·
        refine ⟨34920176223021937089132215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93120469928058498904352573 34920176223021937089132215)
        ·
          refine ⟨52380264334532905633698323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34920176223021937089132215 52380264334532905633698323)
          ·
            refine ⟨78570396501799358450547485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52380264334532905633698323 78570396501799358450547485)
            ·
              refine ⟨29463898688174759418955307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78570396501799358450547485 29463898688174759418955307)
              ·
                refine ⟨44195848032262139128432961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29463898688174759418955307 44195848032262139128432961)
                ·
                  refine ⟨33146886024196604346324721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44195848032262139128432961 33146886024196604346324721)
                  ·
                    refine ⟨24860164518147453259743541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33146886024196604346324721 24860164518147453259743541)
                    ·
                      refine ⟨2330640423576323743100957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24860164518147453259743541 2330640423576323743100957)
                      ·
                        rfl

theorem cell23_4538906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4538906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538906 prefixEnd_4538906 := by exact prefixLift 4538906
  have htrace : WordTrace (prefixWord ++ tailWord_4538906) baseStart_4538906 baseEnd_4538906 := by
    simpa [prefixWord, tailWord_4538906, baseEnd_4538906] using wordTrace_append hprefix tailTrace_4538906
  have hstable : (prefixWord ++ tailWord_4538906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538906).length < 2 ^ (prefixWord ++ tailWord_4538906).sum := by decide
  have hdescent : baseEnd_4538906 < baseStart_4538906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538936 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_4538936 : Nat := 118140960795 + 4538936 * 2 ^ 59
def prefixEnd_4538936 : Nat := 4983230072969 + 3 ^ 40 * 4538936 * 2
def baseEnd_4538936 : Nat := 2330655827995958625725819

theorem tailTrace_4538936 : CollatzResearch.WordTrace tailWord_4538936 prefixEnd_4538936 2330655827995958625725819 := by
  unfold tailWord_4538936
  simp only [CollatzResearch.WordTrace]
  refine ⟨82774298142108767698998331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110365730856145023598664441 82774298142108767698998331)
  ·
    refine ⟨124161447213163151548497497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82774298142108767698998331 124161447213163151548497497)
    ·
      refine ⟨93121085409872363661373123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124161447213163151548497497 93121085409872363661373123)
      ·
        refine ⟨139681628114808545492059685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93121085409872363661373123 139681628114808545492059685)
        ·
          refine ⟨26190305271526602279761191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139681628114808545492059685 26190305271526602279761191)
          ·
            refine ⟨39285457907289903419641787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26190305271526602279761191 39285457907289903419641787)
            ·
              refine ⟨58928186860934855129462681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39285457907289903419641787 58928186860934855129462681)
              ·
                refine ⟨44196140145701141347097011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58928186860934855129462681 44196140145701141347097011)
                ·
                  refine ⟨66294210218551712020645517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44196140145701141347097011 66294210218551712020645517)
                  ·
                    refine ⟨24860328831956892007742069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66294210218551712020645517 24860328831956892007742069)
                    ·
                      refine ⟨2330655827995958625725819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24860328831956892007742069 2330655827995958625725819)
                      ·
                        rfl

theorem cell23_4538936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_4538936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538936 prefixEnd_4538936 := by exact prefixLift 4538936
  have htrace : WordTrace (prefixWord ++ tailWord_4538936) baseStart_4538936 baseEnd_4538936 := by
    simpa [prefixWord, tailWord_4538936, baseEnd_4538936] using wordTrace_append hprefix tailTrace_4538936
  have hstable : (prefixWord ++ tailWord_4538936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538936).length < 2 ^ (prefixWord ++ tailWord_4538936).sum := by decide
  have hdescent : baseEnd_4538936 < baseStart_4538936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538948 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4538948 : Nat := 118140960795 + 4538948 * 2 ^ 59
def prefixEnd_4538948 : Nat := 4983230072969 + 3 ^ 40 * 4538948 * 2
def baseEnd_4538948 : Nat := 2330661989763812578775765

theorem tailTrace_4538948 : CollatzResearch.WordTrace tailWord_4538948 prefixEnd_4538948 2330661989763812578775765 := by
  unfold tailWord_4538948
  simp only [CollatzResearch.WordTrace]
  refine ⟨82774516980087030723716749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110366022640116040964955665 82774516980087030723716749)
  ·
    refine ⟨31040443867532636521393781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82774516980087030723716749 31040443867532636521393781)
    ·
      refine ⟨2910041612581184673880667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31040443867532636521393781 2910041612581184673880667)
      ·
        refine ⟨4365062418871777010821001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910041612581184673880667 4365062418871777010821001)
        ·
          refine ⟨3273796814153832758115751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365062418871777010821001 3273796814153832758115751)
          ·
            refine ⟨4910695221230749137173627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273796814153832758115751 4910695221230749137173627)
            ·
              refine ⟨7366042831846123705760441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910695221230749137173627 7366042831846123705760441)
              ·
                refine ⟨5524532123884592779320331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7366042831846123705760441 5524532123884592779320331)
                ·
                  refine ⟨8286798185826889168980497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524532123884592779320331 8286798185826889168980497)
                  ·
                    refine ⟨6215098639370166876735373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8286798185826889168980497 6215098639370166876735373)
                    ·
                      refine ⟨2330661989763812578775765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6215098639370166876735373 2330661989763812578775765)
                      ·
                        rfl

theorem cell23_4538948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4538948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538948 prefixEnd_4538948 := by exact prefixLift 4538948
  have htrace : WordTrace (prefixWord ++ tailWord_4538948) baseStart_4538948 baseEnd_4538948 := by
    simpa [prefixWord, tailWord_4538948, baseEnd_4538948] using wordTrace_append hprefix tailTrace_4538948
  have hstable : (prefixWord ++ tailWord_4538948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538948).length < 2 ^ (prefixWord ++ tailWord_4538948).sum := by decide
  have hdescent : baseEnd_4538948 < baseStart_4538948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538956 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 9]
def baseStart_4538956 : Nat := 118140960795 + 4538956 * 2 ^ 59
def prefixEnd_4538956 : Nat := 4983230072969 + 3 ^ 40 * 4538956 * 2
def baseEnd_4538956 : Nat := 258962899734338727497303

theorem tailTrace_4538956 : CollatzResearch.WordTrace tailWord_4538956 prefixEnd_4538956 258962899734338727497303 := by
  unfold tailWord_4538956
  simp only [CollatzResearch.WordTrace]
  refine ⟨82774662872072539406862361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110366217162763385875816481 82774662872072539406862361)
  ·
    refine ⟨62080997154054404555146771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82774662872072539406862361 62080997154054404555146771)
    ·
      refine ⟨93121495731081606832720157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62080997154054404555146771 93121495731081606832720157)
      ·
        refine ⟨34920560899155602562270059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93121495731081606832720157 34920560899155602562270059)
        ·
          refine ⟨52380841348733403843405089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34920560899155602562270059 52380841348733403843405089)
          ·
            refine ⟨39285631011550052882553817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52380841348733403843405089 39285631011550052882553817)
            ·
              refine ⟨29464223258662539661915363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39285631011550052882553817 29464223258662539661915363)
              ·
                refine ⟨44196334887993809492873045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29464223258662539661915363 44196334887993809492873045)
                ·
                  refine ⟨258962899734338727497303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44196334887993809492873045 258962899734338727497303)
                  ·
                    rfl

theorem cell23_4538956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_4538956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538956 prefixEnd_4538956 := by exact prefixLift 4538956
  have htrace : WordTrace (prefixWord ++ tailWord_4538956) baseStart_4538956 baseEnd_4538956 := by
    simpa [prefixWord, tailWord_4538956, baseEnd_4538956] using wordTrace_append hprefix tailTrace_4538956
  have hstable : (prefixWord ++ tailWord_4538956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538956).length < 2 ^ (prefixWord ++ tailWord_4538956).sum := by decide
  have hdescent : baseEnd_4538956 < baseStart_4538956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538983 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_4538983 : Nat := 118140960795 + 4538983 * 2 ^ 59
def prefixEnd_4538983 : Nat := 4983230072969 + 3 ^ 40 * 4538983 * 2
def baseEnd_4538983 : Nat := 2330679961586719941838103

theorem tailTrace_4538983 : CollatzResearch.WordTrace tailWord_4538983 prefixEnd_4538983 2330679961586719941838103 := by
  unfold tailWord_4538983
  simp only [CollatzResearch.WordTrace]
  refine ⟨165550310515047262424957603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110366873676698174949971735 165550310515047262424957603)
  ·
    refine ⟨248325465772570893637436405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165550310515047262424957603 248325465772570893637436405)
    ·
      refine ⟨23280512416178521278509663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 248325465772570893637436405 23280512416178521278509663)
      ·
        refine ⟨34920768624267781917764495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23280512416178521278509663 34920768624267781917764495)
        ·
          refine ⟨52381152936401672876646743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34920768624267781917764495 52381152936401672876646743)
          ·
            refine ⟨78571729404602509314970115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52381152936401672876646743 78571729404602509314970115)
            ·
              refine ⟨117857594106903763972455173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78571729404602509314970115 117857594106903763972455173)
              ·
                refine ⟨22098298895044455744835345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117857594106903763972455173 22098298895044455744835345)
                ·
                  refine ⟨16573724171283341808626509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22098298895044455744835345 16573724171283341808626509)
                  ·
                    refine ⟨6215146564231253178234941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16573724171283341808626509 6215146564231253178234941)
                    ·
                      refine ⟨2330679961586719941838103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6215146564231253178234941 2330679961586719941838103)
                      ·
                        rfl

theorem cell23_4538983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_4538983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4538983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4538983 prefixEnd_4538983 := by exact prefixLift 4538983
  have htrace : WordTrace (prefixWord ++ tailWord_4538983) baseStart_4538983 baseEnd_4538983 := by
    simpa [prefixWord, tailWord_4538983, baseEnd_4538983] using wordTrace_append hprefix tailTrace_4538983
  have hstable : (prefixWord ++ tailWord_4538983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538983).length < 2 ^ (prefixWord ++ tailWord_4538983).sum := by decide
  have hdescent : baseEnd_4538983 < baseStart_4538983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539033 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_4539033 : Nat := 118140960795 + 4539033 * 2 ^ 59
def prefixEnd_4539033 : Nat := 4983230072969 + 3 ^ 40 * 4539033 * 2
def baseEnd_4539033 : Nat := 776901878539814915404291

theorem tailTrace_4539033 : CollatzResearch.WordTrace tailWord_4539033 prefixEnd_4539033 776901878539814915404291 := by
  unfold tailWord_4539033
  simp only [CollatzResearch.WordTrace]
  refine ⟨165552134164866120964277753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110368089443244080642851835 165552134164866120964277753)
  ·
    refine ⟨124164100623649590723208315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165552134164866120964277753 124164100623649590723208315)
    ·
      refine ⟨186246150935474386084812473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124164100623649590723208315 186246150935474386084812473)
      ·
        refine ⟨139684613201605789563609355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186246150935474386084812473 139684613201605789563609355)
        ·
          refine ⟨209526919802408684345414033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139684613201605789563609355 209526919802408684345414033)
          ·
            refine ⟨157145189851806513259060525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209526919802408684345414033 157145189851806513259060525)
            ·
              refine ⟨58929446194427442472147697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157145189851806513259060525 58929446194427442472147697)
              ·
                refine ⟨44197084645820581854110773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58929446194427442472147697 44197084645820581854110773)
                ·
                  refine ⟨4143476685545679548822885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44197084645820581854110773 4143476685545679548822885)
                  ·
                    refine ⟨776901878539814915404291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143476685545679548822885 776901878539814915404291)
                    ·
                      rfl

theorem cell23_4539033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_4539033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539033 prefixEnd_4539033 := by exact prefixLift 4539033
  have htrace : WordTrace (prefixWord ++ tailWord_4539033) baseStart_4539033 baseEnd_4539033 := by
    simpa [prefixWord, tailWord_4539033, baseEnd_4539033] using wordTrace_append hprefix tailTrace_4539033
  have hstable : (prefixWord ++ tailWord_4539033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539033).length < 2 ^ (prefixWord ++ tailWord_4539033).sum := by decide
  have hdescent : baseEnd_4539033 < baseStart_4539033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539084 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_4539084 : Nat := 118140960795 + 4539084 * 2 ^ 59
def prefixEnd_4539084 : Nat := 4983230072969 + 3 ^ 40 * 4539084 * 2
def baseEnd_4539084 : Nat := 776910607710941348891713

theorem tailTrace_4539084 : CollatzResearch.WordTrace tailWord_4539084 prefixEnd_4539084 776910607710941348891713 := by
  unfold tailWord_4539084
  simp only [CollatzResearch.WordTrace]
  refine ⟨82776997143840678337192153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110369329525120904449589537 82776997143840678337192153)
  ·
    refine ⟨62082747857880508752894115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82776997143840678337192153 62082747857880508752894115)
    ·
      refine ⟨93124121786820763129341173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62082747857880508752894115 93124121786820763129341173)
      ·
        refine ⟨8730386417514446543375735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93124121786820763129341173 8730386417514446543375735)
        ·
          refine ⟨13095579626271669815063603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730386417514446543375735 13095579626271669815063603)
          ·
            refine ⟨19643369439407504722595405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13095579626271669815063603 19643369439407504722595405)
            ·
              refine ⟨7366263539777814270973277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19643369439407504722595405 7366263539777814270973277)
              ·
                refine ⟨2762348827416680351614979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7366263539777814270973277 2762348827416680351614979)
                ·
                  refine ⟨4143523241125020527422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762348827416680351614979 4143523241125020527422469)
                  ·
                    refine ⟨776910607710941348891713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143523241125020527422469 776910607710941348891713)
                    ·
                      rfl

theorem cell23_4539084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_4539084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539084 prefixEnd_4539084 := by exact prefixLift 4539084
  have htrace : WordTrace (prefixWord ++ tailWord_4539084) baseStart_4539084 baseEnd_4539084 := by
    simpa [prefixWord, tailWord_4539084, baseEnd_4539084] using wordTrace_append hprefix tailTrace_4539084
  have hstable : (prefixWord ++ tailWord_4539084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539084).length < 2 ^ (prefixWord ++ tailWord_4539084).sum := by decide
  have hdescent : baseEnd_4539084 < baseStart_4539084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539117 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4539117 : Nat := 118140960795 + 4539117 * 2 ^ 59
def prefixEnd_4539117 : Nat := 4983230072969 + 3 ^ 40 * 4539117 * 2
def baseEnd_4539117 : Nat := 2330748767994422417562487

theorem tailTrace_4539117 : CollatzResearch.WordTrace tailWord_4539117 prefixEnd_4539117 2330748767994422417562487 := by
  unfold tailWord_4539117
  simp only [CollatzResearch.WordTrace]
  refine ⟨165555197896561803310335605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110370131931041202206890403 165555197896561803310335605)
  ·
    refine ⟨15520799802802669060343963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165555197896561803310335605 15520799802802669060343963)
    ·
      refine ⟨23281199704204003590515945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15520799802802669060343963 23281199704204003590515945)
      ·
        refine ⟨17460899778153002692886959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23281199704204003590515945 17460899778153002692886959)
        ·
          refine ⟨26191349667229504039330439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17460899778153002692886959 26191349667229504039330439)
          ·
            refine ⟨39287024500844256058995659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26191349667229504039330439 39287024500844256058995659)
            ·
              refine ⟨58930536751266384088493489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39287024500844256058995659 58930536751266384088493489)
              ·
                refine ⟨44197902563449788066370117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58930536751266384088493489 44197902563449788066370117)
                ·
                  refine ⟨8287106730646835262444397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44197902563449788066370117 8287106730646835262444397)
                  ·
                    refine ⟨3107665023992563223416649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8287106730646835262444397 3107665023992563223416649)
                    ·
                      refine ⟨2330748767994422417562487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107665023992563223416649 2330748767994422417562487)
                      ·
                        rfl

theorem cell23_4539117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4539117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539117 prefixEnd_4539117 := by exact prefixLift 4539117
  have htrace : WordTrace (prefixWord ++ tailWord_4539117) baseStart_4539117 baseEnd_4539117 := by
    simpa [prefixWord, tailWord_4539117, baseEnd_4539117] using wordTrace_append hprefix tailTrace_4539117
  have hstable : (prefixWord ++ tailWord_4539117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539117).length < 2 ^ (prefixWord ++ tailWord_4539117).sum := by decide
  have hdescent : baseEnd_4539117 < baseStart_4539117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539123 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 1, 6]
def baseStart_4539123 : Nat := 118140960795 + 4539123 * 2 ^ 59
def prefixEnd_4539123 : Nat := 4983230072969 + 3 ^ 40 * 4539123 * 2
def baseEnd_4539123 : Nat := 776917282959449798029153

theorem tailTrace_4539123 : CollatzResearch.WordTrace tailWord_4539123 prefixEnd_4539123 776917282959449798029153 := by
  unfold tailWord_4539123
  simp only [CollatzResearch.WordTrace]
  refine ⟨165555416734540066335054023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110370277823026710890036015 165555416734540066335054023)
  ·
    refine ⟨248333125101810099502581035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165555416734540066335054023 248333125101810099502581035)
    ·
      refine ⟨372499687652715149253871553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248333125101810099502581035 372499687652715149253871553)
      ·
        refine ⟨279374765739536361940403665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372499687652715149253871553 279374765739536361940403665)
        ·
          refine ⟨209531074304652271455302749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279374765739536361940403665 209531074304652271455302749)
          ·
            refine ⟨78574152864244601795738531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209531074304652271455302749 78574152864244601795738531)
            ·
              refine ⟨117861229296366902693607797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78574152864244601795738531 117861229296366902693607797)
              ·
                refine ⟨11049490246534397127525731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117861229296366902693607797 11049490246534397127525731)
                ·
                  refine ⟨16574235369801595691288597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11049490246534397127525731 16574235369801595691288597)
                  ·
                    refine ⟨776917282959449798029153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16574235369801595691288597 776917282959449798029153)
                    ·
                      rfl

theorem cell23_4539123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 6].length) (baseStart_4539123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539123 prefixEnd_4539123 := by exact prefixLift 4539123
  have htrace : WordTrace (prefixWord ++ tailWord_4539123) baseStart_4539123 baseEnd_4539123 := by
    simpa [prefixWord, tailWord_4539123, baseEnd_4539123] using wordTrace_append hprefix tailTrace_4539123
  have hstable : (prefixWord ++ tailWord_4539123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539123).length < 2 ^ (prefixWord ++ tailWord_4539123).sum := by decide
  have hdescent : baseEnd_4539123 < baseStart_4539123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539130 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_4539130 : Nat := 118140960795 + 4539130 * 2 ^ 59
def prefixEnd_4539130 : Nat := 4983230072969 + 3 ^ 40 * 4539130 * 2
def baseEnd_4539130 : Nat := 2330755443242930866699927

theorem tailTrace_4539130 : CollatzResearch.WordTrace tailWord_4539130 prefixEnd_4539130 2330755443242930866699927 := by
  unfold tailWord_4539130
  simp only [CollatzResearch.WordTrace]
  refine ⟨41388918011378676632639711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110370448030343137687039229 41388918011378676632639711)
  ·
    refine ⟨62083377017068014948959567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41388918011378676632639711 62083377017068014948959567)
    ·
      refine ⟨93125065525602022423439351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62083377017068014948959567 93125065525602022423439351)
      ·
        refine ⟨139687598288403033635159027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93125065525602022423439351 139687598288403033635159027)
        ·
          refine ⟨209531397432604550452738541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139687598288403033635159027 209531397432604550452738541)
          ·
            refine ⟨78574274037226706419776953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209531397432604550452738541 78574274037226706419776953)
            ·
              refine ⟨58930705527920029814832715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78574274037226706419776953 58930705527920029814832715)
              ·
                refine ⟨88396058291880044722249073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58930705527920029814832715 88396058291880044722249073)
                ·
                  refine ⟨66297043718910033541686805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88396058291880044722249073 66297043718910033541686805)
                  ·
                    refine ⟨3107673924323907822266569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66297043718910033541686805 3107673924323907822266569)
                    ·
                      refine ⟨2330755443242930866699927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107673924323907822266569 2330755443242930866699927)
                      ·
                        rfl

theorem cell23_4539130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_4539130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539130 prefixEnd_4539130 := by exact prefixLift 4539130
  have htrace : WordTrace (prefixWord ++ tailWord_4539130) baseStart_4539130 baseEnd_4539130 := by
    simpa [prefixWord, tailWord_4539130, baseEnd_4539130] using wordTrace_append hprefix tailTrace_4539130
  have hstable : (prefixWord ++ tailWord_4539130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539130).length < 2 ^ (prefixWord ++ tailWord_4539130).sum := by decide
  have hdescent : baseEnd_4539130 < baseStart_4539130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539134 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4539134 : Nat := 118140960795 + 4539134 * 2 ^ 59
def prefixEnd_4539134 : Nat := 4983230072969 + 3 ^ 40 * 4539134 * 2
def baseEnd_4539134 : Nat := 2330757497165548851049909

theorem tailTrace_4539134 : CollatzResearch.WordTrace tailWord_4539134 prefixEnd_4539134 2330757497165548851049909 := by
  unfold tailWord_4539134
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694477242187526901713057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110370545291666810142469637 20694477242187526901713057)
  ·
    refine ⟨15520857931640645176284793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20694477242187526901713057 15520857931640645176284793)
    ·
      refine ⟨11640643448730483882213595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15520857931640645176284793 11640643448730483882213595)
      ·
        refine ⟨17460965173095725823320393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11640643448730483882213595 17460965173095725823320393)
        ·
          refine ⟨13095723879821794367490295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17460965173095725823320393 13095723879821794367490295)
          ·
            refine ⟨19643585819732691551235443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13095723879821794367490295 19643585819732691551235443)
            ·
              refine ⟨29465378729599037326853165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19643585819732691551235443 29465378729599037326853165)
              ·
                refine ⟨11049517023599638997569937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29465378729599037326853165 11049517023599638997569937)
                ·
                  refine ⟨8287137767699729248177453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11049517023599638997569937 8287137767699729248177453)
                  ·
                    refine ⟨3107676662887398468066545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8287137767699729248177453 3107676662887398468066545)
                    ·
                      refine ⟨2330757497165548851049909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107676662887398468066545 2330757497165548851049909)
                      ·
                        rfl

theorem cell23_4539134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4539134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539134 prefixEnd_4539134 := by exact prefixLift 4539134
  have htrace : WordTrace (prefixWord ++ tailWord_4539134) baseStart_4539134 baseEnd_4539134 := by
    simpa [prefixWord, tailWord_4539134, baseEnd_4539134] using wordTrace_append hprefix tailTrace_4539134
  have hstable : (prefixWord ++ tailWord_4539134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539134).length < 2 ^ (prefixWord ++ tailWord_4539134).sum := by decide
  have hdescent : baseEnd_4539134 < baseStart_4539134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539140 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_4539140 : Nat := 118140960795 + 4539140 * 2 ^ 59
def prefixEnd_4539140 : Nat := 4983230072969 + 3 ^ 40 * 4539140 * 2
def baseEnd_4539140 : Nat := 776920192683158609191627

theorem tailTrace_4539140 : CollatzResearch.WordTrace tailWord_4539140 prefixEnd_4539140 776920192683158609191627 := by
  unfold tailWord_4539140
  simp only [CollatzResearch.WordTrace]
  refine ⟨82778018387739239119211437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110370691183652318825615249 82778018387739239119211437)
  ·
    refine ⟨31041756895402214669704289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82778018387739239119211437 31041756895402214669704289)
    ·
      refine ⟨23281317671551661002278217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31041756895402214669704289 23281317671551661002278217)
      ·
        refine ⟨17460988253663745751708663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23281317671551661002278217 17460988253663745751708663)
        ·
          refine ⟨26191482380495618627562995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17460988253663745751708663 26191482380495618627562995)
          ·
            refine ⟨39287223570743427941344493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26191482380495618627562995 39287223570743427941344493)
            ·
              refine ⟨14732708839028785478004185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39287223570743427941344493 14732708839028785478004185)
              ·
                refine ⟨11049531629271589108503139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14732708839028785478004185 11049531629271589108503139)
                ·
                  refine ⟨16574297443907383662754709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11049531629271589108503139 16574297443907383662754709)
                  ·
                    refine ⟨776920192683158609191627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16574297443907383662754709 776920192683158609191627)
                    ·
                      rfl

theorem cell23_4539140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4539140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539140 prefixEnd_4539140 := by exact prefixLift 4539140
  have htrace : WordTrace (prefixWord ++ tailWord_4539140) baseStart_4539140 baseEnd_4539140 := by
    simpa [prefixWord, tailWord_4539140, baseEnd_4539140] using wordTrace_append hprefix tailTrace_4539140
  have hstable : (prefixWord ++ tailWord_4539140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539140).length < 2 ^ (prefixWord ++ tailWord_4539140).sum := by decide
  have hdescent : baseEnd_4539140 < baseStart_4539140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539157 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_4539157 : Nat := 118140960795 + 4539157 * 2 ^ 59
def prefixEnd_4539157 : Nat := 4983230072969 + 3 ^ 40 * 4539157 * 2
def baseEnd_4539157 : Nat := 776923102406867420354101

theorem tailTrace_4539157 : CollatzResearch.WordTrace tailWord_4539157 prefixEnd_4539157 776923102406867420354101 := by
  unfold tailWord_4539157
  simp only [CollatzResearch.WordTrace]
  refine ⟨165556656816416890141791725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110371104544277926761194483 165556656816416890141791725)
  ·
    refine ⟨62083746306156333803171897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165556656816416890141791725 62083746306156333803171897)
    ·
      refine ⟨46562809729617250352378923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62083746306156333803171897 46562809729617250352378923)
      ·
        refine ⟨69844214594425875528568385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46562809729617250352378923 69844214594425875528568385)
        ·
          refine ⟨52383160945819406646426289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69844214594425875528568385 52383160945819406646426289)
          ·
            refine ⟨39287370709364554984819717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52383160945819406646426289 39287370709364554984819717)
            ·
              refine ⟨7366382008005854059653697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39287370709364554984819717 7366382008005854059653697)
              ·
                refine ⟨5524786506004390544740273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7366382008005854059653697 5524786506004390544740273)
                ·
                  refine ⟨4143589879503292908555205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5524786506004390544740273 4143589879503292908555205)
                  ·
                    refine ⟨776923102406867420354101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143589879503292908555205 776923102406867420354101)
                    ·
                      rfl

theorem cell23_4539157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_4539157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539157 prefixEnd_4539157 := by exact prefixLift 4539157
  have htrace : WordTrace (prefixWord ++ tailWord_4539157) baseStart_4539157 baseEnd_4539157 := by
    simpa [prefixWord, tailWord_4539157, baseEnd_4539157] using wordTrace_append hprefix tailTrace_4539157
  have hstable : (prefixWord ++ tailWord_4539157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539157).length < 2 ^ (prefixWord ++ tailWord_4539157).sum := by decide
  have hdescent : baseEnd_4539157 < baseStart_4539157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539170 : List Nat := [3, 3, 1, 1, 2, 2, 3, 8]
def baseStart_4539170 : Nat := 118140960795 + 4539170 * 2 ^ 59
def prefixEnd_4539170 : Nat := 4983230072969 + 3 ^ 40 * 4539170 * 2
def baseEnd_4539170 : Nat := 86325036387744841118509

theorem tailTrace_4539170 : CollatzResearch.WordTrace tailWord_4539170 prefixEnd_4539170 86325036387744841118509 := by
  unfold tailWord_4539170
  simp only [CollatzResearch.WordTrace]
  refine ⟨41389282741342448340503741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110371420643579862241343309 41389282741342448340503741)
  ·
    refine ⟨15520981028003418127688903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41389282741342448340503741 15520981028003418127688903)
    ·
      refine ⟨23281471542005127191533355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15520981028003418127688903 23281471542005127191533355)
      ·
        refine ⟨34922207313007690787300033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23281471542005127191533355 34922207313007690787300033)
        ·
          refine ⟨26191655484755768090475025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34922207313007690787300033 26191655484755768090475025)
          ·
            refine ⟨19643741613566826067856269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26191655484755768090475025 19643741613566826067856269)
            ·
              refine ⟨7366403105087559775446101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19643741613566826067856269 7366403105087559775446101)
              ·
                refine ⟨86325036387744841118509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7366403105087559775446101 86325036387744841118509)
                ·
                  rfl

theorem cell23_4539170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_4539170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539170 prefixEnd_4539170 := by exact prefixLift 4539170
  have htrace : WordTrace (prefixWord ++ tailWord_4539170) baseStart_4539170 baseEnd_4539170 := by
    simpa [prefixWord, tailWord_4539170, baseEnd_4539170] using wordTrace_append hprefix tailTrace_4539170
  have hstable : (prefixWord ++ tailWord_4539170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539170).length < 2 ^ (prefixWord ++ tailWord_4539170).sum := by decide
  have hdescent : baseEnd_4539170 < baseStart_4539170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539198 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_4539198 : Nat := 118140960795 + 4539198 * 2 ^ 59
def prefixEnd_4539198 : Nat := 4983230072969 + 3 ^ 40 * 4539198 * 2
def baseEnd_4539198 : Nat := 2330790359927436600649615

theorem tailTrace_4539198 : CollatzResearch.WordTrace tailWord_4539198 prefixEnd_4539198 2330790359927436600649615 := by
  unfold tailWord_4539198
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694769026158544268004281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110372101472845569429356165 20694769026158544268004281)
  ·
    refine ⟨15521076769618908201003211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20694769026158544268004281 15521076769618908201003211)
    ·
      refine ⟨23281615154428362301504817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15521076769618908201003211 23281615154428362301504817)
      ·
        refine ⟨17461211365821271726128613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23281615154428362301504817 17461211365821271726128613)
        ·
          refine ⟨3273977131091488448649115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17461211365821271726128613 3273977131091488448649115)
          ·
            refine ⟨4910965696637232672973673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273977131091488448649115 4910965696637232672973673)
            ·
              refine ⟨3683224272477924504730255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4910965696637232672973673 3683224272477924504730255)
              ·
                refine ⟨5524836408716886757095383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683224272477924504730255 5524836408716886757095383)
                ·
                  refine ⟨8287254613075330135643075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524836408716886757095383 8287254613075330135643075)
                  ·
                    refine ⟨12430881919612995203464613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8287254613075330135643075 12430881919612995203464613)
                    ·
                      refine ⟨2330790359927436600649615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12430881919612995203464613 2330790359927436600649615)
                      ·
                        rfl

theorem cell23_4539198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_4539198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539198 prefixEnd_4539198 := by exact prefixLift 4539198
  have htrace : WordTrace (prefixWord ++ tailWord_4539198) baseStart_4539198 baseEnd_4539198 := by
    simpa [prefixWord, tailWord_4539198, baseEnd_4539198] using wordTrace_append hprefix tailTrace_4539198
  have hstable : (prefixWord ++ tailWord_4539198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539198).length < 2 ^ (prefixWord ++ tailWord_4539198).sum := by decide
  have hdescent : baseEnd_4539198 < baseStart_4539198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539201 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4539201 : Nat := 118140960795 + 4539201 * 2 ^ 59
def prefixEnd_4539201 : Nat := 4983230072969 + 3 ^ 40 * 4539201 * 2
def baseEnd_4539201 : Nat := 2330791900369400088912101

theorem tailTrace_4539201 : CollatzResearch.WordTrace tailWord_4539201 prefixEnd_4539201 2330791900369400088912101 := by
  unfold tailWord_4539201
  simp only [CollatzResearch.WordTrace]
  refine ⟨165558261628257485656393457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110372174418838323770928971 165558261628257485656393457)
  ·
    refine ⟨124168696221193114242295093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165558261628257485656393457 124168696221193114242295093)
    ·
      refine ⟨11640815270736854460215165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124168696221193114242295093 11640815270736854460215165)
      ·
        refine ⟨4365305726526320422580687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11640815270736854460215165 4365305726526320422580687)
        ·
          refine ⟨6547958589789480633871031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365305726526320422580687 6547958589789480633871031)
          ·
            refine ⟨9821937884684220950806547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547958589789480633871031 9821937884684220950806547)
            ·
              refine ⟨14732906827026331426209821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9821937884684220950806547 14732906827026331426209821)
              ·
                refine ⟨5524840060134874284828683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14732906827026331426209821 5524840060134874284828683)
                ·
                  refine ⟨8287260090202311427243025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524840060134874284828683 8287260090202311427243025)
                  ·
                    refine ⟨6215445067651733570432269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8287260090202311427243025 6215445067651733570432269)
                    ·
                      refine ⟨2330791900369400088912101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6215445067651733570432269 2330791900369400088912101)
                      ·
                        rfl

theorem cell23_4539201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4539201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539201 prefixEnd_4539201 := by exact prefixLift 4539201
  have htrace : WordTrace (prefixWord ++ tailWord_4539201) baseStart_4539201 baseEnd_4539201 := by
    simpa [prefixWord, tailWord_4539201, baseEnd_4539201] using wordTrace_append hprefix tailTrace_4539201
  have hstable : (prefixWord ++ tailWord_4539201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539201).length < 2 ^ (prefixWord ++ tailWord_4539201).sum := by decide
  have hdescent : baseEnd_4539201 < baseStart_4539201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539250 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4539250 : Nat := 118140960795 + 4539250 * 2 ^ 59
def prefixEnd_4539250 : Nat := 4983230072969 + 3 ^ 40 * 4539250 * 2
def baseEnd_4539250 : Nat := 2330817060921470397199375

theorem tailTrace_4539250 : CollatzResearch.WordTrace tailWord_4539250 prefixEnd_4539250 2330817060921470397199375 := by
  unfold tailWord_4539250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41390012201269991756231801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110373365870053311349951469 41390012201269991756231801)
  ·
    refine ⟨31042509150952493817173851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41390012201269991756231801 31042509150952493817173851)
    ·
      refine ⟨46563763726428740725760777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31042509150952493817173851 46563763726428740725760777)
      ·
        refine ⟨34922822794821555544320583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46563763726428740725760777 34922822794821555544320583)
        ·
          refine ⟨52384234192232333316480875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34922822794821555544320583 52384234192232333316480875)
          ·
            refine ⟨78576351288348499974721313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52384234192232333316480875 78576351288348499974721313)
            ·
              refine ⟨58932263466261374981040985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78576351288348499974721313 58932263466261374981040985)
              ·
                refine ⟨44199197599696031235780739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58932263466261374981040985 44199197599696031235780739)
                ·
                  refine ⟨66298796399544046853671109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44199197599696031235780739 66298796399544046853671109)
                  ·
                    refine ⟨12431024324914508785063333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66298796399544046853671109 12431024324914508785063333)
                    ·
                      refine ⟨2330817060921470397199375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12431024324914508785063333 2330817060921470397199375)
                      ·
                        rfl

theorem cell23_4539250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4539250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539250 prefixEnd_4539250 := by exact prefixLift 4539250
  have htrace : WordTrace (prefixWord ++ tailWord_4539250) baseStart_4539250 baseEnd_4539250 := by
    simpa [prefixWord, tailWord_4539250, baseEnd_4539250] using wordTrace_append hprefix tailTrace_4539250
  have hstable : (prefixWord ++ tailWord_4539250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539250).length < 2 ^ (prefixWord ++ tailWord_4539250).sum := by decide
  have hdescent : baseEnd_4539250 < baseStart_4539250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539300 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_4539300 : Nat := 118140960795 + 4539300 * 2 ^ 59
def prefixEnd_4539300 : Nat := 4983230072969 + 3 ^ 40 * 4539300 * 2
def baseEnd_4539300 : Nat := 2330842734954195201574145

theorem tailTrace_4539300 : CollatzResearch.WordTrace tailWord_4539300 prefixEnd_4539300 2330842734954195201574145 := by
  unfold tailWord_4539300
  simp only [CollatzResearch.WordTrace]
  refine ⟨82780936227449412782123677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110374581636599217042831569 82780936227449412782123677)
  ·
    refine ⟨31042851085293529793296379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82780936227449412782123677 31042851085293529793296379)
    ·
      refine ⟨46564276627940294689944569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31042851085293529793296379 46564276627940294689944569)
      ·
        refine ⟨34923207470955221017458427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46564276627940294689944569 34923207470955221017458427)
        ·
          refine ⟨52384811206432831526187641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34923207470955221017458427 52384811206432831526187641)
          ·
            refine ⟨39288608404824623644640731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52384811206432831526187641 39288608404824623644640731)
            ·
              refine ⟨58932912607236935466961097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39288608404824623644640731 58932912607236935466961097)
              ·
                refine ⟨44199684455427701600220823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58932912607236935466961097 44199684455427701600220823)
                ·
                  refine ⟨66299526683141552400331235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44199684455427701600220823 66299526683141552400331235)
                  ·
                    refine ⟨99449290024712328600496853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66299526683141552400331235 99449290024712328600496853)
                    ·
                      refine ⟨2330842734954195201574145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99449290024712328600496853 2330842734954195201574145)
                      ·
                        rfl

theorem cell23_4539300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_4539300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539300 prefixEnd_4539300 := by exact prefixLift 4539300
  have htrace : WordTrace (prefixWord ++ tailWord_4539300) baseStart_4539300 baseEnd_4539300 := by
    simpa [prefixWord, tailWord_4539300, baseEnd_4539300] using wordTrace_append hprefix tailTrace_4539300
  have hstable : (prefixWord ++ tailWord_4539300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539300).length < 2 ^ (prefixWord ++ tailWord_4539300).sum := by decide
  have hdescent : baseEnd_4539300 < baseStart_4539300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539354 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_4539354 : Nat := 118140960795 + 4539354 * 2 ^ 59
def prefixEnd_4539354 : Nat := 4983230072969 + 3 ^ 40 * 4539354 * 2
def baseEnd_4539354 : Nat := 776956820969845996766299

theorem tailTrace_4539354 : CollatzResearch.WordTrace tailWord_4539354 prefixEnd_4539354 776956820969845996766299 := by
  unfold tailWord_4539354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41390960499175798196678279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110375894664468795191142077 41390960499175798196678279)
  ·
    refine ⟨62086440748763697295017419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41390960499175798196678279 62086440748763697295017419)
    ·
      refine ⟨93129661123145545942526129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62086440748763697295017419 93129661123145545942526129)
      ·
        refine ⟨69847245842359159456894597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93129661123145545942526129 69847245842359159456894597)
        ·
          refine ⟨13096358595442342398167737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69847245842359159456894597 13096358595442342398167737)
          ·
            refine ⟨9822268946581756798625803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13096358595442342398167737 9822268946581756798625803)
            ·
              refine ⟨14733403419872635197938705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9822268946581756798625803 14733403419872635197938705)
              ·
                refine ⟨11050052564904476398454029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14733403419872635197938705 11050052564904476398454029)
                ·
                  refine ⟨4143769711839178649420261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11050052564904476398454029 4143769711839178649420261)
                  ·
                    refine ⟨776956820969845996766299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143769711839178649420261 776956820969845996766299)
                    ·
                      rfl

theorem cell23_4539354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_4539354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539354 prefixEnd_4539354 := by exact prefixLift 4539354
  have htrace : WordTrace (prefixWord ++ tailWord_4539354) baseStart_4539354 baseEnd_4539354 := by
    simpa [prefixWord, tailWord_4539354, baseEnd_4539354] using wordTrace_append hprefix tailTrace_4539354
  have hstable : (prefixWord ++ tailWord_4539354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539354).length < 2 ^ (prefixWord ++ tailWord_4539354).sum := by decide
  have hdescent : baseEnd_4539354 < baseStart_4539354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539404 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_4539404 : Nat := 118140960795 + 4539404 * 2 ^ 59
def prefixEnd_4539404 : Nat := 4983230072969 + 3 ^ 40 * 4539404 * 2
def baseEnd_4539404 : Nat := 2330896136942262794673667

theorem tailTrace_4539404 : CollatzResearch.WordTrace tailWord_4539404 prefixEnd_4539404 2330896136942262794673667 := by
  unfold tailWord_4539404
  simp only [CollatzResearch.WordTrace]
  refine ⟨82782832823261025663016633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110377110431014700884022177 82782832823261025663016633)
  ·
    refine ⟨62087124617445769247262475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82782832823261025663016633 62087124617445769247262475)
    ·
      refine ⟨93130686926168653870893713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62087124617445769247262475 93130686926168653870893713)
      ·
        refine ⟨69848015194626490403170285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93130686926168653870893713 69848015194626490403170285)
        ·
          refine ⟨26193005697984933901188857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69848015194626490403170285 26193005697984933901188857)
          ·
            refine ⟨19644754273488700425891643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26193005697984933901188857 19644754273488700425891643)
            ·
              refine ⟨29467131410233050638837465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19644754273488700425891643 29467131410233050638837465)
              ·
                refine ⟨22100348557674787979128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29467131410233050638837465 22100348557674787979128099)
                ·
                  refine ⟨33150522836512181968692149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22100348557674787979128099 33150522836512181968692149)
                  ·
                    refine ⟨3107861515923017059564889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33150522836512181968692149 3107861515923017059564889)
                    ·
                      refine ⟨2330896136942262794673667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107861515923017059564889 2330896136942262794673667)
                      ·
                        rfl

theorem cell23_4539404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_4539404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539404 prefixEnd_4539404 := by exact prefixLift 4539404
  have htrace : WordTrace (prefixWord ++ tailWord_4539404) baseStart_4539404 baseEnd_4539404 := by
    simpa [prefixWord, tailWord_4539404, baseEnd_4539404] using wordTrace_append hprefix tailTrace_4539404
  have hstable : (prefixWord ++ tailWord_4539404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539404).length < 2 ^ (prefixWord ++ tailWord_4539404).sum := by decide
  have hdescent : baseEnd_4539404 < baseStart_4539404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539417 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_4539417 : Nat := 118140960795 + 4539417 * 2 ^ 59
def prefixEnd_4539417 : Nat := 4983230072969 + 3 ^ 40 * 4539417 * 2
def baseEnd_4539417 : Nat := 2330902812190771243811107

theorem tailTrace_4539417 : CollatzResearch.WordTrace tailWord_4539417 prefixEnd_4539417 2330902812190771243811107 := by
  unfold tailWord_4539417
  simp only [CollatzResearch.WordTrace]
  refine ⟨165566139795474954546256505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110377426530316636364171003 165566139795474954546256505)
  ·
    refine ⟨124174604846606215909692379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165566139795474954546256505 124174604846606215909692379)
    ·
      refine ⟨186261907269909323864538569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124174604846606215909692379 186261907269909323864538569)
      ·
        refine ⟨139696430452431992898403927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186261907269909323864538569 139696430452431992898403927)
        ·
          refine ⟨209544645678647989347605891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139696430452431992898403927 209544645678647989347605891)
          ·
            refine ⟨314316968517971984021408837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209544645678647989347605891 314316968517971984021408837)
            ·
              refine ⟨58934431597119747004014157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314316968517971984021408837 58934431597119747004014157)
              ·
                refine ⟨22100411848919905126505309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58934431597119747004014157 22100411848919905126505309)
                ·
                  refine ⟨8287654443344964422439491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22100411848919905126505309 8287654443344964422439491)
                  ·
                    refine ⟨12431481665017446633659237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8287654443344964422439491 12431481665017446633659237)
                    ·
                      refine ⟨2330902812190771243811107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12431481665017446633659237 2330902812190771243811107)
                      ·
                        rfl

theorem cell23_4539417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_4539417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539417 prefixEnd_4539417 := by exact prefixLift 4539417
  have htrace : WordTrace (prefixWord ++ tailWord_4539417) baseStart_4539417 baseEnd_4539417 := by
    simpa [prefixWord, tailWord_4539417, baseEnd_4539417] using wordTrace_append hprefix tailTrace_4539417
  have hstable : (prefixWord ++ tailWord_4539417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539417).length < 2 ^ (prefixWord ++ tailWord_4539417).sum := by decide
  have hdescent : baseEnd_4539417 < baseStart_4539417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539431 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4539431 : Nat := 118140960795 + 4539431 * 2 ^ 59
def prefixEnd_4539431 : Nat := 4983230072969 + 3 ^ 40 * 4539431 * 2
def baseEnd_4539431 : Nat := 776970000306644729678681

theorem tailTrace_4539431 : CollatzResearch.WordTrace tailWord_4539431 prefixEnd_4539431 776970000306644729678681 := by
  unfold tailWord_4539431
  simp only [CollatzResearch.WordTrace]
  refine ⟨165566650417424234937266147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110377766944949489958177431 165566650417424234937266147)
  ·
    refine ⟨248349975626136352405899221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165566650417424234937266147 248349975626136352405899221)
    ·
      refine ⟨5820702553737570759513263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 248349975626136352405899221 5820702553737570759513263)
      ·
        refine ⟨8731053830606356139269895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820702553737570759513263 8731053830606356139269895)
        ·
          refine ⟨13096580745909534208904843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731053830606356139269895 13096580745909534208904843)
          ·
            refine ⟨19644871118864301313357265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13096580745909534208904843 19644871118864301313357265)
            ·
              refine ⟨14733653339148225985017949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19644871118864301313357265 14733653339148225985017949)
              ·
                refine ⟨5525120002180584744381731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14733653339148225985017949 5525120002180584744381731)
                ·
                  refine ⟨8287680003270877116572597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5525120002180584744381731 8287680003270877116572597)
                  ·
                    refine ⟨776970000306644729678681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8287680003270877116572597 776970000306644729678681)
                    ·
                      rfl

theorem cell23_4539431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4539431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539431 prefixEnd_4539431 := by exact prefixLift 4539431
  have htrace : WordTrace (prefixWord ++ tailWord_4539431) baseStart_4539431 baseEnd_4539431 := by
    simpa [prefixWord, tailWord_4539431, baseEnd_4539431] using wordTrace_append hprefix tailTrace_4539431
  have hstable : (prefixWord ++ tailWord_4539431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539431).length < 2 ^ (prefixWord ++ tailWord_4539431).sum := by decide
  have hdescent : baseEnd_4539431 < baseStart_4539431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539461 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_4539461 : Nat := 118140960795 + 4539461 * 2 ^ 59
def prefixEnd_4539461 : Nat := 4983230072969 + 3 ^ 40 * 4539461 * 2
def baseEnd_4539461 : Nat := 776975135113189690553635

theorem tailTrace_4539461 : CollatzResearch.WordTrace tailWord_4539461 prefixEnd_4539461 776975135113189690553635 := by
  unfold tailWord_4539461
  simp only [CollatzResearch.WordTrace]
  refine ⟨165567744607315550060858237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110378496404877033373905491 165567744607315550060858237)
  ·
    refine ⟨62087904227743331272821839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165567744607315550060858237 62087904227743331272821839)
    ·
      refine ⟨93131856341614996909232759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62087904227743331272821839 93131856341614996909232759)
      ·
        refine ⟨139697784512422495363849139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93131856341614996909232759 139697784512422495363849139)
        ·
          refine ⟨209546676768633743045773709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139697784512422495363849139 209546676768633743045773709)
          ·
            refine ⟨78580003788237653642165141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209546676768633743045773709 78580003788237653642165141)
            ·
              refine ⟨3683437677573640014476491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78580003788237653642165141 3683437677573640014476491)
              ·
                refine ⟨5525156516360460021714737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683437677573640014476491 5525156516360460021714737)
                ·
                  refine ⟨4143867387270345016286053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5525156516360460021714737 4143867387270345016286053)
                  ·
                    refine ⟨776975135113189690553635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143867387270345016286053 776975135113189690553635)
                    ·
                      rfl

theorem cell23_4539461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_4539461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539461 prefixEnd_4539461 := by exact prefixLift 4539461
  have htrace : WordTrace (prefixWord ++ tailWord_4539461) baseStart_4539461 baseEnd_4539461 := by
    simpa [prefixWord, tailWord_4539461, baseEnd_4539461] using wordTrace_append hprefix tailTrace_4539461
  have hstable : (prefixWord ++ tailWord_4539461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539461).length < 2 ^ (prefixWord ++ tailWord_4539461).sum := by decide
  have hdescent : baseEnd_4539461 < baseStart_4539461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539478 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4539478 : Nat := 118140960795 + 4539478 * 2 ^ 59
def prefixEnd_4539478 : Nat := 4983230072969 + 3 ^ 40 * 4539478 * 2
def baseEnd_4539478 : Nat := 776978044836898501716109

theorem tailTrace_4539478 : CollatzResearch.WordTrace tailWord_4539478 prefixEnd_4539478 776978044836898501716109 := by
  unfold tailWord_4539478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348022790515872622764193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110378909765502641309484725 10348022790515872622764193)
  ·
    refine ⟨7761017092886904467073145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10348022790515872622764193 7761017092886904467073145)
    ·
      refine ⟨5820762819665178350304859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7761017092886904467073145 5820762819665178350304859)
      ·
        refine ⟨8731144229497767525457289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820762819665178350304859 8731144229497767525457289)
        ·
          refine ⟨6548358172123325644092967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8731144229497767525457289 6548358172123325644092967)
          ·
            refine ⟨9822537258184988466139451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548358172123325644092967 9822537258184988466139451)
            ·
              refine ⟨14733805887277482699209177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9822537258184988466139451 14733805887277482699209177)
              ·
                refine ⟨11050354415458112024406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14733805887277482699209177 11050354415458112024406883)
                ·
                  refine ⟨16575531623187168036610325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11050354415458112024406883 16575531623187168036610325)
                  ·
                    refine ⟨776978044836898501716109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16575531623187168036610325 776978044836898501716109)
                    ·
                      rfl

theorem cell23_4539478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4539478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539478 prefixEnd_4539478 := by exact prefixLift 4539478
  have htrace : WordTrace (prefixWord ++ tailWord_4539478) baseStart_4539478 baseEnd_4539478 := by
    simpa [prefixWord, tailWord_4539478, baseEnd_4539478] using wordTrace_append hprefix tailTrace_4539478
  have hstable : (prefixWord ++ tailWord_4539478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539478).length < 2 ^ (prefixWord ++ tailWord_4539478).sum := by decide
  have hdescent : baseEnd_4539478 < baseStart_4539478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539485 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4539485 : Nat := 118140960795 + 4539485 * 2 ^ 59
def prefixEnd_4539485 : Nat := 4983230072969 + 3 ^ 40 * 4539485 * 2
def baseEnd_4539485 : Nat := 2330937728875276977760795

theorem tailTrace_4539485 : CollatzResearch.WordTrace tailWord_4539485 prefixEnd_4539485 2330937728875276977760795 := by
  unfold tailWord_4539485
  simp only [CollatzResearch.WordTrace]
  refine ⟨165568619959228602159731909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110379079972819068106487939 165568619959228602159731909)
  ·
    refine ⟨31044116242355362904949733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165568619959228602159731909 31044116242355362904949733)
    ·
      refine ⟨5820771795441630544678075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31044116242355362904949733 5820771795441630544678075)
      ·
        refine ⟨8731157693162445817017113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820771795441630544678075 8731157693162445817017113)
        ·
          refine ⟨6548368269871834362762835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8731157693162445817017113 6548368269871834362762835)
          ·
            refine ⟨9822552404807751544144253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548368269871834362762835 9822552404807751544144253)
            ·
              refine ⟨3683457151802906829054095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9822552404807751544144253 3683457151802906829054095)
              ·
                refine ⟨5525185727704360243581143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683457151802906829054095 5525185727704360243581143)
                ·
                  refine ⟨8287778591556540365371715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5525185727704360243581143 8287778591556540365371715)
                  ·
                    refine ⟨12431667887334810548057573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8287778591556540365371715 12431667887334810548057573)
                    ·
                      refine ⟨2330937728875276977760795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12431667887334810548057573 2330937728875276977760795)
                      ·
                        rfl

theorem cell23_4539485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4539485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539485 prefixEnd_4539485 := by exact prefixLift 4539485
  have htrace : WordTrace (prefixWord ++ tailWord_4539485) baseStart_4539485 baseEnd_4539485 := by
    simpa [prefixWord, tailWord_4539485, baseEnd_4539485] using wordTrace_append hprefix tailTrace_4539485
  have hstable : (prefixWord ++ tailWord_4539485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539485).length < 2 ^ (prefixWord ++ tailWord_4539485).sum := by decide
  have hdescent : baseEnd_4539485 < baseStart_4539485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539502 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4539502 : Nat := 118140960795 + 4539502 * 2 ^ 59
def prefixEnd_4539502 : Nat := 4983230072969 + 3 ^ 40 * 4539502 * 2
def baseEnd_4539502 : Nat := 2330946458046403411248217

theorem tailTrace_4539502 : CollatzResearch.WordTrace tailWord_4539502 prefixEnd_4539502 2330946458046403411248217 := by
  unfold tailWord_4539502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20696155000020876757887595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110379493333444676042067173 20696155000020876757887595)
  ·
    refine ⟨31044232500031315136831393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20696155000020876757887595 31044232500031315136831393)
    ·
      refine ⟨23283174375023486352623545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31044232500031315136831393 23283174375023486352623545)
      ·
        refine ⟨17462380781267614764467659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23283174375023486352623545 17462380781267614764467659)
        ·
          refine ⟨26193571171901422146701489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17462380781267614764467659 26193571171901422146701489)
          ·
            refine ⟨19645178378926066610026117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26193571171901422146701489 19645178378926066610026117)
            ·
              refine ⟨3683470946048637489379897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19645178378926066610026117 3683470946048637489379897)
              ·
                refine ⟨2762603209536478117034923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683470946048637489379897 2762603209536478117034923)
                ·
                  refine ⟨4143904814304717175552385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762603209536478117034923 4143904814304717175552385)
                  ·
                    refine ⟨3107928610728537881664289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4143904814304717175552385 3107928610728537881664289)
                    ·
                      refine ⟨2330946458046403411248217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107928610728537881664289 2330946458046403411248217)
                      ·
                        rfl

theorem cell23_4539502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4539502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539502 prefixEnd_4539502 := by exact prefixLift 4539502
  have htrace : WordTrace (prefixWord ++ tailWord_4539502) baseStart_4539502 baseEnd_4539502 := by
    simpa [prefixWord, tailWord_4539502, baseEnd_4539502] using wordTrace_append hprefix tailTrace_4539502
  have hstable : (prefixWord ++ tailWord_4539502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539502).length < 2 ^ (prefixWord ++ tailWord_4539502).sum := by decide
  have hdescent : baseEnd_4539502 < baseStart_4539502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539575 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_4539575 : Nat := 118140960795 + 4539575 * 2 ^ 59
def prefixEnd_4539575 : Nat := 4983230072969 + 3 ^ 40 * 4539575 * 2
def baseEnd_4539575 : Nat := 2330983942134181625635381

theorem tailTrace_4539575 : CollatzResearch.WordTrace tailWord_4539575 prefixEnd_4539575 2330983942134181625635381 := by
  unfold tailWord_4539575
  simp only [CollatzResearch.WordTrace]
  refine ⟨165571902528902547530508179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110381268352601698353672119 165571902528902547530508179)
  ·
    refine ⟨248357853793353821295762269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165571902528902547530508179 248357853793353821295762269)
    ·
      refine ⟨93134195172507682985910851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248357853793353821295762269 93134195172507682985910851)
      ·
        refine ⟨139701292758761524478866277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93134195172507682985910851 139701292758761524478866277)
        ·
          refine ⟨26193992392267785839787427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139701292758761524478866277 26193992392267785839787427)
          ·
            refine ⟨39290988588401678759681141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26193992392267785839787427 39290988588401678759681141)
            ·
              refine ⟨3683530180162657383720107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39290988588401678759681141 3683530180162657383720107)
              ·
                refine ⟨5525295270243986075580161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683530180162657383720107 5525295270243986075580161)
                ·
                  refine ⟨4143971452682989556685121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5525295270243986075580161 4143971452682989556685121)
                  ·
                    refine ⟨3107978589512242167513841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4143971452682989556685121 3107978589512242167513841)
                    ·
                      refine ⟨2330983942134181625635381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3107978589512242167513841 2330983942134181625635381)
                      ·
                        rfl

theorem cell23_4539575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_4539575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539575 prefixEnd_4539575 := by exact prefixLift 4539575
  have htrace : WordTrace (prefixWord ++ tailWord_4539575) baseStart_4539575 baseEnd_4539575 := by
    simpa [prefixWord, tailWord_4539575, baseEnd_4539575] using wordTrace_append hprefix tailTrace_4539575
  have hstable : (prefixWord ++ tailWord_4539575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539575).length < 2 ^ (prefixWord ++ tailWord_4539575).sum := by decide
  have hdescent : baseEnd_4539575 < baseStart_4539575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539587 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_4539587 : Nat := 118140960795 + 4539587 * 2 ^ 59
def prefixEnd_4539587 : Nat := 4983230072969 + 3 ^ 40 * 4539587 * 2
def baseEnd_4539587 : Nat := 2330990103902035578685325

theorem tailTrace_4539587 : CollatzResearch.WordTrace tailWord_4539587 prefixEnd_4539587 2330990103902035578685325 := by
  unfold tailWord_4539587
  simp only [CollatzResearch.WordTrace]
  refine ⟨165572340204859073579945015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110381560136572715719963343 165572340204859073579945015)
  ·
    refine ⟨248358510307288610369917523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165572340204859073579945015 248358510307288610369917523)
    ·
      refine ⟨372537765460932915554876285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248358510307288610369917523 372537765460932915554876285)
      ·
        refine ⟨139701662047849843333078607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372537765460932915554876285 139701662047849843333078607)
        ·
          refine ⟨209552493071774764999617911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139701662047849843333078607 209552493071774764999617911)
          ·
            refine ⟨314328739607662147499426867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209552493071774764999617911 314328739607662147499426867)
            ·
              refine ⟨471493109411493221249140301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314328739607662147499426867 471493109411493221249140301)
              ·
                refine ⟨176809916029309957968427613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471493109411493221249140301 176809916029309957968427613)
                ·
                  refine ⟨66303718510991234238160355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176809916029309957968427613 66303718510991234238160355)
                  ·
                    refine ⟨99455577766486851357240533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66303718510991234238160355 99455577766486851357240533)
                    ·
                      refine ⟨2330990103902035578685325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99455577766486851357240533 2330990103902035578685325)
                      ·
                        rfl

theorem cell23_4539587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_4539587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539587 prefixEnd_4539587 := by exact prefixLift 4539587
  have htrace : WordTrace (prefixWord ++ tailWord_4539587) baseStart_4539587 baseEnd_4539587 := by
    simpa [prefixWord, tailWord_4539587, baseEnd_4539587] using wordTrace_append hprefix tailTrace_4539587
  have hstable : (prefixWord ++ tailWord_4539587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539587).length < 2 ^ (prefixWord ++ tailWord_4539587).sum := by decide
  have hdescent : baseEnd_4539587 < baseStart_4539587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539594 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_4539594 : Nat := 118140960795 + 4539594 * 2 ^ 59
def prefixEnd_4539594 : Nat := 4983230072969 + 3 ^ 40 * 4539594 * 2
def baseEnd_4539594 : Nat := 776997899422205683765931

theorem tailTrace_4539594 : CollatzResearch.WordTrace tailWord_4539594 prefixEnd_4539594 776997899422205683765931 := by
  unfold tailWord_4539594
  simp only [CollatzResearch.WordTrace]
  refine ⟨41393148878958428443862459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110381730343889142516966557 41393148878958428443862459)
  ·
    refine ⟨62089723318437642665793689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41393148878958428443862459 62089723318437642665793689)
    ·
      refine ⟨46567292488828231999345267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62089723318437642665793689 46567292488828231999345267)
      ·
        refine ⟨69850938733242347999017901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46567292488828231999345267 69850938733242347999017901)
        ·
          refine ⟨26194102024965880499631713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69850938733242347999017901 26194102024965880499631713)
          ·
            refine ⟨19645576518724410374723785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26194102024965880499631713 19645576518724410374723785)
            ·
              refine ⟨14734182389043307781042839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19645576518724410374723785 14734182389043307781042839)
              ·
                refine ⟨22101273583564961671564259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734182389043307781042839 22101273583564961671564259)
                ·
                  refine ⟨33151910375347442507346389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22101273583564961671564259 33151910375347442507346389)
                  ·
                    refine ⟨776997899422205683765931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33151910375347442507346389 776997899422205683765931)
                    ·
                      rfl

theorem cell23_4539594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_4539594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539594 prefixEnd_4539594 := by exact prefixLift 4539594
  have htrace : WordTrace (prefixWord ++ tailWord_4539594) baseStart_4539594 baseEnd_4539594 := by
    simpa [prefixWord, tailWord_4539594, baseEnd_4539594] using wordTrace_append hprefix tailTrace_4539594
  have hstable : (prefixWord ++ tailWord_4539594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539594).length < 2 ^ (prefixWord ++ tailWord_4539594).sum := by decide
  have hdescent : baseEnd_4539594 < baseStart_4539594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539621 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4539621 : Nat := 118140960795 + 4539621 * 2 ^ 59
def prefixEnd_4539621 : Nat := 4983230072969 + 3 ^ 40 * 4539621 * 2
def baseEnd_4539621 : Nat := 2331007562244288445660169

theorem tailTrace_4539621 : CollatzResearch.WordTrace tailWord_4539621 prefixEnd_4539621 2331007562244288445660169 := by
  unfold tailWord_4539621
  simp only [CollatzResearch.WordTrace]
  refine ⟨165573580286735897386682717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110382386857823931591121811 165573580286735897386682717)
  ·
    refine ⟨62090092607525961520006019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165573580286735897386682717 62090092607525961520006019)
    ·
      refine ⟨93135138911288942280009029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62090092607525961520006019 93135138911288942280009029)
      ·
        refine ⟨17462838545866676677501693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93135138911288942280009029 17462838545866676677501693)
        ·
          refine ⟨6548564454700003754063135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17462838545866676677501693 6548564454700003754063135)
          ·
            refine ⟨9822846682050005631094703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548564454700003754063135 9822846682050005631094703)
            ·
              refine ⟨14734270023075008446642055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9822846682050005631094703 14734270023075008446642055)
              ·
                refine ⟨22101405034612512669963083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734270023075008446642055 22101405034612512669963083)
                ·
                  refine ⟨33152107551918769004944625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22101405034612512669963083 33152107551918769004944625)
                  ·
                    refine ⟨24864080663939076753708469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33152107551918769004944625 24864080663939076753708469)
                    ·
                      refine ⟨2331007562244288445660169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24864080663939076753708469 2331007562244288445660169)
                      ·
                        rfl

theorem cell23_4539621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4539621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539621 prefixEnd_4539621 := by exact prefixLift 4539621
  have htrace : WordTrace (prefixWord ++ tailWord_4539621) baseStart_4539621 baseEnd_4539621 := by
    simpa [prefixWord, tailWord_4539621, baseEnd_4539621] using wordTrace_append hprefix tailTrace_4539621
  have hstable : (prefixWord ++ tailWord_4539621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539621).length < 2 ^ (prefixWord ++ tailWord_4539621).sum := by decide
  have hdescent : baseEnd_4539621 < baseStart_4539621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539651 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3]
def baseStart_4539651 : Nat := 118140960795 + 4539651 * 2 ^ 59
def prefixEnd_4539651 : Nat := 4983230072969 + 3 ^ 40 * 4539651 * 2
def baseEnd_4539651 : Nat := 2331022966663923328285031

theorem tailTrace_4539651 : CollatzResearch.WordTrace tailWord_4539651 prefixEnd_4539651 2331022966663923328285031 := by
  unfold tailWord_4539651
  simp only [CollatzResearch.WordTrace]
  refine ⟨165574674476627212510274807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110383116317751475006849871 165574674476627212510274807)
  ·
    refine ⟨248362011714940818765412211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165574674476627212510274807 248362011714940818765412211)
    ·
      refine ⟨372543017572411228148118317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248362011714940818765412211 372543017572411228148118317)
      ·
        refine ⟨139703631589654210555544369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372543017572411228148118317 139703631589654210555544369)
        ·
          refine ⟨104777723692240657916658277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139703631589654210555544369 104777723692240657916658277)
          ·
            refine ⟨19645823192295123359373427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104777723692240657916658277 19645823192295123359373427)
            ·
              refine ⟨29468734788442685039060141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19645823192295123359373427 29468734788442685039060141)
              ·
                refine ⟨11050775545666006889647553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29468734788442685039060141 11050775545666006889647553)
                ·
                  refine ⟨8288081659249505167235665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11050775545666006889647553 8288081659249505167235665)
                  ·
                    refine ⟨6216061244437128875426749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8288081659249505167235665 6216061244437128875426749)
                    ·
                      refine ⟨2331022966663923328285031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216061244437128875426749 2331022966663923328285031)
                      ·
                        rfl

theorem cell23_4539651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_4539651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539651 prefixEnd_4539651 := by exact prefixLift 4539651
  have htrace : WordTrace (prefixWord ++ tailWord_4539651) baseStart_4539651 baseEnd_4539651 := by
    simpa [prefixWord, tailWord_4539651, baseEnd_4539651] using wordTrace_append hprefix tailTrace_4539651
  have hstable : (prefixWord ++ tailWord_4539651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539651).length < 2 ^ (prefixWord ++ tailWord_4539651).sum := by decide
  have hdescent : baseEnd_4539651 < baseStart_4539651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539658 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_4539658 : Nat := 118140960795 + 4539658 * 2 ^ 59
def prefixEnd_4539658 : Nat := 4983230072969 + 3 ^ 40 * 4539658 * 2
def baseEnd_4539658 : Nat := 777008853676168266965833

theorem tailTrace_4539658 : CollatzResearch.WordTrace tailWord_4539658 prefixEnd_4539658 777008853676168266965833 := by
  unfold tailWord_4539658
  simp only [CollatzResearch.WordTrace]
  refine ⟨41393732446900463176444907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110383286525067901803853085 41393732446900463176444907)
  ·
    refine ⟨62090598670350694764667361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41393732446900463176444907 62090598670350694764667361)
    ·
      refine ⟨46567949002763021073500521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62090598670350694764667361 46567949002763021073500521)
      ·
        refine ⟨34925961752072265805125391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46567949002763021073500521 34925961752072265805125391)
        ·
          refine ⟨52388942628108398707688087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34925961752072265805125391 52388942628108398707688087)
          ·
            refine ⟨78583413942162598061532131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52388942628108398707688087 78583413942162598061532131)
            ·
              refine ⟨117875120913243897092298197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78583413942162598061532131 117875120913243897092298197)
              ·
                refine ⟨2762698146404153838100739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117875120913243897092298197 2762698146404153838100739)
                ·
                  refine ⟨4144047219606230757151109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762698146404153838100739 4144047219606230757151109)
                  ·
                    refine ⟨777008853676168266965833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144047219606230757151109 777008853676168266965833)
                    ·
                      rfl

theorem cell23_4539658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_4539658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539658 prefixEnd_4539658 := by exact prefixLift 4539658
  have htrace : WordTrace (prefixWord ++ tailWord_4539658) baseStart_4539658 baseEnd_4539658 := by
    simpa [prefixWord, tailWord_4539658, baseEnd_4539658] using wordTrace_append hprefix tailTrace_4539658
  have hstable : (prefixWord ++ tailWord_4539658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539658).length < 2 ^ (prefixWord ++ tailWord_4539658).sum := by decide
  have hdescent : baseEnd_4539658 < baseStart_4539658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_4539664 : Nat := 118140960795 + 4539664 * 2 ^ 59
def prefixEnd_4539664 : Nat := 4983230072969 + 3 ^ 40 * 4539664 * 2
def baseEnd_4539664 : Nat := 2331029641912431777422471

theorem tailTrace_4539664 : CollatzResearch.WordTrace tailWord_4539664 prefixEnd_4539664 2331029641912431777422471 := by
  unfold tailWord_4539664
  simp only [CollatzResearch.WordTrace]
  refine ⟨82787574312790057865249023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110383432417053410486998697 82787574312790057865249023)
  ·
    refine ⟨124181361469185086797873535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82787574312790057865249023 124181361469185086797873535)
    ·
      refine ⟨186272042203777630196810303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124181361469185086797873535 186272042203777630196810303)
      ·
        refine ⟨279408063305666445295215455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186272042203777630196810303 279408063305666445295215455)
        ·
          refine ⟨419112094958499667942823183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279408063305666445295215455 419112094958499667942823183)
          ·
            refine ⟨628668142437749501914234775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419112094958499667942823183 628668142437749501914234775)
            ·
              refine ⟨943002213656624252871352163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628668142437749501914234775 943002213656624252871352163)
              ·
                refine ⟨1414503320484936379307028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943002213656624252871352163 1414503320484936379307028245)
                ·
                  refine ⟨66304843147731392780016949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1414503320484936379307028245 66304843147731392780016949)
                  ·
                    refine ⟨6216079045099818073126589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66304843147731392780016949 6216079045099818073126589)
                    ·
                      refine ⟨2331029641912431777422471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216079045099818073126589 2331029641912431777422471)
                      ·
                        rfl

theorem cell23_4539664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_4539664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539664 prefixEnd_4539664 := by exact prefixLift 4539664
  have htrace : WordTrace (prefixWord ++ tailWord_4539664) baseStart_4539664 baseEnd_4539664 := by
    simpa [prefixWord, tailWord_4539664, baseEnd_4539664] using wordTrace_append hprefix tailTrace_4539664
  have hstable : (prefixWord ++ tailWord_4539664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539664).length < 2 ^ (prefixWord ++ tailWord_4539664).sum := by decide
  have hdescent : baseEnd_4539664 < baseStart_4539664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539671 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 6]
def baseStart_4539671 : Nat := 118140960795 + 4539671 * 2 ^ 59
def prefixEnd_4539671 : Nat := 4983230072969 + 3 ^ 40 * 4539671 * 2
def baseEnd_4539671 : Nat := 259003692919668138892771

theorem tailTrace_4539671 : CollatzResearch.WordTrace tailWord_4539671 prefixEnd_4539671 259003692919668138892771 := by
  unfold tailWord_4539671
  simp only [CollatzResearch.WordTrace]
  refine ⟨165575403936554755926002867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110383602624369837284001911 165575403936554755926002867)
  ·
    refine ⟨248363105904832133889004301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165575403936554755926002867 248363105904832133889004301)
    ·
      refine ⟨93136164714312050208376613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248363105904832133889004301 93136164714312050208376613)
      ·
        refine ⟨17463030883933509414070615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93136164714312050208376613 17463030883933509414070615)
        ·
          refine ⟨26194546325900264121105923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17463030883933509414070615 26194546325900264121105923)
          ·
            refine ⟨39291819488850396181658885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26194546325900264121105923 39291819488850396181658885)
            ·
              refine ⟨7367216154159449284061041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39291819488850396181658885 7367216154159449284061041)
              ·
                refine ⟨5525412115619586963045781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7367216154159449284061041 5525412115619586963045781)
                ·
                  refine ⟨259003692919668138892771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5525412115619586963045781 259003692919668138892771)
                  ·
                    rfl

theorem cell23_4539671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 6].length) (baseStart_4539671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539671 prefixEnd_4539671 := by exact prefixLift 4539671
  have htrace : WordTrace (prefixWord ++ tailWord_4539671) baseStart_4539671 baseEnd_4539671 := by
    simpa [prefixWord, tailWord_4539671, baseEnd_4539671] using wordTrace_append hprefix tailTrace_4539671
  have hstable : (prefixWord ++ tailWord_4539671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539671).length < 2 ^ (prefixWord ++ tailWord_4539671).sum := by decide
  have hdescent : baseEnd_4539671 < baseStart_4539671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539698 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_4539698 : Nat := 118140960795 + 4539698 * 2 ^ 59
def prefixEnd_4539698 : Nat := 4983230072969 + 3 ^ 40 * 4539698 * 2
def baseEnd_4539698 : Nat := 2331047100254684644397315

theorem tailTrace_4539698 : CollatzResearch.WordTrace tailWord_4539698 prefixEnd_4539698 2331047100254684644397315 := by
  unfold tailWord_4539698
  simp only [CollatzResearch.WordTrace]
  refine ⟨41394097176864234884308937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110384259138304626358157165 41394097176864234884308937)
  ·
    refine ⟨31045572882648176163231703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41394097176864234884308937 31045572882648176163231703)
    ·
      refine ⟨46568359323972264244847555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31045572882648176163231703 46568359323972264244847555)
      ·
        refine ⟨69852538985958396367271333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46568359323972264244847555 69852538985958396367271333)
        ·
          refine ⟨13097351059867199318863375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69852538985958396367271333 13097351059867199318863375)
          ·
            refine ⟨19646026589800798978295063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13097351059867199318863375 19646026589800798978295063)
            ·
              refine ⟨29469039884701198467442595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19646026589800798978295063 29469039884701198467442595)
              ·
                refine ⟨44203559827051797701163893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29469039884701198467442595 44203559827051797701163893)
                ·
                  refine ⟨4144083733786106034484115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44203559827051797701163893 4144083733786106034484115)
                  ·
                    refine ⟨6216125600679159051726173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4144083733786106034484115 6216125600679159051726173)
                    ·
                      refine ⟨2331047100254684644397315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216125600679159051726173 2331047100254684644397315)
                      ·
                        rfl

theorem cell23_4539698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_4539698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539698 prefixEnd_4539698 := by exact prefixLift 4539698
  have htrace : WordTrace (prefixWord ++ tailWord_4539698) baseStart_4539698 baseEnd_4539698 := by
    simpa [prefixWord, tailWord_4539698, baseEnd_4539698] using wordTrace_append hprefix tailTrace_4539698
  have hstable : (prefixWord ++ tailWord_4539698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539698).length < 2 ^ (prefixWord ++ tailWord_4539698).sum := by decide
  have hdescent : baseEnd_4539698 < baseStart_4539698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539701 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4539701 : Nat := 118140960795 + 4539701 * 2 ^ 59
def prefixEnd_4539701 : Nat := 4983230072969 + 3 ^ 40 * 4539701 * 2
def baseEnd_4539701 : Nat := 777016213565549377553267

theorem tailTrace_4539701 : CollatzResearch.WordTrace tailWord_4539701 prefixEnd_4539701 777016213565549377553267 := by
  unfold tailWord_4539701
  simp only [CollatzResearch.WordTrace]
  refine ⟨165576498126446071049594957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110384332084297380699729971 165576498126446071049594957)
  ·
    refine ⟨62091186797417276643598109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165576498126446071049594957 62091186797417276643598109)
    ·
      refine ⟨23284195049031478741349291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62091186797417276643598109 23284195049031478741349291)
      ·
        refine ⟨34926292573547218112023937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23284195049031478741349291 34926292573547218112023937)
        ·
          refine ⟨26194719430160413584017953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34926292573547218112023937 26194719430160413584017953)
          ·
            refine ⟨19646039572620310188013465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26194719430160413584017953 19646039572620310188013465)
            ·
              refine ⟨14734529679465232641010099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19646039572620310188013465 14734529679465232641010099)
              ·
                refine ⟨22101794519197848961515149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734529679465232641010099 22101794519197848961515149)
                ·
                  refine ⟨8288172944699193360568181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22101794519197848961515149 8288172944699193360568181)
                  ·
                    refine ⟨777016213565549377553267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8288172944699193360568181 777016213565549377553267)
                    ·
                      rfl

theorem cell23_4539701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4539701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539701 prefixEnd_4539701 := by exact prefixLift 4539701
  have htrace : WordTrace (prefixWord ++ tailWord_4539701) baseStart_4539701 baseEnd_4539701 := by
    simpa [prefixWord, tailWord_4539701, baseEnd_4539701] using wordTrace_append hprefix tailTrace_4539701
  have hstable : (prefixWord ++ tailWord_4539701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539701).length < 2 ^ (prefixWord ++ tailWord_4539701).sum := by decide
  have hdescent : baseEnd_4539701 < baseStart_4539701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539708 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_4539708 : Nat := 118140960795 + 4539708 * 2 ^ 59
def prefixEnd_4539708 : Nat := 4983230072969 + 3 ^ 40 * 4539708 * 2
def baseEnd_4539708 : Nat := 2331052235061229605272269

theorem tailTrace_4539708 : CollatzResearch.WordTrace tailWord_4539708 prefixEnd_4539708 2331052235061229605272269 := by
  unfold tailWord_4539708
  simp only [CollatzResearch.WordTrace]
  refine ⟨82788376718710355622549889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110384502291613807496733185 82788376718710355622549889)
  ·
    refine ⟨62091282539032766716912417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82788376718710355622549889 62091282539032766716912417)
    ·
      refine ⟨46568461904274575037684313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62091282539032766716912417 46568461904274575037684313)
      ·
        refine ⟨34926346428205931278263235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46568461904274575037684313 34926346428205931278263235)
        ·
          refine ⟨52389519642308896917394853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34926346428205931278263235 52389519642308896917394853)
          ·
            refine ⟨9823034932932918172011535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52389519642308896917394853 9823034932932918172011535)
            ·
              refine ⟨14734552399399377258017303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9823034932932918172011535 14734552399399377258017303)
              ·
                refine ⟨22101828599099065887025955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734552399399377258017303 22101828599099065887025955)
                ·
                  refine ⟨33152742898648598830538933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22101828599099065887025955 33152742898648598830538933)
                  ·
                    refine ⟨3108069646748306140363025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33152742898648598830538933 3108069646748306140363025)
                    ·
                      refine ⟨2331052235061229605272269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108069646748306140363025 2331052235061229605272269)
                      ·
                        rfl

theorem cell23_4539708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_4539708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539708 prefixEnd_4539708 := by exact prefixLift 4539708
  have htrace : WordTrace (prefixWord ++ tailWord_4539708) baseStart_4539708 baseEnd_4539708 := by
    simpa [prefixWord, tailWord_4539708, baseEnd_4539708] using wordTrace_append hprefix tailTrace_4539708
  have hstable : (prefixWord ++ tailWord_4539708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539708).length < 2 ^ (prefixWord ++ tailWord_4539708).sum := by decide
  have hdescent : baseEnd_4539708 < baseStart_4539708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539731 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 4, 4]
def baseStart_4539731 : Nat := 118140960795 + 4539731 * 2 ^ 59
def prefixEnd_4539731 : Nat := 4983230072969 + 3 ^ 40 * 4539731 * 2
def baseEnd_4539731 : Nat := 777021348372094338428221

theorem tailTrace_4539731 : CollatzResearch.WordTrace tailWord_4539731 prefixEnd_4539731 777021348372094338428221 := by
  unfold tailWord_4539731
  simp only [CollatzResearch.WordTrace]
  refine ⟨165577592316337386173187047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110385061544224924115458031 165577592316337386173187047)
  ·
    refine ⟨248366388474506079259780571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165577592316337386173187047 248366388474506079259780571)
    ·
      refine ⟨372549582711759118889670857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248366388474506079259780571 372549582711759118889670857)
      ·
        refine ⟨279412187033819339167253143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372549582711759118889670857 279412187033819339167253143)
        ·
          refine ⟨419118280550729008750879715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279412187033819339167253143 419118280550729008750879715)
          ·
            refine ⟨628677420826093513126319573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419118280550729008750879715 628677420826093513126319573)
            ·
              refine ⟨14734627050611566713898115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 628677420826093513126319573 14734627050611566713898115)
              ·
                refine ⟨22101940575917350070847173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734627050611566713898115 22101940575917350070847173)
                ·
                  refine ⟨4144113857984503138283845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22101940575917350070847173 4144113857984503138283845)
                  ·
                    refine ⟨777021348372094338428221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144113857984503138283845 777021348372094338428221)
                    ·
                      rfl

theorem cell23_4539731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 4].length) (baseStart_4539731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539731 prefixEnd_4539731 := by exact prefixLift 4539731
  have htrace : WordTrace (prefixWord ++ tailWord_4539731) baseStart_4539731 baseEnd_4539731 := by
    simpa [prefixWord, tailWord_4539731, baseEnd_4539731] using wordTrace_append hprefix tailTrace_4539731
  have hstable : (prefixWord ++ tailWord_4539731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539731).length < 2 ^ (prefixWord ++ tailWord_4539731).sum := by decide
  have hdescent : baseEnd_4539731 < baseStart_4539731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539748 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_4539748 : Nat := 118140960795 + 4539748 * 2 ^ 59
def prefixEnd_4539748 : Nat := 4983230072969 + 3 ^ 40 * 4539748 * 2
def baseEnd_4539748 : Nat := 777024258095803149590695

theorem tailTrace_4539748 : CollatzResearch.WordTrace tailWord_4539748 prefixEnd_4539748 777024258095803149590695 := by
  unfold tailWord_4539748
  simp only [CollatzResearch.WordTrace]
  refine ⟨82789106178637899038277949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110385474904850532051037265 82789106178637899038277949)
  ·
    refine ⟨31045914816989212139354231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82789106178637899038277949 31045914816989212139354231)
    ·
      refine ⟨46568872225483818209031347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31045914816989212139354231 46568872225483818209031347)
      ·
        refine ⟨69853308338225727313547021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46568872225483818209031347 69853308338225727313547021)
        ·
          refine ⟨26194990626834647742580133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69853308338225727313547021 26194990626834647742580133)
          ·
            refine ⟨4911560742531496451733775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26194990626834647742580133 4911560742531496451733775)
            ·
              refine ⟨7367341113797244677600663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911560742531496451733775 7367341113797244677600663)
              ·
                refine ⟨11051011670695867016400995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7367341113797244677600663 11051011670695867016400995)
                ·
                  refine ⟨16576517506043800524601493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11051011670695867016400995 16576517506043800524601493)
                  ·
                    refine ⟨777024258095803149590695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16576517506043800524601493 777024258095803149590695)
                    ·
                      rfl

theorem cell23_4539748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_4539748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539748 prefixEnd_4539748 := by exact prefixLift 4539748
  have htrace : WordTrace (prefixWord ++ tailWord_4539748) baseStart_4539748 baseEnd_4539748 := by
    simpa [prefixWord, tailWord_4539748, baseEnd_4539748] using wordTrace_append hprefix tailTrace_4539748
  have hstable : (prefixWord ++ tailWord_4539748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539748).length < 2 ^ (prefixWord ++ tailWord_4539748).sum := by decide
  have hdescent : baseEnd_4539748 < baseStart_4539748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539761 : List Nat := [1, 2, 2, 2, 1, 2, 6, 7]
def baseStart_4539761 : Nat := 118140960795 + 4539761 * 2 ^ 59
def prefixEnd_4539761 : Nat := 4983230072969 + 3 ^ 40 * 4539761 * 2
def baseEnd_4539761 : Nat := 86336275908737699922575

theorem tailTrace_4539761 : CollatzResearch.WordTrace tailWord_4539761 prefixEnd_4539761 86336275908737699922575 := by
  unfold tailWord_4539761
  simp only [CollatzResearch.WordTrace]
  refine ⟨165578686506228701296779137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110385791004152467531186091 165578686506228701296779137)
  ·
    refine ⟨124184014879671525972584353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165578686506228701296779137 124184014879671525972584353)
    ·
      refine ⟨93138011159753644479438265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124184014879671525972584353 93138011159753644479438265)
      ·
        refine ⟨69853508369815233359578699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93138011159753644479438265 69853508369815233359578699)
        ·
          refine ⟨104780262554722850039368049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69853508369815233359578699 104780262554722850039368049)
          ·
            refine ⟨78585196916042137529526037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104780262554722850039368049 78585196916042137529526037)
            ·
              refine ⟨3683681105439475196696533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78585196916042137529526037 3683681105439475196696533)
              ·
                refine ⟨86336275908737699922575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3683681105439475196696533 86336275908737699922575)
                ·
                  rfl

theorem cell23_4539761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 7].length) (baseStart_4539761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539761 prefixEnd_4539761 := by exact prefixLift 4539761
  have htrace : WordTrace (prefixWord ++ tailWord_4539761) baseStart_4539761 baseEnd_4539761 := by
    simpa [prefixWord, tailWord_4539761, baseEnd_4539761] using wordTrace_append hprefix tailTrace_4539761
  have hstable : (prefixWord ++ tailWord_4539761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539761).length < 2 ^ (prefixWord ++ tailWord_4539761).sum := by decide
  have hdescent : baseEnd_4539761 < baseStart_4539761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539771 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3]
def baseStart_4539771 : Nat := 118140960795 + 4539771 * 2 ^ 59
def prefixEnd_4539771 : Nat := 4983230072969 + 3 ^ 40 * 4539771 * 2
def baseEnd_4539771 : Nat := 2331084584342462858784479

theorem tailTrace_4539771 : CollatzResearch.WordTrace tailWord_4539771 prefixEnd_4539771 2331084584342462858784479 := by
  unfold tailWord_4539771
  simp only [CollatzResearch.WordTrace]
  refine ⟨165579051236192473004643167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110386034157461648669762111 165579051236192473004643167)
  ·
    refine ⟨248368576854288709506964751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165579051236192473004643167 248368576854288709506964751)
    ·
      refine ⟨372552865281433064260447127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248368576854288709506964751 372552865281433064260447127)
      ·
        refine ⟨558829297922149596390670691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372552865281433064260447127 558829297922149596390670691)
        ·
          refine ⟨838243946883224394586006037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558829297922149596390670691 838243946883224394586006037)
          ·
            refine ⟨39292685010151143496219033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 838243946883224394586006037 39292685010151143496219033)
            ·
              refine ⟨29469513757613357622164275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39292685010151143496219033 29469513757613357622164275)
              ·
                refine ⟨44204270636420036433246413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29469513757613357622164275 44204270636420036433246413)
                ·
                  refine ⟨16576601488657513662467405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44204270636420036433246413 16576601488657513662467405)
                  ·
                    refine ⟨6216225558246567623425277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16576601488657513662467405 6216225558246567623425277)
                    ·
                      refine ⟨2331084584342462858784479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216225558246567623425277 2331084584342462858784479)
                      ·
                        rfl

theorem cell23_4539771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3].length) (baseStart_4539771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539771 prefixEnd_4539771 := by exact prefixLift 4539771
  have htrace : WordTrace (prefixWord ++ tailWord_4539771) baseStart_4539771 baseEnd_4539771 := by
    simpa [prefixWord, tailWord_4539771, baseEnd_4539771] using wordTrace_append hprefix tailTrace_4539771
  have hstable : (prefixWord ++ tailWord_4539771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539771).length < 2 ^ (prefixWord ++ tailWord_4539771).sum := by decide
  have hdescent : baseEnd_4539771 < baseStart_4539771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539778 : List Nat := [3, 4, 2, 1, 1, 1, 11]
def baseStart_4539778 : Nat := 118140960795 + 4539778 * 2 ^ 59
def prefixEnd_4539778 : Nat := 4983230072969 + 3 ^ 40 * 4539778 * 2
def baseEnd_4539778 : Nat := 28778866403790670757987

theorem tailTrace_4539778 : CollatzResearch.WordTrace tailWord_4539778 prefixEnd_4539778 28778866403790670757987 := by
  unfold tailWord_4539778
  simp only [CollatzResearch.WordTrace]
  refine ⟨41394826636791778300036997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110386204364778075466765325 41394826636791778300036997)
  ·
    refine ⟨7761529994398458431256937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41394826636791778300036997 7761529994398458431256937)
    ·
      refine ⟨5821147495798843823442703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7761529994398458431256937 5821147495798843823442703)
      ·
        refine ⟨8731721243698265735164055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821147495798843823442703 8731721243698265735164055)
        ·
          refine ⟨13097581865547398602746083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731721243698265735164055 13097581865547398602746083)
          ·
            refine ⟨19646372798321097904119125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13097581865547398602746083 19646372798321097904119125)
            ·
              refine ⟨28778866403790670757987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19646372798321097904119125 28778866403790670757987)
              ·
                rfl

theorem cell23_4539778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 11].length) (baseStart_4539778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539778 prefixEnd_4539778 := by exact prefixLift 4539778
  have htrace : WordTrace (prefixWord ++ tailWord_4539778) baseStart_4539778 baseEnd_4539778 := by
    simpa [prefixWord, tailWord_4539778, baseEnd_4539778] using wordTrace_append hprefix tailTrace_4539778
  have hstable : (prefixWord ++ tailWord_4539778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539778).length < 2 ^ (prefixWord ++ tailWord_4539778).sum := by decide
  have hdescent : baseEnd_4539778 < baseStart_4539778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539788 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4539788 : Nat := 118140960795 + 4539788 * 2 ^ 59
def prefixEnd_4539788 : Nat := 4983230072969 + 3 ^ 40 * 4539788 * 2
def baseEnd_4539788 : Nat := 2331093313513589292271901

theorem tailTrace_4539788 : CollatzResearch.WordTrace tailWord_4539788 prefixEnd_4539788 2331093313513589292271901 := by
  unfold tailWord_4539788
  simp only [CollatzResearch.WordTrace]
  refine ⟨82789835638565442454006009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110386447518087256605341345 82789835638565442454006009)
  ·
    refine ⟨62092376728924081840504507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82789835638565442454006009 62092376728924081840504507)
    ·
      refine ⟨93138565093386122760756761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62092376728924081840504507 93138565093386122760756761)
      ·
        refine ⟨69853923820039592070567571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93138565093386122760756761 69853923820039592070567571)
        ·
          refine ⟨104780885730059388105851357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69853923820039592070567571 104780885730059388105851357)
          ·
            refine ⟨39292832148772270539694259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104780885730059388105851357 39292832148772270539694259)
            ·
              refine ⟨58939248223158405809541389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39292832148772270539694259 58939248223158405809541389)
              ·
                refine ⟨22102218083684402178578021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58939248223158405809541389 22102218083684402178578021)
                ·
                  refine ⟨4144165890690825408483379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22102218083684402178578021 4144165890690825408483379)
                  ·
                    refine ⟨6216248836036238112725069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4144165890690825408483379 6216248836036238112725069)
                    ·
                      refine ⟨2331093313513589292271901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216248836036238112725069 2331093313513589292271901)
                      ·
                        rfl

theorem cell23_4539788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4539788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539788 prefixEnd_4539788 := by exact prefixLift 4539788
  have htrace : WordTrace (prefixWord ++ tailWord_4539788) baseStart_4539788 baseEnd_4539788 := by
    simpa [prefixWord, tailWord_4539788, baseEnd_4539788] using wordTrace_append hprefix tailTrace_4539788
  have hstable : (prefixWord ++ tailWord_4539788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539788).length < 2 ^ (prefixWord ++ tailWord_4539788).sum := by decide
  have hdescent : baseEnd_4539788 < baseStart_4539788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539815 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4539815 : Nat := 118140960795 + 4539815 * 2 ^ 59
def prefixEnd_4539815 : Nat := 4983230072969 + 3 ^ 40 * 4539815 * 2
def baseEnd_4539815 : Nat := 2331107177491260686634277

theorem tailTrace_4539815 : CollatzResearch.WordTrace tailWord_4539815 prefixEnd_4539815 2331107177491260686634277 := by
  unfold tailWord_4539815
  simp only [CollatzResearch.WordTrace]
  refine ⟨165580656048033068519244899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110387104032022045679496599 165580656048033068519244899)
  ·
    refine ⟨248370984072049602778867349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165580656048033068519244899 248370984072049602778867349)
    ·
      refine ⟨11642389878377325130259407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 248370984072049602778867349 11642389878377325130259407)
      ·
        refine ⟨17463584817565987695389111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11642389878377325130259407 17463584817565987695389111)
        ·
          refine ⟨26195377226348981543083667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17463584817565987695389111 26195377226348981543083667)
          ·
            refine ⟨39293065839523472314625501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26195377226348981543083667 39293065839523472314625501)
            ·
              refine ⟨14734899689821302117984563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39293065839523472314625501 14734899689821302117984563)
              ·
                refine ⟨22102349534731953176976845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734899689821302117984563 22102349534731953176976845)
                ·
                  refine ⟨8288381075524482441366317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22102349534731953176976845 8288381075524482441366317)
                  ·
                    refine ⟨3108142903321680915512369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8288381075524482441366317 3108142903321680915512369)
                    ·
                      refine ⟨2331107177491260686634277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108142903321680915512369 2331107177491260686634277)
                      ·
                        rfl

theorem cell23_4539815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4539815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539815 prefixEnd_4539815 := by exact prefixLift 4539815
  have htrace : WordTrace (prefixWord ++ tailWord_4539815) baseStart_4539815 baseEnd_4539815 := by
    simpa [prefixWord, tailWord_4539815, baseEnd_4539815] using wordTrace_append hprefix tailTrace_4539815
  have hstable : (prefixWord ++ tailWord_4539815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539815).length < 2 ^ (prefixWord ++ tailWord_4539815).sum := by decide
  have hdescent : baseEnd_4539815 < baseStart_4539815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539831 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_4539831 : Nat := 118140960795 + 4539831 * 2 ^ 59
def prefixEnd_4539831 : Nat := 4983230072969 + 3 ^ 40 * 4539831 * 2
def baseEnd_4539831 : Nat := 2331115393181732624034203

theorem tailTrace_4539831 : CollatzResearch.WordTrace tailWord_4539831 prefixEnd_4539831 2331115393181732624034203 := by
  unfold tailWord_4539831
  simp only [CollatzResearch.WordTrace]
  refine ⟨165581239615975103251827347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110387493077316735501218231 165581239615975103251827347)
  ·
    refine ⟨248371859423962654877741021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165581239615975103251827347 248371859423962654877741021)
    ·
      refine ⟨93139447283985995579152883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248371859423962654877741021 93139447283985995579152883)
      ·
        refine ⟨139709170925978993368729325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93139447283985995579152883 139709170925978993368729325)
        ·
          refine ⟨52390939097242122513273497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139709170925978993368729325 52390939097242122513273497)
          ·
            refine ⟨39293204322931591884955123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52390939097242122513273497 39293204322931591884955123)
            ·
              refine ⟨58939806484397387827432685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39293204322931591884955123 58939806484397387827432685)
              ·
                refine ⟨22102427431649020435287257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58939806484397387827432685 22102427431649020435287257)
                ·
                  refine ⟨16576820573736765326465443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22102427431649020435287257 16576820573736765326465443)
                  ·
                    refine ⟨24865230860605147989698165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16576820573736765326465443 24865230860605147989698165)
                    ·
                      refine ⟨2331115393181732624034203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24865230860605147989698165 2331115393181732624034203)
                      ·
                        rfl

theorem cell23_4539831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_4539831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539831 prefixEnd_4539831 := by exact prefixLift 4539831
  have htrace : WordTrace (prefixWord ++ tailWord_4539831) baseStart_4539831 baseEnd_4539831 := by
    simpa [prefixWord, tailWord_4539831, baseEnd_4539831] using wordTrace_append hprefix tailTrace_4539831
  have hstable : (prefixWord ++ tailWord_4539831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539831).length < 2 ^ (prefixWord ++ tailWord_4539831).sum := by decide
  have hdescent : baseEnd_4539831 < baseStart_4539831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539862 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_4539862 : Nat := 118140960795 + 4539862 * 2 ^ 59
def prefixEnd_4539862 : Nat := 4983230072969 + 3 ^ 40 * 4539862 * 2
def baseEnd_4539862 : Nat := 2331131311082022002746561

theorem tailTrace_4539862 : CollatzResearch.WordTrace tailWord_4539862 prefixEnd_4539862 2331131311082022002746561 := by
  unfold tailWord_4539862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348898142428924721637865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110388246852575197030803893 10348898142428924721637865)
  ·
    refine ⟨7761673606821693541228399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10348898142428924721637865 7761673606821693541228399)
    ·
      refine ⟨11642510410232540311842599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761673606821693541228399 11642510410232540311842599)
      ·
        refine ⟨17463765615348810467763899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11642510410232540311842599 17463765615348810467763899)
        ·
          refine ⟨26195648423023215701645849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17463765615348810467763899 26195648423023215701645849)
          ·
            refine ⟨19646736317267411776234387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26195648423023215701645849 19646736317267411776234387)
            ·
              refine ⟨29470104475901117664351581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19646736317267411776234387 29470104475901117664351581)
              ·
                refine ⟨11051289178462919124131843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29470104475901117664351581 11051289178462919124131843)
                ·
                  refine ⟨16576933767694378686197765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11051289178462919124131843 16576933767694378686197765)
                  ·
                    refine ⟨3108175081442696003662081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16576933767694378686197765 3108175081442696003662081)
                    ·
                      refine ⟨2331131311082022002746561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108175081442696003662081 2331131311082022002746561)
                      ·
                        rfl

theorem cell23_4539862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_4539862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539862 prefixEnd_4539862 := by exact prefixLift 4539862
  have htrace : WordTrace (prefixWord ++ tailWord_4539862) baseStart_4539862 baseEnd_4539862 := by
    simpa [prefixWord, tailWord_4539862, baseEnd_4539862] using wordTrace_append hprefix tailTrace_4539862
  have hstable : (prefixWord ++ tailWord_4539862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539862).length < 2 ^ (prefixWord ++ tailWord_4539862).sum := by decide
  have hdescent : baseEnd_4539862 < baseStart_4539862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539891 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_4539891 : Nat := 118140960795 + 4539891 * 2 ^ 59
def prefixEnd_4539891 : Nat := 4983230072969 + 3 ^ 40 * 4539891 * 2
def baseEnd_4539891 : Nat := 2331146202021002389283927

theorem tailTrace_4539891 : CollatzResearch.WordTrace tailWord_4539891 prefixEnd_4539891 2331146202021002389283927 := by
  unfold tailWord_4539891
  simp only [CollatzResearch.WordTrace]
  refine ⟨165583427995757733499011527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110388951997171822332674351 165583427995757733499011527)
  ·
    refine ⟨248375141993636600248517291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165583427995757733499011527 248375141993636600248517291)
    ·
      refine ⟨372562712990454900372775937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248375141993636600248517291 372562712990454900372775937)
      ·
        refine ⟨279422034742841175279581953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372562712990454900372775937 279422034742841175279581953)
        ·
          refine ⟨209566526057130881459686465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279422034742841175279581953 209566526057130881459686465)
          ·
            refine ⟨157174894542848161094764849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209566526057130881459686465 157174894542848161094764849)
            ·
              refine ⟨117881170907136120821073637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157174894542848161094764849 117881170907136120821073637)
              ·
                refine ⟨22102719545088022653951307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117881170907136120821073637 22102719545088022653951307)
                ·
                  refine ⟨33154079317632033980926961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22102719545088022653951307 33154079317632033980926961)
                  ·
                    refine ⟨24865559488224025485695221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33154079317632033980926961 24865559488224025485695221)
                    ·
                      refine ⟨2331146202021002389283927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24865559488224025485695221 2331146202021002389283927)
                      ·
                        rfl

theorem cell23_4539891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_4539891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539891 prefixEnd_4539891 := by exact prefixLift 4539891
  have htrace : WordTrace (prefixWord ++ tailWord_4539891) baseStart_4539891 baseEnd_4539891 := by
    simpa [prefixWord, tailWord_4539891, baseEnd_4539891] using wordTrace_append hprefix tailTrace_4539891
  have hstable : (prefixWord ++ tailWord_4539891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539891).length < 2 ^ (prefixWord ++ tailWord_4539891).sum := by decide
  have hdescent : baseEnd_4539891 < baseStart_4539891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539902 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_4539902 : Nat := 118140960795 + 4539902 * 2 ^ 59
def prefixEnd_4539902 : Nat := 4983230072969 + 3 ^ 40 * 4539902 * 2
def baseEnd_4539902 : Nat := 259016872256466871805153

theorem tailTrace_4539902 : CollatzResearch.WordTrace tailWord_4539902 prefixEnd_4539902 259016872256466871805153 := by
  unfold tailWord_4539902
  simp only [CollatzResearch.WordTrace]
  refine ⟨20697978649839735297207745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110389219465811921585107973 20697978649839735297207745)
  ·
    refine ⟨15523483987379801472905809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20697978649839735297207745 15523483987379801472905809)
    ·
      refine ⟨11642612990534851104679357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15523483987379801472905809 11642612990534851104679357)
      ·
        refine ⟨4365979871450569164254759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11642612990534851104679357 4365979871450569164254759)
        ·
          refine ⟨6548969807175853746382139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365979871450569164254759 6548969807175853746382139)
          ·
            refine ⟨9823454710763780619573209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548969807175853746382139 9823454710763780619573209)
            ·
              refine ⟨7367591033072835464679907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9823454710763780619573209 7367591033072835464679907)
              ·
                refine ⟨11051386549609253197019861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7367591033072835464679907 11051386549609253197019861)
                ·
                  refine ⟨259016872256466871805153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11051386549609253197019861 259016872256466871805153)
                  ·
                    rfl

theorem cell23_4539902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_4539902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539902 prefixEnd_4539902 := by exact prefixLift 4539902
  have htrace : WordTrace (prefixWord ++ tailWord_4539902) baseStart_4539902 baseEnd_4539902 := by
    simpa [prefixWord, tailWord_4539902, baseEnd_4539902] using wordTrace_append hprefix tailTrace_4539902
  have hstable : (prefixWord ++ tailWord_4539902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539902).length < 2 ^ (prefixWord ++ tailWord_4539902).sum := by decide
  have hdescent : baseEnd_4539902 < baseStart_4539902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539955 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3]
def baseStart_4539955 : Nat := 118140960795 + 4539955 * 2 ^ 59
def prefixEnd_4539955 : Nat := 4983230072969 + 3 ^ 40 * 4539955 * 2
def baseEnd_4539955 : Nat := 2331179064782890138883633

theorem tailTrace_4539955 : CollatzResearch.WordTrace tailWord_4539955 prefixEnd_4539955 2331179064782890138883633 := by
  unfold tailWord_4539955
  simp only [CollatzResearch.WordTrace]
  refine ⟨165585762267525872429341319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110390508178350581619560879 165585762267525872429341319)
  ·
    refine ⟨248378643401288808644011979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165585762267525872429341319 248378643401288808644011979)
    ·
      refine ⟨372567965101933212966017969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248378643401288808644011979 372567965101933212966017969)
      ·
        refine ⟨279425973826449909724513477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372567965101933212966017969 279425973826449909724513477)
        ·
          refine ⟨52392370092459358073346277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279425973826449909724513477 52392370092459358073346277)
          ·
            refine ⟨9823569392336129638752427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52392370092459358073346277 9823569392336129638752427)
            ·
              refine ⟨14735354088504194458128641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9823569392336129638752427 14735354088504194458128641)
              ·
                refine ⟨11051515566378145843596481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14735354088504194458128641 11051515566378145843596481)
                ·
                  refine ⟨8288636674783609382697361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11051515566378145843596481 8288636674783609382697361)
                  ·
                    refine ⟨6216477506087707037023021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8288636674783609382697361 6216477506087707037023021)
                    ·
                      refine ⟨2331179064782890138883633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216477506087707037023021 2331179064782890138883633)
                      ·
                        rfl

theorem cell23_4539955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_4539955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539955 prefixEnd_4539955 := by exact prefixLift 4539955
  have htrace : WordTrace (prefixWord ++ tailWord_4539955) baseStart_4539955 baseEnd_4539955 := by
    simpa [prefixWord, tailWord_4539955, baseEnd_4539955] using wordTrace_append hprefix tailTrace_4539955
  have hstable : (prefixWord ++ tailWord_4539955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539955).length < 2 ^ (prefixWord ++ tailWord_4539955).sum := by decide
  have hdescent : baseEnd_4539955 < baseStart_4539955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539971 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 11]
def baseStart_4539971 : Nat := 118140960795 + 4539971 * 2 ^ 59
def prefixEnd_4539971 : Nat := 4983230072969 + 3 ^ 40 * 4539971 * 2
def baseEnd_4539971 : Nat := 777062426824454025427853

theorem tailTrace_4539971 : CollatzResearch.WordTrace tailWord_4539971 prefixEnd_4539971 777062426824454025427853 := by
  unfold tailWord_4539971
  simp only [CollatzResearch.WordTrace]
  refine ⟨165586345835467907161923767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110390897223645271441282511 165586345835467907161923767)
  ·
    refine ⟨248379518753201860742885651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165586345835467907161923767 248379518753201860742885651)
    ·
      refine ⟨372569278129802791114328477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248379518753201860742885651 372569278129802791114328477)
      ·
        refine ⟨139713479298676046667873179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372569278129802791114328477 139713479298676046667873179)
        ·
          refine ⟨209570218948014070001809769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139713479298676046667873179 209570218948014070001809769)
          ·
            refine ⟨157177664211010552501357327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209570218948014070001809769 157177664211010552501357327)
            ·
              refine ⟨235766496316515828752035991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157177664211010552501357327 235766496316515828752035991)
              ·
                refine ⟨353649744474773743128053987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235766496316515828752035991 353649744474773743128053987)
                ·
                  refine ⟨530474616712160614692080981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353649744474773743128053987 530474616712160614692080981)
                  ·
                    refine ⟨777062426824454025427853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 530474616712160614692080981 777062426824454025427853)
                    ·
                      rfl

theorem cell23_4539971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_4539971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539971 prefixEnd_4539971 := by exact prefixLift 4539971
  have htrace : WordTrace (prefixWord ++ tailWord_4539971) baseStart_4539971 baseEnd_4539971 := by
    simpa [prefixWord, tailWord_4539971, baseEnd_4539971] using wordTrace_append hprefix tailTrace_4539971
  have hstable : (prefixWord ++ tailWord_4539971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539971).length < 2 ^ (prefixWord ++ tailWord_4539971).sum := by decide
  have hdescent : baseEnd_4539971 < baseStart_4539971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539975 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 6]
def baseStart_4539975 : Nat := 118140960795 + 4539975 * 2 ^ 59
def prefixEnd_4539975 : Nat := 4983230072969 + 3 ^ 40 * 4539975 * 2
def baseEnd_4539975 : Nat := 259021037155108895625949

theorem tailTrace_4539975 : CollatzResearch.WordTrace tailWord_4539975 prefixEnd_4539975 259021037155108895625949 := by
  unfold tailWord_4539975
  simp only [CollatzResearch.WordTrace]
  refine ⟨165586491727453415845069379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110390994484968943896712919 165586491727453415845069379)
  ·
    refine ⟨248379737591180123767604069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165586491727453415845069379 248379737591180123767604069)
    ·
      refine ⟨46571200798346273206425763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248379737591180123767604069 46571200798346273206425763)
      ·
        refine ⟨69856801197519409809638645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46571200798346273206425763 69856801197519409809638645)
        ·
          refine ⟨6549075112267444669653623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69856801197519409809638645 6549075112267444669653623)
          ·
            refine ⟨9823612668401167004480435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549075112267444669653623 9823612668401167004480435)
            ·
              refine ⟨14735419002601750506720653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9823612668401167004480435 14735419002601750506720653)
              ·
                refine ⟨5525782125975656440020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14735419002601750506720653 5525782125975656440020245)
                ·
                  refine ⟨259021037155108895625949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5525782125975656440020245 259021037155108895625949)
                  ·
                    rfl

theorem cell23_4539975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 6].length) (baseStart_4539975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539975 prefixEnd_4539975 := by exact prefixLift 4539975
  have htrace : WordTrace (prefixWord ++ tailWord_4539975) baseStart_4539975 baseEnd_4539975 := by
    simpa [prefixWord, tailWord_4539975, baseEnd_4539975] using wordTrace_append hprefix tailTrace_4539975
  have hstable : (prefixWord ++ tailWord_4539975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539975).length < 2 ^ (prefixWord ++ tailWord_4539975).sum := by decide
  have hdescent : baseEnd_4539975 < baseStart_4539975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4539985 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_4539985 : Nat := 118140960795 + 4539985 * 2 ^ 59
def prefixEnd_4539985 : Nat := 4983230072969 + 3 ^ 40 * 4539985 * 2
def baseEnd_4539985 : Nat := 2331194469202525021508495

theorem tailTrace_4539985 : CollatzResearch.WordTrace tailWord_4539985 prefixEnd_4539985 2331194469202525021508495 := by
  unfold tailWord_4539985
  simp only [CollatzResearch.WordTrace]
  refine ⟨165586856457417187552933409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110391237638278125035288939 165586856457417187552933409)
  ·
    refine ⟨124190142343062890664700057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165586856457417187552933409 124190142343062890664700057)
    ·
      refine ⟨93142606757297167998525043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124190142343062890664700057 93142606757297167998525043)
      ·
        refine ⟨139713910135945751997787565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93142606757297167998525043 139713910135945751997787565)
        ·
          refine ⟨52392716300979656999170337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139713910135945751997787565 52392716300979656999170337)
          ·
            refine ⟨39294537225734742749377753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52392716300979656999170337 39294537225734742749377753)
            ·
              refine ⟨29470902919301057062033315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39294537225734742749377753 29470902919301057062033315)
              ·
                refine ⟨44206354378951585593049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29470902919301057062033315 44206354378951585593049973)
                ·
                  refine ⟨4144345723026711149348435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44206354378951585593049973 4144345723026711149348435)
                  ·
                    refine ⟨6216518584540066724022653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4144345723026711149348435 6216518584540066724022653)
                    ·
                      refine ⟨2331194469202525021508495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216518584540066724022653 2331194469202525021508495)
                      ·
                        rfl

theorem cell23_4539985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_4539985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4539985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4539985 prefixEnd_4539985 := by exact prefixLift 4539985
  have htrace : WordTrace (prefixWord ++ tailWord_4539985) baseStart_4539985 baseEnd_4539985 := by
    simpa [prefixWord, tailWord_4539985, baseEnd_4539985] using wordTrace_append hprefix tailTrace_4539985
  have hstable : (prefixWord ++ tailWord_4539985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4539985).length < 2 ^ (prefixWord ++ tailWord_4539985).sum := by decide
  have hdescent : baseEnd_4539985 < baseStart_4539985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4539985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540013 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_4540013 : Nat := 118140960795 + 4540013 * 2 ^ 59
def prefixEnd_4540013 : Nat := 4983230072969 + 3 ^ 40 * 4540013 * 2
def baseEnd_4540013 : Nat := 777069615553616970652789

theorem tailTrace_4540013 : CollatzResearch.WordTrace tailWord_4540013 prefixEnd_4540013 777069615553616970652789 := by
  unfold tailWord_4540013
  simp only [CollatzResearch.WordTrace]
  refine ⟨165587877701315748334952693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110391918467543832223301795 165587877701315748334952693)
  ·
    refine ⟨15523863534498351406401815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165587877701315748334952693 15523863534498351406401815)
    ·
      refine ⟨23285795301747527109602723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15523863534498351406401815 23285795301747527109602723)
      ·
        refine ⟨34928692952621290664404085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23285795301747527109602723 34928692952621290664404085)
        ·
          refine ⟨3274564964308245999787883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34928692952621290664404085 3274564964308245999787883)
          ·
            refine ⟨4911847446462368999681825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3274564964308245999787883 4911847446462368999681825)
            ·
              refine ⟨3683885584846776749761369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911847446462368999681825 3683885584846776749761369)
              ·
                refine ⟨2762914188635082562321027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683885584846776749761369 2762914188635082562321027)
                ·
                  refine ⟨4144371282952623843481541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762914188635082562321027 4144371282952623843481541)
                  ·
                    refine ⟨777069615553616970652789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144371282952623843481541 777069615553616970652789)
                    ·
                      rfl

theorem cell23_4540013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_4540013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540013 prefixEnd_4540013 := by exact prefixLift 4540013
  have htrace : WordTrace (prefixWord ++ tailWord_4540013) baseStart_4540013 baseEnd_4540013 := by
    simpa [prefixWord, tailWord_4540013, baseEnd_4540013] using wordTrace_append hprefix tailTrace_4540013
  have hstable : (prefixWord ++ tailWord_4540013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540013).length < 2 ^ (prefixWord ++ tailWord_4540013).sum := by decide
  have hdescent : baseEnd_4540013 < baseStart_4540013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540028 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_4540028 : Nat := 118140960795 + 4540028 * 2 ^ 59
def prefixEnd_4540028 : Nat := 4983230072969 + 3 ^ 40 * 4540028 * 2
def baseEnd_4540028 : Nat := 2331216548870668353270797

theorem tailTrace_4540028 : CollatzResearch.WordTrace tailWord_4540028 prefixEnd_4540028 2331216548870668353270797 := by
  unfold tailWord_4540028
  simp only [CollatzResearch.WordTrace]
  refine ⟨82794212398130702948374369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110392283197507603931165825 82794212398130702948374369)
  ·
    refine ⟨62095659298598027211280777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82794212398130702948374369 62095659298598027211280777)
    ·
      refine ⟨46571744473948520408460583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62095659298598027211280777 46571744473948520408460583)
      ·
        refine ⟨69857616710922780612690875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46571744473948520408460583 69857616710922780612690875)
        ·
          refine ⟨104786425066384170919036313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69857616710922780612690875 104786425066384170919036313)
          ·
            refine ⟨78589818799788128189277235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104786425066384170919036313 78589818799788128189277235)
            ·
              refine ⟨117884728199682192283915853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78589818799788128189277235 117884728199682192283915853)
              ·
                refine ⟨44206773074880822106468445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117884728199682192283915853 44206773074880822106468445)
                ·
                  refine ⟨16577539903080308289925667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44206773074880822106468445 16577539903080308289925667)
                  ·
                    refine ⟨24866309854620462434888501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16577539903080308289925667 24866309854620462434888501)
                    ·
                      refine ⟨2331216548870668353270797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24866309854620462434888501 2331216548870668353270797)
                      ·
                        rfl

theorem cell23_4540028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_4540028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540028 prefixEnd_4540028 := by exact prefixLift 4540028
  have htrace : WordTrace (prefixWord ++ tailWord_4540028) baseStart_4540028 baseEnd_4540028 := by
    simpa [prefixWord, tailWord_4540028, baseEnd_4540028] using wordTrace_append hprefix tailTrace_4540028
  have hstable : (prefixWord ++ tailWord_4540028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540028).length < 2 ^ (prefixWord ++ tailWord_4540028).sum := by decide
  have hdescent : baseEnd_4540028 < baseStart_4540028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540055 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_4540055 : Nat := 118140960795 + 4540055 * 2 ^ 59
def prefixEnd_4540055 : Nat := 4983230072969 + 3 ^ 40 * 4540055 * 2
def baseEnd_4540055 : Nat := 2331230412848339747633173

theorem tailTrace_4540055 : CollatzResearch.WordTrace tailWord_4540055 prefixEnd_4540055 2331230412848339747633173 := by
  unfold tailWord_4540055
  simp only [CollatzResearch.WordTrace]
  refine ⟨165589409567163589507981619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110392939711442393005321079 165589409567163589507981619)
  ·
    refine ⟨248384114350745384261972429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165589409567163589507981619 248384114350745384261972429)
    ·
      refine ⟨93144042881529519098239661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248384114350745384261972429 93144042881529519098239661)
      ·
        refine ⟨34929016080573569661839873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93144042881529519098239661 34929016080573569661839873)
        ·
          refine ⟨26196762060430177246379905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34929016080573569661839873 26196762060430177246379905)
          ·
            refine ⟨19647571545322632934784929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26196762060430177246379905 19647571545322632934784929)
            ·
              refine ⟨14735678658991974701088697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19647571545322632934784929 14735678658991974701088697)
              ·
                refine ⟨11051758994243981025816523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14735678658991974701088697 11051758994243981025816523)
                ·
                  refine ⟨16577638491365971538724785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11051758994243981025816523 16577638491365971538724785)
                  ·
                    refine ⟨12433228868524478654043589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16577638491365971538724785 12433228868524478654043589)
                    ·
                      refine ⟨2331230412848339747633173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12433228868524478654043589 2331230412848339747633173)
                      ·
                        rfl

theorem cell23_4540055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_4540055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540055 prefixEnd_4540055 := by exact prefixLift 4540055
  have htrace : WordTrace (prefixWord ++ tailWord_4540055) baseStart_4540055 baseEnd_4540055 := by
    simpa [prefixWord, tailWord_4540055, baseEnd_4540055] using wordTrace_append hprefix tailTrace_4540055
  have hstable : (prefixWord ++ tailWord_4540055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540055).length < 2 ^ (prefixWord ++ tailWord_4540055).sum := by decide
  have hdescent : baseEnd_4540055 < baseStart_4540055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540088 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_4540088 : Nat := 118140960795 + 4540088 * 2 ^ 59
def prefixEnd_4540088 : Nat := 4983230072969 + 3 ^ 40 * 4540088 * 2
def baseEnd_4540088 : Nat := 2331247357709938118520521

theorem tailTrace_4540088 : CollatzResearch.WordTrace tailWord_4540088 prefixEnd_4540088 2331247357709938118520521 := by
  unfold tailWord_4540088
  simp only [CollatzResearch.WordTrace]
  refine ⟨82795306588022018071966459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110393742117362690762621945 82795306588022018071966459)
  ·
    refine ⟨124192959882033027107949689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82795306588022018071966459 124192959882033027107949689)
    ·
      refine ⟨93144719911524770330962267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124192959882033027107949689 93144719911524770330962267)
      ·
        refine ⟨139717079867287155496443401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93144719911524770330962267 139717079867287155496443401)
        ·
          refine ⟨104787809900465366622332551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139717079867287155496443401 104787809900465366622332551)
          ·
            refine ⟨157181714850698049933498827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104787809900465366622332551 157181714850698049933498827)
            ·
              refine ⟨235772572276047074900248241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157181714850698049933498827 235772572276047074900248241)
              ·
                refine ⟨176829429207035306175186181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235772572276047074900248241 176829429207035306175186181)
                ·
                  refine ⟨33155517976319119907847409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176829429207035306175186181 33155517976319119907847409)
                  ·
                    refine ⟨24866638482239339930885557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33155517976319119907847409 24866638482239339930885557)
                    ·
                      refine ⟨2331247357709938118520521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24866638482239339930885557 2331247357709938118520521)
                      ·
                        rfl

theorem cell23_4540088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_4540088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540088 prefixEnd_4540088 := by exact prefixLift 4540088
  have htrace : WordTrace (prefixWord ++ tailWord_4540088) baseStart_4540088 baseEnd_4540088 := by
    simpa [prefixWord, tailWord_4540088, baseEnd_4540088] using wordTrace_append hprefix tailTrace_4540088
  have hstable : (prefixWord ++ tailWord_4540088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540088).length < 2 ^ (prefixWord ++ tailWord_4540088).sum := by decide
  have hdescent : baseEnd_4540088 < baseStart_4540088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540092 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4540092 : Nat := 118140960795 + 4540092 * 2 ^ 59
def prefixEnd_4540092 : Nat := 4983230072969 + 3 ^ 40 * 4540092 * 2
def baseEnd_4540092 : Nat := 2331249411632556102870503

theorem tailTrace_4540092 : CollatzResearch.WordTrace tailWord_4540092 prefixEnd_4540092 2331249411632556102870503 := by
  unfold tailWord_4540092
  simp only [CollatzResearch.WordTrace]
  refine ⟨82795379534014772413539265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110393839378686363218052353 82795379534014772413539265)
  ·
    refine ⟨62096534650511079310154449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82795379534014772413539265 62096534650511079310154449)
    ·
      refine ⟨46572400987883309482615837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62096534650511079310154449 46572400987883309482615837)
      ·
        refine ⟨17464650370456241055980939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46572400987883309482615837 17464650370456241055980939)
        ·
          refine ⟨26196975555684361583971409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17464650370456241055980939 26196975555684361583971409)
          ·
            refine ⟨19647731666763271187978557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26196975555684361583971409 19647731666763271187978557)
            ·
              refine ⟨7367899375036226695491959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19647731666763271187978557 7367899375036226695491959)
              ·
                refine ⟨11051849062554340043237939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7367899375036226695491959 11051849062554340043237939)
                ·
                  refine ⟨16577773593831510064856909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11051849062554340043237939 16577773593831510064856909)
                  ·
                    refine ⟨6216665097686816274321341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16577773593831510064856909 6216665097686816274321341)
                    ·
                      refine ⟨2331249411632556102870503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216665097686816274321341 2331249411632556102870503)
                      ·
                        rfl

theorem cell23_4540092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4540092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540092 prefixEnd_4540092 := by exact prefixLift 4540092
  have htrace : WordTrace (prefixWord ++ tailWord_4540092) baseStart_4540092 baseEnd_4540092 := by
    simpa [prefixWord, tailWord_4540092, baseEnd_4540092] using wordTrace_append hprefix tailTrace_4540092
  have hstable : (prefixWord ++ tailWord_4540092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540092).length < 2 ^ (prefixWord ++ tailWord_4540092).sum := by decide
  have hdescent : baseEnd_4540092 < baseStart_4540092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540165 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_4540165 : Nat := 118140960795 + 4540165 * 2 ^ 59
def prefixEnd_4540165 : Nat := 4983230072969 + 3 ^ 40 * 4540165 * 2
def baseEnd_4540165 : Nat := 2331286895720334317257667

theorem tailTrace_4540165 : CollatzResearch.WordTrace tailWord_4540165 prefixEnd_4540165 2331286895720334317257667 := by
  unfold tailWord_4540165
  simp only [CollatzResearch.WordTrace]
  refine ⟨165593421596765078294485949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110395614397843385529657299 165593421596765078294485949)
  ·
    refine ⟨62097533098786904360432231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165593421596765078294485949 62097533098786904360432231)
    ·
      refine ⟨93146299648180356540648347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62097533098786904360432231 93146299648180356540648347)
      ·
        refine ⟨139719449472270534810972521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93146299648180356540648347 139719449472270534810972521)
        ·
          refine ⟨104789587104202901108229391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139719449472270534810972521 104789587104202901108229391)
          ·
            refine ⟨157184380656304351662344087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104789587104202901108229391 157184380656304351662344087)
            ·
              refine ⟨235776570984456527493516131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157184380656304351662344087 235776570984456527493516131)
              ·
                refine ⟨353664856476684791240274197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235776570984456527493516131 353664856476684791240274197)
                ·
                  refine ⟨16578040147344599589387853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 353664856476684791240274197 16578040147344599589387853)
                  ·
                    refine ⟨6216765055254224846020445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16578040147344599589387853 6216765055254224846020445)
                    ·
                      refine ⟨2331286895720334317257667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6216765055254224846020445 2331286895720334317257667)
                      ·
                        rfl

theorem cell23_4540165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_4540165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540165 prefixEnd_4540165 := by exact prefixLift 4540165
  have htrace : WordTrace (prefixWord ++ tailWord_4540165) baseStart_4540165 baseEnd_4540165 := by
    simpa [prefixWord, tailWord_4540165, baseEnd_4540165] using wordTrace_append hprefix tailTrace_4540165
  have hstable : (prefixWord ++ tailWord_4540165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540165).length < 2 ^ (prefixWord ++ tailWord_4540165).sum := by decide
  have hdescent : baseEnd_4540165 < baseStart_4540165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540192 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4540192 : Nat := 118140960795 + 4540192 * 2 ^ 59
def prefixEnd_4540192 : Nat := 4983230072969 + 3 ^ 40 * 4540192 * 2
def baseEnd_4540192 : Nat := 2331300759698005711620043

theorem tailTrace_4540192 : CollatzResearch.WordTrace tailWord_4540192 prefixEnd_4540192 2331300759698005711620043 := by
  unfold tailWord_4540192
  simp only [CollatzResearch.WordTrace]
  refine ⟨82797203183833630952859415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110396270911778174603812553 82797203183833630952859415)
  ·
    refine ⟨124195804775750446429289123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82797203183833630952859415 124195804775750446429289123)
    ·
      refine ⟨186293707163625669643933685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124195804775750446429289123 186293707163625669643933685)
      ·
        refine ⟨17465035046589906529118783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186293707163625669643933685 17465035046589906529118783)
        ·
          refine ⟨26197552569884859793678175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17465035046589906529118783 26197552569884859793678175)
          ·
            refine ⟨39296328854827289690517263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26197552569884859793678175 39296328854827289690517263)
            ·
              refine ⟨58944493282240934535775895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39296328854827289690517263 58944493282240934535775895)
              ·
                refine ⟨88416739923361401803663843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58944493282240934535775895 88416739923361401803663843)
                ·
                  refine ⟨132625109885042102705495765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88416739923361401803663843 132625109885042102705495765)
                  ·
                    refine ⟨3108401012930674282160057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 132625109885042102705495765 3108401012930674282160057)
                    ·
                      refine ⟨2331300759698005711620043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108401012930674282160057 2331300759698005711620043)
                      ·
                        rfl

theorem cell23_4540192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4540192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540192 prefixEnd_4540192 := by exact prefixLift 4540192
  have htrace : WordTrace (prefixWord ++ tailWord_4540192) baseStart_4540192 baseEnd_4540192 := by
    simpa [prefixWord, tailWord_4540192, baseEnd_4540192] using wordTrace_append hprefix tailTrace_4540192
  have hstable : (prefixWord ++ tailWord_4540192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540192).length < 2 ^ (prefixWord ++ tailWord_4540192).sum := by decide
  have hdescent : baseEnd_4540192 < baseStart_4540192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540195 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4540195 : Nat := 118140960795 + 4540195 * 2 ^ 59
def prefixEnd_4540195 : Nat := 4983230072969 + 3 ^ 40 * 4540195 * 2
def baseEnd_4540195 : Nat := 2331302300139969199882529

theorem tailTrace_4540195 : CollatzResearch.WordTrace tailWord_4540195 prefixEnd_4540195 2331302300139969199882529 := by
  unfold tailWord_4540195
  simp only [CollatzResearch.WordTrace]
  refine ⟨165594515786656393418078039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110396343857770928945385359 165594515786656393418078039)
  ·
    refine ⟨248391773679984590127117059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165594515786656393418078039 248391773679984590127117059)
    ·
      refine ⟨372587660519976885190675589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248391773679984590127117059 372587660519976885190675589)
      ·
        refine ⟨69860186347495665973251673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372587660519976885190675589 69860186347495665973251673)
        ·
          refine ⟨52395139760621749479938755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69860186347495665973251673 52395139760621749479938755)
          ·
            refine ⟨78592709640932624219908133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52395139760621749479938755 78592709640932624219908133)
            ·
              refine ⟨14736133057674867041232775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78592709640932624219908133 14736133057674867041232775)
              ·
                refine ⟨22104199586512300561849163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14736133057674867041232775 22104199586512300561849163)
                ·
                  refine ⟨33156299379768450842773745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22104199586512300561849163 33156299379768450842773745)
                  ·
                    refine ⟨24867224534826338132080309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33156299379768450842773745 24867224534826338132080309)
                    ·
                      refine ⟨2331302300139969199882529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24867224534826338132080309 2331302300139969199882529)
                      ·
                        rfl

theorem cell23_4540195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4540195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540195 prefixEnd_4540195 := by exact prefixLift 4540195
  have htrace : WordTrace (prefixWord ++ tailWord_4540195) baseStart_4540195 baseEnd_4540195 := by
    simpa [prefixWord, tailWord_4540195, baseEnd_4540195] using wordTrace_append hprefix tailTrace_4540195
  have hstable : (prefixWord ++ tailWord_4540195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540195).length < 2 ^ (prefixWord ++ tailWord_4540195).sum := by decide
  have hdescent : baseEnd_4540195 < baseStart_4540195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540249 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 1, 4]
def baseStart_4540249 : Nat := 118140960795 + 4540249 * 2 ^ 59
def prefixEnd_4540249 : Nat := 4983230072969 + 3 ^ 40 * 4540249 * 2
def baseEnd_4540249 : Nat := 777110009365103996202427

theorem tailTrace_4540249 : CollatzResearch.WordTrace tailWord_4540249 prefixEnd_4540249 777110009365103996202427 := by
  unfold tailWord_4540249
  simp only [CollatzResearch.WordTrace]
  refine ⟨165596485328460760640543801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110397656885640507093695867 165596485328460760640543801)
  ·
    refine ⟨124197363996345570480407851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165596485328460760640543801 124197363996345570480407851)
    ·
      refine ⟨186296045994518355720611777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124197363996345570480407851 186296045994518355720611777)
      ·
        refine ⟨139722034495888766790458833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186296045994518355720611777 139722034495888766790458833)
        ·
          refine ⟨104791525871916575092844125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139722034495888766790458833 104791525871916575092844125)
          ·
            refine ⟨39296822201968715659816547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104791525871916575092844125 39296822201968715659816547)
            ·
              refine ⟨58945233302953073489724821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39296822201968715659816547 58945233302953073489724821)
              ·
                refine ⟨2763057811075925319830851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58945233302953073489724821 2763057811075925319830851)
                ·
                  refine ⟨4144586716613887979746277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763057811075925319830851 4144586716613887979746277)
                  ·
                    refine ⟨777110009365103996202427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144586716613887979746277 777110009365103996202427)
                    ·
                      rfl

theorem cell23_4540249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 4].length) (baseStart_4540249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540249 prefixEnd_4540249 := by exact prefixLift 4540249
  have htrace : WordTrace (prefixWord ++ tailWord_4540249) baseStart_4540249 baseEnd_4540249 := by
    simpa [prefixWord, tailWord_4540249, baseEnd_4540249] using wordTrace_append hprefix tailTrace_4540249
  have hstable : (prefixWord ++ tailWord_4540249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540249).length < 2 ^ (prefixWord ++ tailWord_4540249).sum := by decide
  have hdescent : baseEnd_4540249 < baseStart_4540249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540335 : List Nat := [1, 1, 2, 1, 2, 2, 3, 11]
def baseStart_4540335 : Nat := 118140960795 + 4540335 * 2 ^ 59
def prefixEnd_4540335 : Nat := 4983230072969 + 3 ^ 40 * 4540335 * 2
def baseEnd_4540335 : Nat := 86347192127096246375255

theorem tailTrace_4540335 : CollatzResearch.WordTrace tailWord_4540335 prefixEnd_4540335 86347192127096246375255 := by
  unfold tailWord_4540335
  simp only [CollatzResearch.WordTrace]
  refine ⟨165599622006149197328174459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110399748004099464885449639 165599622006149197328174459)
  ·
    refine ⟨248399433009223795992261689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165599622006149197328174459 248399433009223795992261689)
    ·
      refine ⟨186299574756917846994196267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248399433009223795992261689 186299574756917846994196267)
      ·
        refine ⟨279449362135376770491294401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186299574756917846994196267 279449362135376770491294401)
        ·
          refine ⟨209587021601532577868470801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279449362135376770491294401 209587021601532577868470801)
          ·
            refine ⟨157190266201149433401353101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209587021601532577868470801 157190266201149433401353101)
            ·
              refine ⟨58946349825431037525507413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157190266201149433401353101 58946349825431037525507413)
              ·
                refine ⟨86347192127096246375255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58946349825431037525507413 86347192127096246375255)
                ·
                  rfl

theorem cell23_4540335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 11].length) (baseStart_4540335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540335 prefixEnd_4540335 := by exact prefixLift 4540335
  have htrace : WordTrace (prefixWord ++ tailWord_4540335) baseStart_4540335 baseEnd_4540335 := by
    simpa [prefixWord, tailWord_4540335, baseEnd_4540335] using wordTrace_append hprefix tailTrace_4540335
  have hstable : (prefixWord ++ tailWord_4540335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540335).length < 2 ^ (prefixWord ++ tailWord_4540335).sum := by decide
  have hdescent : baseEnd_4540335 < baseStart_4540335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540349 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4540349 : Nat := 118140960795 + 4540349 * 2 ^ 59
def prefixEnd_4540349 : Nat := 4983230072969 + 3 ^ 40 * 4540349 * 2
def baseEnd_4540349 : Nat := 2331381376160761597356821

theorem tailTrace_4540349 : CollatzResearch.WordTrace tailWord_4540349 prefixEnd_4540349 2331381376160761597356821 := by
  unfold tailWord_4540349
  simp only [CollatzResearch.WordTrace]
  refine ⟨165600132628098477719184101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110400088418732318479456067 165600132628098477719184101)
  ·
    refine ⟨31050024867768464572347019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165600132628098477719184101 31050024867768464572347019)
    ·
      refine ⟨46575037301652696858520529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31050024867768464572347019 46575037301652696858520529)
      ·
        refine ⟨34931277976239522643890397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46575037301652696858520529 34931277976239522643890397)
        ·
          refine ⟨13099229241089820991458899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34931277976239522643890397 13099229241089820991458899)
          ·
            refine ⟨19648843861634731487188349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13099229241089820991458899 19648843861634731487188349)
            ·
              refine ⟨7368316448113024307695631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19648843861634731487188349 7368316448113024307695631)
              ·
                refine ⟨11052474672169536461543447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368316448113024307695631 11052474672169536461543447)
                ·
                  refine ⟨16578712008254304692315171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11052474672169536461543447 16578712008254304692315171)
                  ·
                    refine ⟨24868068012381457038472757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16578712008254304692315171 24868068012381457038472757)
                    ·
                      refine ⟨2331381376160761597356821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24868068012381457038472757 2331381376160761597356821)
                      ·
                        rfl

theorem cell23_4540349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4540349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540349 prefixEnd_4540349 := by exact prefixLift 4540349
  have htrace : WordTrace (prefixWord ++ tailWord_4540349) baseStart_4540349 baseEnd_4540349 := by
    simpa [prefixWord, tailWord_4540349, baseEnd_4540349] using wordTrace_append hprefix tailTrace_4540349
  have hstable : (prefixWord ++ tailWord_4540349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540349).length < 2 ^ (prefixWord ++ tailWord_4540349).sum := by decide
  have hdescent : baseEnd_4540349 < baseStart_4540349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540363 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 1, 2, 2]
def baseStart_4540363 : Nat := 118140960795 + 4540363 * 2 ^ 59
def prefixEnd_4540363 : Nat := 4983230072969 + 3 ^ 40 * 4540363 * 2
def baseEnd_4540363 : Nat := 2331388564889924542581757

theorem tailTrace_4540363 : CollatzResearch.WordTrace tailWord_4540363 prefixEnd_4540363 2331388564889924542581757 := by
  unfold tailWord_4540363
  simp only [CollatzResearch.WordTrace]
  refine ⟨165600643250047758110193743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110400428833365172073462495 165600643250047758110193743)
  ·
    refine ⟨248400964875071637165290615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165600643250047758110193743 248400964875071637165290615)
    ·
      refine ⟨372601447312607455747935923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248400964875071637165290615 372601447312607455747935923)
      ·
        refine ⟨558902170968911183621903885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372601447312607455747935923 558902170968911183621903885)
        ·
          refine ⟨209588314113341693858213957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558902170968911183621903885 209588314113341693858213957)
          ·
            refine ⟨39297808896251567598415117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209588314113341693858213957 39297808896251567598415117)
            ·
              refine ⟨14736678336094337849405669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39297808896251567598415117 14736678336094337849405669)
              ·
                refine ⟨2763127188017688346763563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14736678336094337849405669 2763127188017688346763563)
                ·
                  refine ⟨4144690782026532520145345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763127188017688346763563 4144690782026532520145345)
                  ·
                    refine ⟨3108518086519899390109009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4144690782026532520145345 3108518086519899390109009)
                    ·
                      refine ⟨2331388564889924542581757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108518086519899390109009 2331388564889924542581757)
                      ·
                        rfl

theorem cell23_4540363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 2, 2].length) (baseStart_4540363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540363 prefixEnd_4540363 := by exact prefixLift 4540363
  have htrace : WordTrace (prefixWord ++ tailWord_4540363) baseStart_4540363 baseEnd_4540363 := by
    simpa [prefixWord, tailWord_4540363, baseEnd_4540363] using wordTrace_append hprefix tailTrace_4540363
  have hstable : (prefixWord ++ tailWord_4540363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540363).length < 2 ^ (prefixWord ++ tailWord_4540363).sum := by decide
  have hdescent : baseEnd_4540363 < baseStart_4540363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540392 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4540392 : Nat := 118140960795 + 4540392 * 2 ^ 59
def prefixEnd_4540392 : Nat := 4983230072969 + 3 ^ 40 * 4540392 * 2
def baseEnd_4540392 : Nat := 2331403455828904929119123

theorem tailTrace_4540392 : CollatzResearch.WordTrace tailWord_4540392 prefixEnd_4540392 2331403455828904929119123 := by
  unfold tailWord_4540392
  simp only [CollatzResearch.WordTrace]
  refine ⟨82800850483471348031499715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110401133977961797375332953 82800850483471348031499715)
  ·
    refine ⟨124201275725207022047249573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82800850483471348031499715 124201275725207022047249573)
    ·
      refine ⟨23287739198476316633859295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124201275725207022047249573 23287739198476316633859295)
      ·
        refine ⟨34931608797714474950788943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23287739198476316633859295 34931608797714474950788943)
        ·
          refine ⟨52397413196571712426183415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34931608797714474950788943 52397413196571712426183415)
          ·
            refine ⟨78596119794857568639275123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52397413196571712426183415 78596119794857568639275123)
            ·
              refine ⟨117894179692286352958912685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78596119794857568639275123 117894179692286352958912685)
              ·
                refine ⟨44210317384607382359592257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117894179692286352958912685 44210317384607382359592257)
                ·
                  refine ⟨33157738038455536769694193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44210317384607382359592257 33157738038455536769694193)
                  ·
                    refine ⟨24868303528841652577270645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33157738038455536769694193 24868303528841652577270645)
                    ·
                      refine ⟨2331403455828904929119123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24868303528841652577270645 2331403455828904929119123)
                      ·
                        rfl

theorem cell23_4540392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4540392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540392 prefixEnd_4540392 := by exact prefixLift 4540392
  have htrace : WordTrace (prefixWord ++ tailWord_4540392) baseStart_4540392 baseEnd_4540392 := by
    simpa [prefixWord, tailWord_4540392, baseEnd_4540392] using wordTrace_append hprefix tailTrace_4540392
  have hstable : (prefixWord ++ tailWord_4540392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540392).length < 2 ^ (prefixWord ++ tailWord_4540392).sum := by decide
  have hdescent : baseEnd_4540392 < baseStart_4540392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540397 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4540397 : Nat := 118140960795 + 4540397 * 2 ^ 59
def prefixEnd_4540397 : Nat := 4983230072969 + 3 ^ 40 * 4540397 * 2
def baseEnd_4540397 : Nat := 2331406023232177409556601

theorem tailTrace_4540397 : CollatzResearch.WordTrace tailWord_4540397 prefixEnd_4540397 2331406023232177409556601 := by
  unfold tailWord_4540397
  simp only [CollatzResearch.WordTrace]
  refine ⟨165601883331924581916931445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110401255554616387944620963 165601883331924581916931445)
  ·
    refine ⟨15525176562367929554712323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165601883331924581916931445 15525176562367929554712323)
    ·
      refine ⟨23287764843551894332068485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15525176562367929554712323 23287764843551894332068485)
      ·
        refine ⟨4366455908165980187262841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23287764843551894332068485 4366455908165980187262841)
        ·
          refine ⟨3274841931124485140447131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4366455908165980187262841 3274841931124485140447131)
          ·
            refine ⟨4912262896686727710670697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3274841931124485140447131 4912262896686727710670697)
            ·
              refine ⟨3684197172515045783003023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4912262896686727710670697 3684197172515045783003023)
              ·
                refine ⟨5526295758772568674504535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684197172515045783003023 5526295758772568674504535)
                ·
                  refine ⟨8289443638158853011756803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526295758772568674504535 8289443638158853011756803)
                  ·
                    refine ⟨12434165457238279517635205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8289443638158853011756803 12434165457238279517635205)
                    ·
                      refine ⟨2331406023232177409556601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12434165457238279517635205 2331406023232177409556601)
                      ·
                        rfl

theorem cell23_4540397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4540397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540397 prefixEnd_4540397 := by exact prefixLift 4540397
  have htrace : WordTrace (prefixWord ++ tailWord_4540397) baseStart_4540397 baseEnd_4540397 := by
    simpa [prefixWord, tailWord_4540397, baseEnd_4540397] using wordTrace_append hprefix tailTrace_4540397
  have hstable : (prefixWord ++ tailWord_4540397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540397).length < 2 ^ (prefixWord ++ tailWord_4540397).sum := by decide
  have hdescent : baseEnd_4540397 < baseStart_4540397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540412 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_4540412 : Nat := 118140960795 + 4540412 * 2 ^ 59
def prefixEnd_4540412 : Nat := 4983230072969 + 3 ^ 40 * 4540412 * 2
def baseEnd_4540412 : Nat := 777137908480664950289677

theorem tailTrace_4540412 : CollatzResearch.WordTrace tailWord_4540412 prefixEnd_4540412 777137908480664950289677 := by
  unfold tailWord_4540412
  simp only [CollatzResearch.WordTrace]
  refine ⟨82801215213435119739363745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110401620284580159652484993 82801215213435119739363745)
  ·
    refine ⟨62100911410076339804522809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82801215213435119739363745 62100911410076339804522809)
    ·
      refine ⟨46575683557557254853392107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62100911410076339804522809 46575683557557254853392107)
      ·
        refine ⟨69863525336335882280088161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46575683557557254853392107 69863525336335882280088161)
        ·
          refine ⟨52397644002251911710066121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69863525336335882280088161 52397644002251911710066121)
          ·
            refine ⟨39298233001688933782549591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52397644002251911710066121 39298233001688933782549591)
            ·
              refine ⟨58947349502533400673824387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39298233001688933782549591 58947349502533400673824387)
              ·
                refine ⟨88421024253800101010736581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58947349502533400673824387 88421024253800101010736581)
                ·
                  refine ⟨16578942047587518939513109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88421024253800101010736581 16578942047587518939513109)
                  ·
                    refine ⟨777137908480664950289677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16578942047587518939513109 777137908480664950289677)
                    ·
                      rfl

theorem cell23_4540412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_4540412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540412 prefixEnd_4540412 := by exact prefixLift 4540412
  have htrace : WordTrace (prefixWord ++ tailWord_4540412) baseStart_4540412 baseEnd_4540412 := by
    simpa [prefixWord, tailWord_4540412, baseEnd_4540412] using wordTrace_append hprefix tailTrace_4540412
  have hstable : (prefixWord ++ tailWord_4540412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540412).length < 2 ^ (prefixWord ++ tailWord_4540412).sum := by decide
  have hdescent : baseEnd_4540412 < baseStart_4540412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540419 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 3, 4, 2]
def baseStart_4540419 : Nat := 118140960795 + 4540419 * 2 ^ 59
def prefixEnd_4540419 : Nat := 4983230072969 + 3 ^ 40 * 4540419 * 2
def baseEnd_4540419 : Nat := 2331417319806576323481499

theorem tailTrace_4540419 : CollatzResearch.WordTrace tailWord_4540419 prefixEnd_4540419 2331417319806576323481499 := by
  unfold tailWord_4540419
  simp only [CollatzResearch.WordTrace]
  refine ⟨165602685737844879674232311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110401790491896586449488207 165602685737844879674232311)
  ·
    refine ⟨248404028606767319511348467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165602685737844879674232311 248404028606767319511348467)
    ·
      refine ⟨372606042910150979267022701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248404028606767319511348467 372606042910150979267022701)
      ·
        refine ⟨139727266091306617225133513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372606042910150979267022701 139727266091306617225133513)
        ·
          refine ⟨104795449568479962918850135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139727266091306617225133513 104795449568479962918850135)
          ·
            refine ⟨157193174352719944378275203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104795449568479962918850135 157193174352719944378275203)
            ·
              refine ⟨235789761529079916567412805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157193174352719944378275203 235789761529079916567412805)
              ·
                refine ⟨44210580286702484356389901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235789761529079916567412805 44210580286702484356389901)
                ·
                  refine ⟨16578967607513431633646213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44210580286702484356389901 16578967607513431633646213)
                  ·
                    refine ⟨3108556426408768431308665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16578967607513431633646213 3108556426408768431308665)
                    ·
                      refine ⟨2331417319806576323481499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108556426408768431308665 2331417319806576323481499)
                      ·
                        rfl

theorem cell23_4540419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_4540419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540419 prefixEnd_4540419 := by exact prefixLift 4540419
  have htrace : WordTrace (prefixWord ++ tailWord_4540419) baseStart_4540419 baseEnd_4540419 := by
    simpa [prefixWord, tailWord_4540419, baseEnd_4540419] using wordTrace_append hprefix tailTrace_4540419
  have hstable : (prefixWord ++ tailWord_4540419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540419).length < 2 ^ (prefixWord ++ tailWord_4540419).sum := by decide
  have hdescent : baseEnd_4540419 < baseStart_4540419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540459 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 5]
def baseStart_4540459 : Nat := 118140960795 + 4540459 * 2 ^ 59
def prefixEnd_4540459 : Nat := 4983230072969 + 3 ^ 40 * 4540459 * 2
def baseEnd_4540459 : Nat := 259048651003639574109035

theorem tailTrace_4540459 : CollatzResearch.WordTrace tailWord_4540459 prefixEnd_4540459 259048651003639574109035 := by
  unfold tailWord_4540459
  simp only [CollatzResearch.WordTrace]
  refine ⟨165604144657699966505688431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110402763105133311003792287 165604144657699966505688431)
  ·
    refine ⟨248406216986549949758532647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165604144657699966505688431 248406216986549949758532647)
    ·
      refine ⟨372609325479824924637798971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248406216986549949758532647 372609325479824924637798971)
      ·
        refine ⟨558913988219737386956698457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372609325479824924637798971 558913988219737386956698457)
        ·
          refine ⟨419185491164803040217523843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558913988219737386956698457 419185491164803040217523843)
          ·
            refine ⟨628778236747204560326285765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419185491164803040217523843 628778236747204560326285765)
            ·
              refine ⟨117895919390100855061178581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 628778236747204560326285765 117895919390100855061178581)
              ·
                refine ⟨2763185610705488790496373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117895919390100855061178581 2763185610705488790496373)
                ·
                  refine ⟨259048651003639574109035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763185610705488790496373 259048651003639574109035)
                  ·
                    rfl

theorem cell23_4540459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 5].length) (baseStart_4540459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540459 prefixEnd_4540459 := by exact prefixLift 4540459
  have htrace : WordTrace (prefixWord ++ tailWord_4540459) baseStart_4540459 baseEnd_4540459 := by
    simpa [prefixWord, tailWord_4540459, baseEnd_4540459] using wordTrace_append hprefix tailTrace_4540459
  have hstable : (prefixWord ++ tailWord_4540459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540459).length < 2 ^ (prefixWord ++ tailWord_4540459).sum := by decide
  have hdescent : baseEnd_4540459 < baseStart_4540459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540469 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_4540469 : Nat := 118140960795 + 4540469 * 2 ^ 59
def prefixEnd_4540469 : Nat := 4983230072969 + 3 ^ 40 * 4540469 * 2
def baseEnd_4540469 : Nat := 2331442993839301127856269

theorem tailTrace_4540469 : CollatzResearch.WordTrace tailWord_4540469 prefixEnd_4540469 2331442993839301127856269 := by
  unfold tailWord_4540469
  simp only [CollatzResearch.WordTrace]
  refine ⟨165604509387663738213552461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110403006258442492142368307 165604509387663738213552461)
  ·
    refine ⟨62101691020373901830082173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165604509387663738213552461 62101691020373901830082173)
    ·
      refine ⟨23288134132640213186280815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62101691020373901830082173 23288134132640213186280815)
      ·
        refine ⟨34932201198960319779421223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23288134132640213186280815 34932201198960319779421223)
        ·
          refine ⟨52398301798440479669131835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34932201198960319779421223 52398301798440479669131835)
          ·
            refine ⟨78597452697660719503697753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52398301798440479669131835 78597452697660719503697753)
            ·
              refine ⟨58948089523245539627773315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78597452697660719503697753 58948089523245539627773315)
              ·
                refine ⟨88422134284868309441659973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58948089523245539627773315 88422134284868309441659973)
                ·
                  refine ⟨16579150178412808020311245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88422134284868309441659973 16579150178412808020311245)
                  ·
                    refine ⟨6217181316904803007616717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16579150178412808020311245 6217181316904803007616717)
                    ·
                      refine ⟨2331442993839301127856269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6217181316904803007616717 2331442993839301127856269)
                      ·
                        rfl

theorem cell23_4540469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_4540469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540469 prefixEnd_4540469 := by exact prefixLift 4540469
  have htrace : WordTrace (prefixWord ++ tailWord_4540469) baseStart_4540469 baseEnd_4540469 := by
    simpa [prefixWord, tailWord_4540469, baseEnd_4540469] using wordTrace_append hprefix tailTrace_4540469
  have hstable : (prefixWord ++ tailWord_4540469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540469).length < 2 ^ (prefixWord ++ tailWord_4540469).sum := by decide
  have hdescent : baseEnd_4540469 < baseStart_4540469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540470 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4540470 : Nat := 118140960795 + 4540470 * 2 ^ 59
def prefixEnd_4540470 : Nat := 4983230072969 + 3 ^ 40 * 4540470 * 2
def baseEnd_4540470 : Nat := 2331443507319955623943765

theorem tailTrace_4540470 : CollatzResearch.WordTrace tailWord_4540470 prefixEnd_4540470 2331443507319955623943765 := by
  unfold tailWord_4540470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350284116291257211521179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110403030573773410256225909 10350284116291257211521179)
  ·
    refine ⟨15525426174436885817281769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10350284116291257211521179 15525426174436885817281769)
    ·
      refine ⟨11644069630827664362961327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15525426174436885817281769 11644069630827664362961327)
      ·
        refine ⟨17466104446241496544441991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644069630827664362961327 17466104446241496544441991)
        ·
          refine ⟨26199156669362244816662987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17466104446241496544441991 26199156669362244816662987)
          ·
            refine ⟨39298735004043367224994481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26199156669362244816662987 39298735004043367224994481)
            ·
              refine ⟨29474051253032525418745861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39298735004043367224994481 29474051253032525418745861)
              ·
                refine ⟨5526384609943598516014849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29474051253032525418745861 5526384609943598516014849)
                ·
                  refine ⟨4144788457457698887011137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5526384609943598516014849 4144788457457698887011137)
                  ·
                    refine ⟨3108591343093274165258353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4144788457457698887011137 3108591343093274165258353)
                    ·
                      refine ⟨2331443507319955623943765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108591343093274165258353 2331443507319955623943765)
                      ·
                        rfl

theorem cell23_4540470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4540470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540470 prefixEnd_4540470 := by exact prefixLift 4540470
  have htrace : WordTrace (prefixWord ++ tailWord_4540470) baseStart_4540470 baseEnd_4540470 := by
    simpa [prefixWord, tailWord_4540470, baseEnd_4540470] using wordTrace_append hprefix tailTrace_4540470
  have hstable : (prefixWord ++ tailWord_4540470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540470).length < 2 ^ (prefixWord ++ tailWord_4540470).sum := by decide
  have hdescent : baseEnd_4540470 < baseStart_4540470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540526 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4540526 : Nat := 118140960795 + 4540526 * 2 ^ 59
def prefixEnd_4540526 : Nat := 4983230072969 + 3 ^ 40 * 4540526 * 2
def baseEnd_4540526 : Nat := 2331472262236607404843507

theorem tailTrace_4540526 : CollatzResearch.WordTrace tailWord_4540526 prefixEnd_4540526 2331472262236607404843507 := by
  unfold tailWord_4540526
  simp only [CollatzResearch.WordTrace]
  refine ⟨20700823543557154618547179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110404392232304824632251621 20700823543557154618547179)
  ·
    refine ⟨31051235315335731927820769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20700823543557154618547179 31051235315335731927820769)
    ·
      refine ⟨23288426486501798945865577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31051235315335731927820769 23288426486501798945865577)
      ·
        refine ⟨17466319864876349209399183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23288426486501798945865577 17466319864876349209399183)
        ·
          refine ⟨26199479797314523814098775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17466319864876349209399183 26199479797314523814098775)
          ·
            refine ⟨39299219695971785721148163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26199479797314523814098775 39299219695971785721148163)
            ·
              refine ⟨58948829543957678581722245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39299219695971785721148163 58948829543957678581722245)
              ·
                refine ⟨11052905539492064734072921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58948829543957678581722245 11052905539492064734072921)
                ·
                  refine ⟨8289679154619048550554691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11052905539492064734072921 8289679154619048550554691)
                  ·
                    refine ⟨12434518731928572825832037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8289679154619048550554691 12434518731928572825832037)
                    ·
                      refine ⟨2331472262236607404843507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12434518731928572825832037 2331472262236607404843507)
                      ·
                        rfl

theorem cell23_4540526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4540526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540526 prefixEnd_4540526 := by exact prefixLift 4540526
  have htrace : WordTrace (prefixWord ++ tailWord_4540526) baseStart_4540526 baseEnd_4540526 := by
    simpa [prefixWord, tailWord_4540526, baseEnd_4540526] using wordTrace_append hprefix tailTrace_4540526
  have hstable : (prefixWord ++ tailWord_4540526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540526).length < 2 ^ (prefixWord ++ tailWord_4540526).sum := by decide
  have hdescent : baseEnd_4540526 < baseStart_4540526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540616 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_4540616 : Nat := 118140960795 + 4540616 * 2 ^ 59
def prefixEnd_4540616 : Nat := 4983230072969 + 3 ^ 40 * 4540616 * 2
def baseEnd_4540616 : Nat := 2331518475495512052718093

theorem tailTrace_4540616 : CollatzResearch.WordTrace tailWord_4540616 prefixEnd_4540616 2331518475495512052718093 := by
  unfold tailWord_4540616
  simp only [CollatzResearch.WordTrace]
  refine ⟨82804935459065591159576851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110406580612087454879435801 82804935459065591159576851)
  ·
    refine ⟨124207403188598386739365277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82804935459065591159576851 124207403188598386739365277)
    ·
      refine ⟨46577776195724395027261979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124207403188598386739365277 46577776195724395027261979)
      ·
        refine ⟨69866664293586592540892969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46577776195724395027261979 69866664293586592540892969)
        ·
          refine ⟨52399998220189944405669727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69866664293586592540892969 52399998220189944405669727)
          ·
            refine ⟨78599997330284916608504591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52399998220189944405669727 78599997330284916608504591)
            ·
              refine ⟨117899995995427374912756887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78599997330284916608504591 117899995995427374912756887)
              ·
                refine ⟨176849993993141062369135331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117899995995427374912756887 176849993993141062369135331)
                ·
                  refine ⟨265274990989711593553702997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176849993993141062369135331 265274990989711593553702997)
                  ·
                    refine ⟨3108691300660682736957457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 265274990989711593553702997 3108691300660682736957457)
                    ·
                      refine ⟨2331518475495512052718093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108691300660682736957457 2331518475495512052718093)
                      ·
                        rfl

theorem cell23_4540616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_4540616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540616 prefixEnd_4540616 := by exact prefixLift 4540616
  have htrace : WordTrace (prefixWord ++ tailWord_4540616) baseStart_4540616 baseEnd_4540616 := by
    simpa [prefixWord, tailWord_4540616, baseEnd_4540616] using wordTrace_append hprefix tailTrace_4540616
  have hstable : (prefixWord ++ tailWord_4540616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540616).length < 2 ^ (prefixWord ++ tailWord_4540616).sum := by decide
  have hdescent : baseEnd_4540616 < baseStart_4540616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540619 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_4540619 : Nat := 118140960795 + 4540619 * 2 ^ 59
def prefixEnd_4540619 : Nat := 4983230072969 + 3 ^ 40 * 4540619 * 2
def baseEnd_4540619 : Nat := 2331520015937475540980579

theorem tailTrace_4540619 : CollatzResearch.WordTrace tailWord_4540619 prefixEnd_4540619 2331520015937475540980579 := by
  unfold tailWord_4540619
  simp only [CollatzResearch.WordTrace]
  refine ⟨165609980337120313831512911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110406653558080209221008607 165609980337120313831512911)
  ·
    refine ⟨248414970505680470747269367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165609980337120313831512911 248414970505680470747269367)
    ·
      refine ⟨372622455758520706120904051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248414970505680470747269367 372622455758520706120904051)
      ·
        refine ⟨558933683637781059181356077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372622455758520706120904051 558933683637781059181356077)
        ·
          refine ⟨209600131364167897193008529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558933683637781059181356077 209600131364167897193008529)
          ·
            refine ⟨157200098523125922894756397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209600131364167897193008529 157200098523125922894756397)
            ·
              refine ⟨58950036946172221085533649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157200098523125922894756397 58950036946172221085533649)
              ·
                refine ⟨44212527709629165814150237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58950036946172221085533649 44212527709629165814150237)
                ·
                  refine ⟨16579697891110937180306339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44212527709629165814150237 16579697891110937180306339)
                  ·
                    refine ⟨24869546836666405770459509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16579697891110937180306339 24869546836666405770459509)
                    ·
                      refine ⟨2331520015937475540980579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24869546836666405770459509 2331520015937475540980579)
                      ·
                        rfl

theorem cell23_4540619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_4540619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540619 prefixEnd_4540619 := by exact prefixLift 4540619
  have htrace : WordTrace (prefixWord ++ tailWord_4540619) baseStart_4540619 baseEnd_4540619 := by
    simpa [prefixWord, tailWord_4540619, baseEnd_4540619] using wordTrace_append hprefix tailTrace_4540619
  have hstable : (prefixWord ++ tailWord_4540619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540619).length < 2 ^ (prefixWord ++ tailWord_4540619).sum := by decide
  have hdescent : baseEnd_4540619 < baseStart_4540619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540630 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4540630 : Nat := 118140960795 + 4540630 * 2 ^ 59
def prefixEnd_4540630 : Nat := 4983230072969 + 3 ^ 40 * 4540630 * 2
def baseEnd_4540630 : Nat := 777175221408224999314343

theorem tailTrace_4540630 : CollatzResearch.WordTrace tailWord_4540630 prefixEnd_4540630 777175221408224999314343 := by
  unfold tailWord_4540630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350648846255028919385209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110406921026720308473442229 10350648846255028919385209)
  ·
    refine ⟨7762986634691271689538907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10350648846255028919385209 7762986634691271689538907)
    ·
      refine ⟨11644479952036907534308361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7762986634691271689538907 11644479952036907534308361)
      ·
        refine ⟨8733359964027680650731271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11644479952036907534308361 8733359964027680650731271)
        ·
          refine ⟨13100039946041520976096907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733359964027680650731271 13100039946041520976096907)
          ·
            refine ⟨19650059919062281464145361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13100039946041520976096907 19650059919062281464145361)
            ·
              refine ⟨14737544939296711098109021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19650059919062281464145361 14737544939296711098109021)
              ·
                refine ⟨5526579352236266661790883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14737544939296711098109021 5526579352236266661790883)
                ·
                  refine ⟨8289869028354399992686325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526579352236266661790883 8289869028354399992686325)
                  ·
                    refine ⟨777175221408224999314343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8289869028354399992686325 777175221408224999314343)
                    ·
                      rfl

theorem cell23_4540630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4540630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540630 prefixEnd_4540630 := by exact prefixLift 4540630
  have htrace : WordTrace (prefixWord ++ tailWord_4540630) baseStart_4540630 baseEnd_4540630 := by
    simpa [prefixWord, tailWord_4540630, baseEnd_4540630] using wordTrace_append hprefix tailTrace_4540630
  have hstable : (prefixWord ++ tailWord_4540630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540630).length < 2 ^ (prefixWord ++ tailWord_4540630).sum := by decide
  have hdescent : baseEnd_4540630 < baseStart_4540630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540633 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 5, 2, 2]
def baseStart_4540633 : Nat := 118140960795 + 4540633 * 2 ^ 59
def prefixEnd_4540633 : Nat := 4983230072969 + 3 ^ 40 * 4540633 * 2
def baseEnd_4540633 : Nat := 2331527204666638486205515

theorem tailTrace_4540633 : CollatzResearch.WordTrace tailWord_4540633 prefixEnd_4540633 2331527204666638486205515 := by
  unfold tailWord_4540633
  simp only [CollatzResearch.WordTrace]
  refine ⟨165610490959069594222522553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110406993972713062815015035 165610490959069594222522553)
  ·
    refine ⟨124207868219302195666891915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165610490959069594222522553 124207868219302195666891915)
    ·
      refine ⟨186311802328953293500337873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124207868219302195666891915 186311802328953293500337873)
      ·
        refine ⟨139733851746714970125253405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186311802328953293500337873 139733851746714970125253405)
        ·
          refine ⟨52400194405018113796970027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139733851746714970125253405 52400194405018113796970027)
          ·
            refine ⟨78600291607527170695455041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52400194405018113796970027 78600291607527170695455041)
            ·
              refine ⟨58950218705645378021591281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78600291607527170695455041 58950218705645378021591281)
              ·
                refine ⟨44212664029234033516193461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58950218705645378021591281 44212664029234033516193461)
                ·
                  refine ⟨4144937252740690642143137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44212664029234033516193461 4144937252740690642143137)
                  ·
                    refine ⟨3108702939555517981607353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4144937252740690642143137 3108702939555517981607353)
                    ·
                      refine ⟨2331527204666638486205515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108702939555517981607353 2331527204666638486205515)
                      ·
                        rfl

theorem cell23_4540633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_4540633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540633 prefixEnd_4540633 := by exact prefixLift 4540633
  have htrace : WordTrace (prefixWord ++ tailWord_4540633) baseStart_4540633 baseEnd_4540633 := by
    simpa [prefixWord, tailWord_4540633, baseEnd_4540633] using wordTrace_append hprefix tailTrace_4540633
  have hstable : (prefixWord ++ tailWord_4540633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540633).length < 2 ^ (prefixWord ++ tailWord_4540633).sum := by decide
  have hdescent : baseEnd_4540633 < baseStart_4540633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540659 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_4540659 : Nat := 118140960795 + 4540659 * 2 ^ 59
def prefixEnd_4540659 : Nat := 4983230072969 + 3 ^ 40 * 4540659 * 2
def baseEnd_4540659 : Nat := 2331540555163655384480395

theorem tailTrace_4540659 : CollatzResearch.WordTrace tailWord_4540659 prefixEnd_4540659 2331540555163655384480395 := by
  unfold tailWord_4540659
  simp only [CollatzResearch.WordTrace]
  refine ⟨165611439256975400662969031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110407626171316933775312687 165611439256975400662969031)
  ·
    refine ⟨248417158885463100994453547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165611439256975400662969031 248417158885463100994453547)
    ·
      refine ⟨372625738328194651491680321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248417158885463100994453547 372625738328194651491680321)
      ·
        refine ⟨279469303746145988618760241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372625738328194651491680321 279469303746145988618760241)
        ·
          refine ⟨209601977809609491464070181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279469303746145988618760241 209601977809609491464070181)
          ·
            refine ⟨39300370839301779649513159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209601977809609491464070181 39300370839301779649513159)
            ·
              refine ⟨58950556258952669474269739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39300370839301779649513159 58950556258952669474269739)
              ·
                refine ⟨88425834388429004211404609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58950556258952669474269739 88425834388429004211404609)
                ·
                  refine ⟨66319375791321753158553457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88425834388429004211404609 66319375791321753158553457)
                  ·
                    refine ⟨49739531843491314868915093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66319375791321753158553457 49739531843491314868915093)
                    ·
                      refine ⟨2331540555163655384480395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49739531843491314868915093 2331540555163655384480395)
                      ·
                        rfl

theorem cell23_4540659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_4540659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540659 prefixEnd_4540659 := by exact prefixLift 4540659
  have htrace : WordTrace (prefixWord ++ tailWord_4540659) baseStart_4540659 baseEnd_4540659 := by
    simpa [prefixWord, tailWord_4540659, baseEnd_4540659] using wordTrace_append hprefix tailTrace_4540659
  have hstable : (prefixWord ++ tailWord_4540659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540659).length < 2 ^ (prefixWord ++ tailWord_4540659).sum := by decide
  have hdescent : baseEnd_4540659 < baseStart_4540659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540717 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4540717 : Nat := 118140960795 + 4540717 * 2 ^ 59
def prefixEnd_4540717 : Nat := 4983230072969 + 3 ^ 40 * 4540717 * 2
def baseEnd_4540717 : Nat := 2331570337041616157555129

theorem tailTrace_4540717 : CollatzResearch.WordTrace tailWord_4540717 prefixEnd_4540717 2331570337041616157555129 := by
  unfold tailWord_4540717
  simp only [CollatzResearch.WordTrace]
  refine ⟨165613554690765276568580405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110409036460510184379053603 165613554690765276568580405)
  ·
    refine ⟨15526270752259244678304413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165613554690765276568580405 15526270752259244678304413)
    ·
      refine ⟨5822351532097216754364155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15526270752259244678304413 5822351532097216754364155)
      ·
        refine ⟨8733527298145825131546233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822351532097216754364155 8733527298145825131546233)
        ·
          refine ⟨6550145473609368848659675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8733527298145825131546233 6550145473609368848659675)
          ·
            refine ⟨9825218210414053272989513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550145473609368848659675 9825218210414053272989513)
            ·
              refine ⟨7368913657810539954742135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9825218210414053272989513 7368913657810539954742135)
              ·
                refine ⟨11053370486715809932113203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368913657810539954742135 11053370486715809932113203)
                ·
                  refine ⟨16580055730073714898169805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11053370486715809932113203 16580055730073714898169805)
                  ·
                    refine ⟨6217520898777643086813677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16580055730073714898169805 6217520898777643086813677)
                    ·
                      refine ⟨2331570337041616157555129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6217520898777643086813677 2331570337041616157555129)
                      ·
                        rfl

theorem cell23_4540717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4540717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540717 prefixEnd_4540717 := by exact prefixLift 4540717
  have htrace : WordTrace (prefixWord ++ tailWord_4540717) baseStart_4540717 baseEnd_4540717 := by
    simpa [prefixWord, tailWord_4540717, baseEnd_4540717] using wordTrace_append hprefix tailTrace_4540717
  have hstable : (prefixWord ++ tailWord_4540717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540717).length < 2 ^ (prefixWord ++ tailWord_4540717).sum := by decide
  have hdescent : baseEnd_4540717 < baseStart_4540717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540757 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_4540757 : Nat := 118140960795 + 4540757 * 2 ^ 59
def prefixEnd_4540757 : Nat := 4983230072969 + 3 ^ 40 * 4540757 * 2
def baseEnd_4540757 : Nat := 2331590876267796001054945

theorem tailTrace_4540757 : CollatzResearch.WordTrace tailWord_4540757 prefixEnd_4540757 2331590876267796001054945 := by
  unfold tailWord_4540757
  simp only [CollatzResearch.WordTrace]
  refine ⟨165615013610620363400036525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110410009073746908933357683 165615013610620363400036525)
  ·
    refine ⟨62105630103982636275013697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165615013610620363400036525 62105630103982636275013697)
    ·
      refine ⟨46579222577986977206260273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62105630103982636275013697 46579222577986977206260273)
      ·
        refine ⟨34934416933490232904695205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46579222577986977206260273 34934416933490232904695205)
        ·
          refine ⟨6550203175029418669630351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34934416933490232904695205 6550203175029418669630351)
          ·
            refine ⟨9825304762544128004445527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550203175029418669630351 9825304762544128004445527)
            ·
              refine ⟨14737957143816192006668291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825304762544128004445527 14737957143816192006668291)
              ·
                refine ⟨22106935715724288010002437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14737957143816192006668291 22106935715724288010002437)
                ·
                  refine ⟨4145050446698304001875457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22106935715724288010002437 4145050446698304001875457)
                  ·
                    refine ⟨3108787835023728001406593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4145050446698304001875457 3108787835023728001406593)
                    ·
                      refine ⟨2331590876267796001054945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108787835023728001406593 2331590876267796001054945)
                      ·
                        rfl

theorem cell23_4540757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_4540757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540757 prefixEnd_4540757 := by exact prefixLift 4540757
  have htrace : WordTrace (prefixWord ++ tailWord_4540757) baseStart_4540757 baseEnd_4540757 := by
    simpa [prefixWord, tailWord_4540757, baseEnd_4540757] using wordTrace_append hprefix tailTrace_4540757
  have hstable : (prefixWord ++ tailWord_4540757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540757).length < 2 ^ (prefixWord ++ tailWord_4540757).sum := by decide
  have hdescent : baseEnd_4540757 < baseStart_4540757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540773 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_4540773 : Nat := 118140960795 + 4540773 * 2 ^ 59
def prefixEnd_4540773 : Nat := 4983230072969 + 3 ^ 40 * 4540773 * 2
def baseEnd_4540773 : Nat := 2331599091958267938454871

theorem tailTrace_4540773 : CollatzResearch.WordTrace tailWord_4540773 prefixEnd_4540773 2331599091958267938454871 := by
  unfold tailWord_4540773
  simp only [CollatzResearch.WordTrace]
  refine ⟨165615597178562398132618973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110410398119041598755079315 165615597178562398132618973)
  ·
    refine ⟨62105848941960899299732115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165615597178562398132618973 62105848941960899299732115)
    ·
      refine ⟨93158773412941348949598173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62105848941960899299732115 93158773412941348949598173)
      ·
        refine ⟨34934540029853005856099315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93158773412941348949598173 34934540029853005856099315)
        ·
          refine ⟨52401810044779508784148973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34934540029853005856099315 52401810044779508784148973)
          ·
            refine ⟨19650678766792315794055865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52401810044779508784148973 19650678766792315794055865)
            ·
              refine ⟨14738009075094236845541899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19650678766792315794055865 14738009075094236845541899)
              ·
                refine ⟨22107013612641355268312849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14738009075094236845541899 22107013612641355268312849)
                ·
                  refine ⟨16580260209481016451234637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22107013612641355268312849 16580260209481016451234637)
                  ·
                    refine ⟨6217597578555381169212989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16580260209481016451234637 6217597578555381169212989)
                    ·
                      refine ⟨2331599091958267938454871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6217597578555381169212989 2331599091958267938454871)
                      ·
                        rfl

theorem cell23_4540773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_4540773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540773 prefixEnd_4540773 := by exact prefixLift 4540773
  have htrace : WordTrace (prefixWord ++ tailWord_4540773) baseStart_4540773 baseEnd_4540773 := by
    simpa [prefixWord, tailWord_4540773, baseEnd_4540773] using wordTrace_append hprefix tailTrace_4540773
  have hstable : (prefixWord ++ tailWord_4540773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540773).length < 2 ^ (prefixWord ++ tailWord_4540773).sum := by decide
  have hdescent : baseEnd_4540773 < baseStart_4540773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540820 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4540820 : Nat := 118140960795 + 4540820 * 2 ^ 59
def prefixEnd_4540820 : Nat := 4983230072969 + 3 ^ 40 * 4540820 * 2
def baseEnd_4540820 : Nat := 2331623225549029254567155

theorem tailTrace_4540820 : CollatzResearch.WordTrace tailWord_4540820 prefixEnd_4540820 2331623225549029254567155 := by
  unfold tailWord_4540820
  simp only [CollatzResearch.WordTrace]
  refine ⟨82808655704696062579789957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110411540939594750106386609 82808655704696062579789957)
  ·
    refine ⟨15526622944630511733710617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82808655704696062579789957 15526622944630511733710617)
    ·
      refine ⟨11644967208472883800282963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15526622944630511733710617 11644967208472883800282963)
      ·
        refine ⟨17467450812709325700424445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644967208472883800282963 17467450812709325700424445)
        ·
          refine ⟨6550294054765997137659167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17467450812709325700424445 6550294054765997137659167)
          ·
            refine ⟨9825441082148995706488751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550294054765997137659167 9825441082148995706488751)
            ·
              refine ⟨14738161623223493559733127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825441082148995706488751 14738161623223493559733127)
              ·
                refine ⟨22107242434835240339599691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14738161623223493559733127 22107242434835240339599691)
                ·
                  refine ⟨33160863652252860509399537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22107242434835240339599691 33160863652252860509399537)
                  ·
                    refine ⟨24870647739189645382049653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33160863652252860509399537 24870647739189645382049653)
                    ·
                      refine ⟨2331623225549029254567155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24870647739189645382049653 2331623225549029254567155)
                      ·
                        rfl

theorem cell23_4540820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4540820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540820 prefixEnd_4540820 := by exact prefixLift 4540820
  have htrace : WordTrace (prefixWord ++ tailWord_4540820) baseStart_4540820 baseEnd_4540820 := by
    simpa [prefixWord, tailWord_4540820, baseEnd_4540820] using wordTrace_append hprefix tailTrace_4540820
  have hstable : (prefixWord ++ tailWord_4540820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540820).length < 2 ^ (prefixWord ++ tailWord_4540820).sum := by decide
  have hdescent : baseEnd_4540820 < baseStart_4540820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540850 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_4540850 : Nat := 118140960795 + 4540850 * 2 ^ 59
def prefixEnd_4540850 : Nat := 4983230072969 + 3 ^ 40 * 4540850 * 2
def baseEnd_4540850 : Nat := 2331638629968664137192017

theorem tailTrace_4540850 : CollatzResearch.WordTrace tailWord_4540850 prefixEnd_4540850 2331638629968664137192017 := by
  unfold tailWord_4540850
  simp only [CollatzResearch.WordTrace]
  refine ⟨41404601399820860070793001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110412270399522293522114669 41404601399820860070793001)
  ·
    refine ⟨31053451049865645053094751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41404601399820860070793001 31053451049865645053094751)
    ·
      refine ⟨46580176574798467579642127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31053451049865645053094751 46580176574798467579642127)
      ·
        refine ⟨69870264862197701369463191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46580176574798467579642127 69870264862197701369463191)
        ·
          refine ⟨104805397293296552054194787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69870264862197701369463191 104805397293296552054194787)
          ·
            refine ⟨157208095939944828081292181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104805397293296552054194787 157208095939944828081292181)
            ·
              refine ⟨7369129497184913816310571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157208095939944828081292181 7369129497184913816310571)
              ·
                refine ⟨11053694245777370724465857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7369129497184913816310571 11053694245777370724465857)
                ·
                  refine ⟨8290270684333028043349393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11053694245777370724465857 8290270684333028043349393)
                  ·
                    refine ⟨6217703013249771032512045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8290270684333028043349393 6217703013249771032512045)
                    ·
                      refine ⟨2331638629968664137192017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6217703013249771032512045 2331638629968664137192017)
                      ·
                        rfl

theorem cell23_4540850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_4540850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540850 prefixEnd_4540850 := by exact prefixLift 4540850
  have htrace : WordTrace (prefixWord ++ tailWord_4540850) baseStart_4540850 baseEnd_4540850 := by
    simpa [prefixWord, tailWord_4540850, baseEnd_4540850] using wordTrace_append hprefix tailTrace_4540850
  have hstable : (prefixWord ++ tailWord_4540850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540850).length < 2 ^ (prefixWord ++ tailWord_4540850).sum := by decide
  have hdescent : baseEnd_4540850 < baseStart_4540850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540856 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_4540856 : Nat := 118140960795 + 4540856 * 2 ^ 59
def prefixEnd_4540856 : Nat := 4983230072969 + 3 ^ 40 * 4540856 * 2
def baseEnd_4540856 : Nat := 2331641710852591113716989

theorem tailTrace_4540856 : CollatzResearch.WordTrace tailWord_4540856 prefixEnd_4540856 2331641710852591113716989 := by
  unfold tailWord_4540856
  simp only [CollatzResearch.WordTrace]
  refine ⟨82809312218630851653945211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110412416291507802205260281 82809312218630851653945211)
  ·
    refine ⟨124213968327946277480917817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82809312218630851653945211 124213968327946277480917817)
    ·
      refine ⟨93160476245959708110688363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124213968327946277480917817 93160476245959708110688363)
      ·
        refine ⟨139740714368939562166032545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93160476245959708110688363 139740714368939562166032545)
        ·
          refine ⟨104805535776704671624524409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139740714368939562166032545 104805535776704671624524409)
          ·
            refine ⟨78604151832528503718393307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104805535776704671624524409 78604151832528503718393307)
            ·
              refine ⟨117906227748792755577589961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78604151832528503718393307 117906227748792755577589961)
              ·
                refine ⟨88429670811594566683192471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117906227748792755577589961 88429670811594566683192471)
                ·
                  refine ⟨132644506217391850024788707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88429670811594566683192471 132644506217391850024788707)
                  ·
                    refine ⟨198966759326087775037183061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132644506217391850024788707 198966759326087775037183061)
                    ·
                      refine ⟨2331641710852591113716989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 198966759326087775037183061 2331641710852591113716989)
                      ·
                        rfl

theorem cell23_4540856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_4540856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540856 prefixEnd_4540856 := by exact prefixLift 4540856
  have htrace : WordTrace (prefixWord ++ tailWord_4540856) baseStart_4540856 baseEnd_4540856 := by
    simpa [prefixWord, tailWord_4540856, baseEnd_4540856] using wordTrace_append hprefix tailTrace_4540856
  have hstable : (prefixWord ++ tailWord_4540856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540856).length < 2 ^ (prefixWord ++ tailWord_4540856).sum := by decide
  have hdescent : baseEnd_4540856 < baseStart_4540856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540890 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_4540890 : Nat := 118140960795 + 4540890 * 2 ^ 59
def prefixEnd_4540890 : Nat := 4983230072969 + 3 ^ 40 * 4540890 * 2
def baseEnd_4540890 : Nat := 2331659169194843980691833

theorem tailTrace_4540890 : CollatzResearch.WordTrace tailWord_4540890 prefixEnd_4540890 2331659169194843980691833 := by
  unfold tailWord_4540890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41404966129784631778657031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110413243012759018076418749 41404966129784631778657031)
  ·
    refine ⟨62107449194676947667985547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41404966129784631778657031 62107449194676947667985547)
    ·
      refine ⟨93161173792015421501978321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62107449194676947667985547 93161173792015421501978321)
      ·
        refine ⟨69870880344011566126483741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93161173792015421501978321 69870880344011566126483741)
        ·
          refine ⟨26201580129004337297431403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69870880344011566126483741 26201580129004337297431403)
          ·
            refine ⟨39302370193506505946147105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26201580129004337297431403 39302370193506505946147105)
            ·
              refine ⟨29476777645129879459610329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39302370193506505946147105 29476777645129879459610329)
              ·
                refine ⟨22107583233847409594707747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29476777645129879459610329 22107583233847409594707747)
                ·
                  refine ⟨33161374850771114392061621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22107583233847409594707747 33161374850771114392061621)
                  ·
                    refine ⟨3108878892259791974255777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33161374850771114392061621 3108878892259791974255777)
                    ·
                      refine ⟨2331659169194843980691833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108878892259791974255777 2331659169194843980691833)
                      ·
                        rfl

theorem cell23_4540890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_4540890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540890 prefixEnd_4540890 := by exact prefixLift 4540890
  have htrace : WordTrace (prefixWord ++ tailWord_4540890) baseStart_4540890 baseEnd_4540890 := by
    simpa [prefixWord, tailWord_4540890, baseEnd_4540890] using wordTrace_append hprefix tailTrace_4540890
  have hstable : (prefixWord ++ tailWord_4540890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540890).length < 2 ^ (prefixWord ++ tailWord_4540890).sum := by decide
  have hdescent : baseEnd_4540890 < baseStart_4540890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540893 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4540893 : Nat := 118140960795 + 4540893 * 2 ^ 59
def prefixEnd_4540893 : Nat := 4983230072969 + 3 ^ 40 * 4540893 * 2
def baseEnd_4540893 : Nat := 2331660709636807468954319

theorem tailTrace_4540893 : CollatzResearch.WordTrace tailWord_4540893 prefixEnd_4540893 2331660709636807468954319 := by
  unfold tailWord_4540893
  simp only [CollatzResearch.WordTrace]
  refine ⟨165619973938127658626987333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110413315958751772417991555 165619973938127658626987333)
  ·
    refine ⟨31053745113398935992560125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165619973938127658626987333 31053745113398935992560125)
    ·
      refine ⟨11645154417524600997210047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31053745113398935992560125 11645154417524600997210047)
      ·
        refine ⟨17467731626286901495815071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11645154417524600997210047 17467731626286901495815071)
        ·
          refine ⟨26201597439430352243722607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17467731626286901495815071 26201597439430352243722607)
          ·
            refine ⟨39302396159145528365583911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26201597439430352243722607 39302396159145528365583911)
            ·
              refine ⟨58953594238718292548375867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39302396159145528365583911 58953594238718292548375867)
              ·
                refine ⟨88430391358077438822563801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58953594238718292548375867 88430391358077438822563801)
                ·
                  refine ⟨66322793518558079116922851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88430391358077438822563801 66322793518558079116922851)
                  ·
                    refine ⟨99484190277837118675384277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66322793518558079116922851 99484190277837118675384277)
                    ·
                      refine ⟨2331660709636807468954319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99484190277837118675384277 2331660709636807468954319)
                      ·
                        rfl

theorem cell23_4540893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4540893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540893 prefixEnd_4540893 := by exact prefixLift 4540893
  have htrace : WordTrace (prefixWord ++ tailWord_4540893) baseStart_4540893 baseEnd_4540893 := by
    simpa [prefixWord, tailWord_4540893, baseEnd_4540893] using wordTrace_append hprefix tailTrace_4540893
  have hstable : (prefixWord ++ tailWord_4540893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540893).length < 2 ^ (prefixWord ++ tailWord_4540893).sum := by decide
  have hdescent : baseEnd_4540893 < baseStart_4540893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540913 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_4540913 : Nat := 118140960795 + 4540913 * 2 ^ 59
def prefixEnd_4540913 : Nat := 4983230072969 + 3 ^ 40 * 4540913 * 2
def baseEnd_4540913 : Nat := 777223659749965796901409

theorem tailTrace_4540913 : CollatzResearch.WordTrace tailWord_4540913 prefixEnd_4540913 777223659749965796901409 := by
  unfold tailWord_4540913
  simp only [CollatzResearch.WordTrace]
  refine ⟨165620703398055202042715393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110413802265370134695143595 165620703398055202042715393)
  ·
    refine ⟨124215527548541401532036545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165620703398055202042715393 124215527548541401532036545)
    ·
      refine ⟨93161645661406051149027409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124215527548541401532036545 93161645661406051149027409)
      ·
        refine ⟨69871234246054538361770557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93161645661406051149027409 69871234246054538361770557)
        ·
          refine ⟨26201712842270451885663959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69871234246054538361770557 26201712842270451885663959)
          ·
            refine ⟨39302569263405677828495939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26201712842270451885663959 39302569263405677828495939)
            ·
              refine ⟨58953853895108516742743909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39302569263405677828495939 58953853895108516742743909)
              ·
                refine ⟨11053847605332846889264483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58953853895108516742743909 11053847605332846889264483)
                ·
                  refine ⟨16580771407999270333896725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11053847605332846889264483 16580771407999270333896725)
                  ·
                    refine ⟨777223659749965796901409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16580771407999270333896725 777223659749965796901409)
                    ·
                      rfl

theorem cell23_4540913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_4540913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540913 prefixEnd_4540913 := by exact prefixLift 4540913
  have htrace : WordTrace (prefixWord ++ tailWord_4540913) baseStart_4540913 baseEnd_4540913 := by
    simpa [prefixWord, tailWord_4540913, baseEnd_4540913] using wordTrace_append hprefix tailTrace_4540913
  have hstable : (prefixWord ++ tailWord_4540913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540913).length < 2 ^ (prefixWord ++ tailWord_4540913).sum := by decide
  have hdescent : baseEnd_4540913 < baseStart_4540913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540920 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_4540920 : Nat := 118140960795 + 4540920 * 2 ^ 59
def prefixEnd_4540920 : Nat := 4983230072969 + 3 ^ 40 * 4540920 * 2
def baseEnd_4540920 : Nat := 2331674573614478863316695

theorem tailTrace_4540920 : CollatzResearch.WordTrace tailWord_4540920 prefixEnd_4540920 2331674573614478863316695 := by
  unfold tailWord_4540920
  simp only [CollatzResearch.WordTrace]
  refine ⟨82810479354514921119110107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110413972472686561492146809 82810479354514921119110107)
  ·
    refine ⟨124215719031772381678665161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82810479354514921119110107 124215719031772381678665161)
    ·
      refine ⟨93161789273829286258998871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124215719031772381678665161 93161789273829286258998871)
      ·
        refine ⟨139742683910743929388498307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93161789273829286258998871 139742683910743929388498307)
        ·
          refine ⟨209614025866115894082747461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139742683910743929388498307 209614025866115894082747461)
          ·
            refine ⟨39302629849896730140515149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209614025866115894082747461 39302629849896730140515149)
            ·
              refine ⟨14738486193711273802693181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39302629849896730140515149 14738486193711273802693181)
              ·
                refine ⟨5526932322641727676009943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14738486193711273802693181 5526932322641727676009943)
                ·
                  refine ⟨8290398483962591514014915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526932322641727676009943 8290398483962591514014915)
                  ·
                    refine ⟨12435597725943887271022373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8290398483962591514014915 12435597725943887271022373)
                    ·
                      refine ⟨2331674573614478863316695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12435597725943887271022373 2331674573614478863316695)
                      ·
                        rfl

theorem cell23_4540920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_4540920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540920 prefixEnd_4540920 := by exact prefixLift 4540920
  have htrace : WordTrace (prefixWord ++ tailWord_4540920) baseStart_4540920 baseEnd_4540920 := by
    simpa [prefixWord, tailWord_4540920, baseEnd_4540920] using wordTrace_append hprefix tailTrace_4540920
  have hstable : (prefixWord ++ tailWord_4540920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540920).length < 2 ^ (prefixWord ++ tailWord_4540920).sum := by decide
  have hdescent : baseEnd_4540920 < baseStart_4540920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540933 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_4540933 : Nat := 118140960795 + 4540933 * 2 ^ 59
def prefixEnd_4540933 : Nat := 4983230072969 + 3 ^ 40 * 4540933 * 2
def baseEnd_4540933 : Nat := 2331681248862987312454135

theorem tailTrace_4540933 : CollatzResearch.WordTrace tailWord_4540933 prefixEnd_4540933 2331681248862987312454135 := by
  unfold tailWord_4540933
  simp only [CollatzResearch.WordTrace]
  refine ⟨165621432857982745458443453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110414288571988496972295635 165621432857982745458443453)
  ·
    refine ⟨62108037321743529546916295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165621432857982745458443453 62108037321743529546916295)
    ·
      refine ⟨93162055982615294320374443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62108037321743529546916295 93162055982615294320374443)
      ·
        refine ⟨139743083973922941480561665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93162055982615294320374443 139743083973922941480561665)
        ·
          refine ⟨104807312980442206110421249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139743083973922941480561665 104807312980442206110421249)
          ·
            refine ⟨78605484735331654582815937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104807312980442206110421249 78605484735331654582815937)
            ·
              refine ⟨58954113551498740937111953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78605484735331654582815937 58954113551498740937111953)
              ·
                refine ⟨44215585163624055702833965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58954113551498740937111953 44215585163624055702833965)
                ·
                  refine ⟨16580844436359020888562737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44215585163624055702833965 16580844436359020888562737)
                  ·
                    refine ⟨12435633327269265666422053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16580844436359020888562737 12435633327269265666422053)
                    ·
                      refine ⟨2331681248862987312454135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12435633327269265666422053 2331681248862987312454135)
                      ·
                        rfl

theorem cell23_4540933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_4540933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540933 prefixEnd_4540933 := by exact prefixLift 4540933
  have htrace : WordTrace (prefixWord ++ tailWord_4540933) baseStart_4540933 baseEnd_4540933 := by
    simpa [prefixWord, tailWord_4540933, baseEnd_4540933] using wordTrace_append hprefix tailTrace_4540933
  have hstable : (prefixWord ++ tailWord_4540933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540933).length < 2 ^ (prefixWord ++ tailWord_4540933).sum := by decide
  have hdescent : baseEnd_4540933 < baseStart_4540933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540940 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4540940 : Nat := 118140960795 + 4540940 * 2 ^ 59
def prefixEnd_4540940 : Nat := 4983230072969 + 3 ^ 40 * 4540940 * 2
def baseEnd_4540940 : Nat := 2331684843227568785066603

theorem tailTrace_4540940 : CollatzResearch.WordTrace tailWord_4540940 prefixEnd_4540940 2331684843227568785066603 := by
  unfold tailWord_4540940
  simp only [CollatzResearch.WordTrace]
  refine ⟨82810844084478692826974137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110414458779304923769298849 82810844084478692826974137)
  ·
    refine ⟨62108133063359019620230603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82810844084478692826974137 62108133063359019620230603)
    ·
      refine ⟨93162199595038529430345905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62108133063359019620230603 93162199595038529430345905)
      ·
        refine ⟨69871649696278897072759429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93162199595038529430345905 69871649696278897072759429)
        ·
          refine ⟨13100934318052293201142393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69871649696278897072759429 13100934318052293201142393)
          ·
            refine ⟨9825700738539219900856795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13100934318052293201142393 9825700738539219900856795)
            ·
              refine ⟨14738551107808829851285193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825700738539219900856795 14738551107808829851285193)
              ·
                refine ⟨11053913330856622388463895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14738551107808829851285193 11053913330856622388463895)
                ·
                  refine ⟨16580869996284933582695843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11053913330856622388463895 16580869996284933582695843)
                  ·
                    refine ⟨24871304994427400374043765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16580869996284933582695843 24871304994427400374043765)
                    ·
                      refine ⟨2331684843227568785066603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24871304994427400374043765 2331684843227568785066603)
                      ·
                        rfl

theorem cell23_4540940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4540940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540940 prefixEnd_4540940 := by exact prefixLift 4540940
  have htrace : WordTrace (prefixWord ++ tailWord_4540940) baseStart_4540940 baseEnd_4540940 := by
    simpa [prefixWord, tailWord_4540940, baseEnd_4540940] using wordTrace_append hprefix tailTrace_4540940
  have hstable : (prefixWord ++ tailWord_4540940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540940).length < 2 ^ (prefixWord ++ tailWord_4540940).sum := by decide
  have hdescent : baseEnd_4540940 < baseStart_4540940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540947 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 2, 4]
def baseStart_4540947 : Nat := 118140960795 + 4540947 * 2 ^ 59
def prefixEnd_4540947 : Nat := 4983230072969 + 3 ^ 40 * 4540947 * 2
def baseEnd_4540947 : Nat := 777229479197383419226357

theorem tailTrace_4540947 : CollatzResearch.WordTrace tailWord_4540947 prefixEnd_4540947 777229479197383419226357 := by
  unfold tailWord_4540947
  simp only [CollatzResearch.WordTrace]
  refine ⟨165621943479932025849453095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110414628986621350566302063 165621943479932025849453095)
  ·
    refine ⟨248432915219898038774179643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165621943479932025849453095 248432915219898038774179643)
    ·
      refine ⟨372649372829847058161269465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248432915219898038774179643 372649372829847058161269465)
      ·
        refine ⟨279487029622385293620952099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372649372829847058161269465 279487029622385293620952099)
        ·
          refine ⟨419230544433577940431428149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279487029622385293620952099 419230544433577940431428149)
          ·
            refine ⟨39302863540647931915446389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 419230544433577940431428149 39302863540647931915446389)
            ·
              refine ⟨3684643456935743617073099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39302863540647931915446389 3684643456935743617073099)
              ·
                refine ⟨5526965185403615425609649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684643456935743617073099 5526965185403615425609649)
                ·
                  refine ⟨4145223889052711569207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5526965185403615425609649 4145223889052711569207237)
                  ·
                    refine ⟨777229479197383419226357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145223889052711569207237 777229479197383419226357)
                    ·
                      rfl

theorem cell23_4540947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 4].length) (baseStart_4540947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540947 prefixEnd_4540947 := by exact prefixLift 4540947
  have htrace : WordTrace (prefixWord ++ tailWord_4540947) baseStart_4540947 baseEnd_4540947 := by
    simpa [prefixWord, tailWord_4540947, baseEnd_4540947] using wordTrace_append hprefix tailTrace_4540947
  have hstable : (prefixWord ++ tailWord_4540947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540947).length < 2 ^ (prefixWord ++ tailWord_4540947).sum := by decide
  have hdescent : baseEnd_4540947 < baseStart_4540947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540957 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_4540957 : Nat := 118140960795 + 4540957 * 2 ^ 59
def prefixEnd_4540957 : Nat := 4983230072969 + 3 ^ 40 * 4540957 * 2
def baseEnd_4540957 : Nat := 2331693572398695218554025

theorem tailTrace_4540957 : CollatzResearch.WordTrace tailWord_4540957 prefixEnd_4540957 2331693572398695218554025 := by
  unfold tailWord_4540957
  simp only [CollatzResearch.WordTrace]
  refine ⟨165622308209895797557317125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110414872139930531704878083 165622308209895797557317125)
  ·
    refine ⟨31054182789355462041996961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165622308209895797557317125 31054182789355462041996961)
    ·
      refine ⟨23290637092016596531497721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31054182789355462041996961 23290637092016596531497721)
      ·
        refine ⟨17467977819012447398623291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23290637092016596531497721 17467977819012447398623291)
        ·
          refine ⟨26201966728518671097934937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17467977819012447398623291 26201966728518671097934937)
          ·
            refine ⟨19651475046389003323451203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26201966728518671097934937 19651475046389003323451203)
            ·
              refine ⟨29477212569583504985176805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19651475046389003323451203 29477212569583504985176805)
              ·
                refine ⟨5526977356796907184720651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29477212569583504985176805 5526977356796907184720651)
                ·
                  refine ⟨8290466035195360777080977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526977356796907184720651 8290466035195360777080977)
                  ·
                    refine ⟨6217849526396520582810733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8290466035195360777080977 6217849526396520582810733)
                    ·
                      refine ⟨2331693572398695218554025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6217849526396520582810733 2331693572398695218554025)
                      ·
                        rfl

theorem cell23_4540957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_4540957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540957 prefixEnd_4540957 := by exact prefixLift 4540957
  have htrace : WordTrace (prefixWord ++ tailWord_4540957) baseStart_4540957 baseEnd_4540957 := by
    simpa [prefixWord, tailWord_4540957, baseEnd_4540957] using wordTrace_append hprefix tailTrace_4540957
  have hstable : (prefixWord ++ tailWord_4540957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540957).length < 2 ^ (prefixWord ++ tailWord_4540957).sum := by decide
  have hdescent : baseEnd_4540957 < baseStart_4540957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540960 : List Nat := [2, 1, 1, 6, 2, 1, 1, 9]
def baseStart_4540960 : Nat := 118140960795 + 4540960 * 2 ^ 59
def prefixEnd_4540960 : Nat := 4983230072969 + 3 ^ 40 * 4540960 * 2
def baseEnd_4540960 : Nat := 86359078253357729882093

theorem tailTrace_4540960 : CollatzResearch.WordTrace tailWord_4540960 prefixEnd_4540960 86359078253357729882093 := by
  unfold tailWord_4540960
  simp only [CollatzResearch.WordTrace]
  refine ⟨82811208814442464534838167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110414945085923286046450889 82811208814442464534838167)
  ·
    refine ⟨124216813221663696802257251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82811208814442464534838167 124216813221663696802257251)
    ·
      refine ⟨186325219832495545203385877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124216813221663696802257251 186325219832495545203385877)
      ·
        refine ⟨8733994679648228681408713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186325219832495545203385877 8733994679648228681408713)
        ·
          refine ⟨6550496009736171511056535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8733994679648228681408713 6550496009736171511056535)
          ·
            refine ⟨9825744014604257266584803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550496009736171511056535 9825744014604257266584803)
            ·
              refine ⟨14738616021906385899877205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825744014604257266584803 14738616021906385899877205)
              ·
                refine ⟨86359078253357729882093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14738616021906385899877205 86359078253357729882093)
                ·
                  rfl

theorem cell23_4540960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 9].length) (baseStart_4540960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540960 prefixEnd_4540960 := by exact prefixLift 4540960
  have htrace : WordTrace (prefixWord ++ tailWord_4540960) baseStart_4540960 baseEnd_4540960 := by
    simpa [prefixWord, tailWord_4540960, baseEnd_4540960] using wordTrace_append hprefix tailTrace_4540960
  have hstable : (prefixWord ++ tailWord_4540960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540960).length < 2 ^ (prefixWord ++ tailWord_4540960).sum := by decide
  have hdescent : baseEnd_4540960 < baseStart_4540960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540983 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_4540983 : Nat := 118140960795 + 4540983 * 2 ^ 59
def prefixEnd_4540983 : Nat := 4983230072969 + 3 ^ 40 * 4540983 * 2
def baseEnd_4540983 : Nat := 2331706922895712116828905

theorem tailTrace_4540983 : CollatzResearch.WordTrace tailWord_4540983 prefixEnd_4540983 2331706922895712116828905 := by
  unfold tailWord_4540983
  simp only [CollatzResearch.WordTrace]
  refine ⟨165623256507801603997763603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110415504338534402665175735 165623256507801603997763603)
  ·
    refine ⟨248434884761702405996645405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165623256507801603997763603 248434884761702405996645405)
    ·
      refine ⟨93163081785638402248742027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248434884761702405996645405 93163081785638402248742027)
      ·
        refine ⟨139744622678457603373113041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93163081785638402248742027 139744622678457603373113041)
        ·
          refine ⟨104808467008843202529834781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139744622678457603373113041 104808467008843202529834781)
          ·
            refine ⟨39303175128316200948688043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104808467008843202529834781 39303175128316200948688043)
            ·
              refine ⟨58954762692474301423032065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39303175128316200948688043 58954762692474301423032065)
              ·
                refine ⟨44216072019355726067274049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58954762692474301423032065 44216072019355726067274049)
                ·
                  refine ⟨33162054014516794550455537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44216072019355726067274049 33162054014516794550455537)
                  ·
                    refine ⟨24871540510887595912841653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33162054014516794550455537 24871540510887595912841653)
                    ·
                      refine ⟨2331706922895712116828905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24871540510887595912841653 2331706922895712116828905)
                      ·
                        rfl

theorem cell23_4540983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_4540983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540983 prefixEnd_4540983 := by exact prefixLift 4540983
  have htrace : WordTrace (prefixWord ++ tailWord_4540983) baseStart_4540983 baseEnd_4540983 := by
    simpa [prefixWord, tailWord_4540983, baseEnd_4540983] using wordTrace_append hprefix tailTrace_4540983
  have hstable : (prefixWord ++ tailWord_4540983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540983).length < 2 ^ (prefixWord ++ tailWord_4540983).sum := by decide
  have hdescent : baseEnd_4540983 < baseStart_4540983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540988 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_4540988 : Nat := 118140960795 + 4540988 * 2 ^ 59
def prefixEnd_4540988 : Nat := 4983230072969 + 3 ^ 40 * 4540988 * 2
def baseEnd_4540988 : Nat := 2331709490298984597266383

theorem tailTrace_4540988 : CollatzResearch.WordTrace tailWord_4540988 prefixEnd_4540988 2331709490298984597266383 := by
  unfold tailWord_4540988
  simp only [CollatzResearch.WordTrace]
  refine ⟨82811719436391744925847809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110415625915188993234463745 82811719436391744925847809)
  ·
    refine ⟨62108789577293808694385857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82811719436391744925847809 62108789577293808694385857)
    ·
      refine ⟨46581592182970356520789393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62108789577293808694385857 46581592182970356520789393)
      ·
        refine ⟨34936194137227767390592045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46581592182970356520789393 34936194137227767390592045)
        ·
          refine ⟨13101072801460412771472017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34936194137227767390592045 13101072801460412771472017)
          ·
            refine ⟨9825804601095309578604013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13101072801460412771472017 9825804601095309578604013)
            ·
              refine ⟨3684676725410741091976505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9825804601095309578604013 3684676725410741091976505)
              ·
                refine ⟨2763507544058055818982379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684676725410741091976505 2763507544058055818982379)
                ·
                  refine ⟨4145261316087083728473569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763507544058055818982379 4145261316087083728473569)
                  ·
                    refine ⟨3108945987065312796355177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4145261316087083728473569 3108945987065312796355177)
                    ·
                      refine ⟨2331709490298984597266383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108945987065312796355177 2331709490298984597266383)
                      ·
                        rfl

theorem cell23_4540988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_4540988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540988 prefixEnd_4540988 := by exact prefixLift 4540988
  have htrace : WordTrace (prefixWord ++ tailWord_4540988) baseStart_4540988 baseEnd_4540988 := by
    simpa [prefixWord, tailWord_4540988, baseEnd_4540988] using wordTrace_append hprefix tailTrace_4540988
  have hstable : (prefixWord ++ tailWord_4540988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540988).length < 2 ^ (prefixWord ++ tailWord_4540988).sum := by decide
  have hdescent : baseEnd_4540988 < baseStart_4540988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540998 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_4540998 : Nat := 118140960795 + 4540998 * 2 ^ 59
def prefixEnd_4540998 : Nat := 4983230072969 + 3 ^ 40 * 4540998 * 2
def baseEnd_4540998 : Nat := 777238208368509852713779

theorem tailTrace_4540998 : CollatzResearch.WordTrace tailWord_4540998 prefixEnd_4540998 777238208368509852713779 := by
  unfold tailWord_4540998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175743862585851923736239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110415869068498174373039765 5175743862585851923736239)
  ·
    refine ⟨7763615793878777885604359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5175743862585851923736239 7763615793878777885604359)
    ·
      refine ⟨11645423690818166828406539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763615793878777885604359 11645423690818166828406539)
      ·
        refine ⟨17468135536227250242609809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11645423690818166828406539 17468135536227250242609809)
        ·
          refine ⟨13101101652170437681957357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17468135536227250242609809 13101101652170437681957357)
          ·
            refine ⟨4912913119563914130734009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13101101652170437681957357 4912913119563914130734009)
            ·
              refine ⟨3684684839672935598050507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4912913119563914130734009 3684684839672935598050507)
              ·
                refine ⟨5527027259509403397075761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684684839672935598050507 5527027259509403397075761)
                ·
                  refine ⟨4145270444632052547806821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527027259509403397075761 4145270444632052547806821)
                  ·
                    refine ⟨777238208368509852713779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145270444632052547806821 777238208368509852713779)
                    ·
                      rfl

theorem cell23_4540998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_4540998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4540998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4540998 prefixEnd_4540998 := by exact prefixLift 4540998
  have htrace : WordTrace (prefixWord ++ tailWord_4540998) baseStart_4540998 baseEnd_4540998 := by
    simpa [prefixWord, tailWord_4540998, baseEnd_4540998] using wordTrace_append hprefix tailTrace_4540998
  have hstable : (prefixWord ++ tailWord_4540998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540998).length < 2 ^ (prefixWord ++ tailWord_4540998).sum := by decide
  have hdescent : baseEnd_4540998 < baseStart_4540998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541003 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 2, 6]
def baseStart_4541003 : Nat := 118140960795 + 4541003 * 2 ^ 59
def prefixEnd_4541003 : Nat := 4983230072969 + 3 ^ 40 * 4541003 * 2
def baseEnd_4541003 : Nat := 777239064169600679526271

theorem tailTrace_4541003 : CollatzResearch.WordTrace tailWord_4541003 prefixEnd_4541003 777239064169600679526271 := by
  unfold tailWord_4541003
  simp only [CollatzResearch.WordTrace]
  refine ⟨165623985967729147413491663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110415990645152764942327775 165623985967729147413491663)
  ·
    refine ⟨248435978951593721120237495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165623985967729147413491663 248435978951593721120237495)
    ·
      refine ⟨372653968427390581680356243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248435978951593721120237495 372653968427390581680356243)
      ·
        refine ⟨558980952641085872520534365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372653968427390581680356243 558980952641085872520534365)
        ·
          refine ⟨209617857240407202195200387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558980952641085872520534365 209617857240407202195200387)
          ·
            refine ⟨314426785860610803292800581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209617857240407202195200387 314426785860610803292800581)
            ·
              refine ⟨58955022348864525617400109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314426785860610803292800581 58955022348864525617400109)
              ·
                refine ⟨22108133380824197106525041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58955022348864525617400109 22108133380824197106525041)
                ·
                  refine ⟨16581100035618147829893781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22108133380824197106525041 16581100035618147829893781)
                  ·
                    refine ⟨777239064169600679526271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16581100035618147829893781 777239064169600679526271)
                    ·
                      rfl

theorem cell23_4541003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_4541003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541003 prefixEnd_4541003 := by exact prefixLift 4541003
  have htrace : WordTrace (prefixWord ++ tailWord_4541003) baseStart_4541003 baseEnd_4541003 := by
    simpa [prefixWord, tailWord_4541003, baseEnd_4541003] using wordTrace_append hprefix tailTrace_4541003
  have hstable : (prefixWord ++ tailWord_4541003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541003).length < 2 ^ (prefixWord ++ tailWord_4541003).sum := by decide
  have hdescent : baseEnd_4541003 < baseStart_4541003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541027 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 1, 4, 2]
def baseStart_4541027 : Nat := 118140960795 + 4541027 * 2 ^ 59
def prefixEnd_4541027 : Nat := 4983230072969 + 3 ^ 40 * 4541027 * 2
def baseEnd_4541027 : Nat := 2331729516044509944678703

theorem tailTrace_4541027 : CollatzResearch.WordTrace tailWord_4541027 prefixEnd_4541027 2331729516044509944678703 := by
  unfold tailWord_4541027
  simp only [CollatzResearch.WordTrace]
  refine ⟨165624861319642199512365335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110416574213094799674910223 165624861319642199512365335)
  ·
    refine ⟨248437291979463299268548003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165624861319642199512365335 248437291979463299268548003)
    ·
      refine ⟨372655937969194948902822005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248437291979463299268548003 372655937969194948902822005)
      ·
        refine ⟨34936494184612026459639563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 372655937969194948902822005 34936494184612026459639563)
        ·
          refine ⟨52404741276918039689459345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34936494184612026459639563 52404741276918039689459345)
          ·
            refine ⟨39303555957688529767094509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52404741276918039689459345 39303555957688529767094509)
            ·
              refine ⟨14738833484133198662660441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39303555957688529767094509 14738833484133198662660441)
              ·
                refine ⟨11054125113099898996995331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14738833484133198662660441 11054125113099898996995331)
                ·
                  refine ⟨16581187669649848495492997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11054125113099898996995331 16581187669649848495492997)
                  ·
                    refine ⟨3108972688059346592904937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16581187669649848495492997 3108972688059346592904937)
                    ·
                      refine ⟨2331729516044509944678703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3108972688059346592904937 2331729516044509944678703)
                      ·
                        rfl

theorem cell23_4541027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_4541027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541027 prefixEnd_4541027 := by exact prefixLift 4541027
  have htrace : WordTrace (prefixWord ++ tailWord_4541027) baseStart_4541027 baseEnd_4541027 := by
    simpa [prefixWord, tailWord_4541027, baseEnd_4541027] using wordTrace_append hprefix tailTrace_4541027
  have hstable : (prefixWord ++ tailWord_4541027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541027).length < 2 ^ (prefixWord ++ tailWord_4541027).sum := by decide
  have hdescent : baseEnd_4541027 < baseStart_4541027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541080 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_4541080 : Nat := 118140960795 + 4541080 * 2 ^ 59
def prefixEnd_4541080 : Nat := 4983230072969 + 3 ^ 40 * 4541080 * 2
def baseEnd_4541080 : Nat := 777252243506399412438653

theorem tailTrace_4541080 : CollatzResearch.WordTrace tailWord_4541080 prefixEnd_4541080 777252243506399412438653 := by
  unfold tailWord_4541080
  simp only [CollatzResearch.WordTrace]
  refine ⟨82813397194225094782022347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110417862925633459709363129 82813397194225094782022347)
  ·
    refine ⟨124220095791337642173033521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82813397194225094782022347 124220095791337642173033521)
    ·
      refine ⟨93165071843503231629775141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124220095791337642173033521 93165071843503231629775141)
      ·
        refine ⟨17468450970656855930582839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93165071843503231629775141 17468450970656855930582839)
        ·
          refine ⟨26202676455985283895874259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17468450970656855930582839 26202676455985283895874259)
          ·
            refine ⟨39304014683977925843811389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26202676455985283895874259 39304014683977925843811389)
            ·
              refine ⟨14739005506491722191429271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39304014683977925843811389 14739005506491722191429271)
              ·
                refine ⟨22108508259737583287143907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14739005506491722191429271 22108508259737583287143907)
                ·
                  refine ⟨33162762389606374930715861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22108508259737583287143907 33162762389606374930715861)
                  ·
                    refine ⟨777252243506399412438653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33162762389606374930715861 777252243506399412438653)
                    ·
                      rfl

theorem cell23_4541080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_4541080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541080 prefixEnd_4541080 := by exact prefixLift 4541080
  have htrace : WordTrace (prefixWord ++ tailWord_4541080) baseStart_4541080 baseEnd_4541080 := by
    simpa [prefixWord, tailWord_4541080, baseEnd_4541080] using wordTrace_append hprefix tailTrace_4541080
  have hstable : (prefixWord ++ tailWord_4541080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541080).length < 2 ^ (prefixWord ++ tailWord_4541080).sum := by decide
  have hdescent : baseEnd_4541080 < baseStart_4541080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541084 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 5]
def baseStart_4541084 : Nat := 118140960795 + 4541084 * 2 ^ 59
def prefixEnd_4541084 : Nat := 4983230072969 + 3 ^ 40 * 4541084 * 2
def baseEnd_4541084 : Nat := 259084309382424024629549

theorem tailTrace_4541084 : CollatzResearch.WordTrace tailWord_4541084 prefixEnd_4541084 259084309382424024629549 := by
  unfold tailWord_4541084
  simp only [CollatzResearch.WordTrace]
  refine ⟨82813470140217849123595153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110417960186957132164793537 82813470140217849123595153)
  ·
    refine ⟨62110102605163386842696365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82813470140217849123595153 62110102605163386842696365)
    ·
      refine ⟨23291288476936270066011137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62110102605163386842696365 23291288476936270066011137)
      ·
        refine ⟨17468466357702202549508353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23291288476936270066011137 17468466357702202549508353)
        ·
          refine ⟨13101349768276651912131265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17468466357702202549508353 13101349768276651912131265)
          ·
            refine ⟨9826012326207488934098449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13101349768276651912131265 9826012326207488934098449)
            ·
              refine ⟨7369509244655616700573837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9826012326207488934098449 7369509244655616700573837)
              ·
                refine ⟨2763565966745856262715189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7369509244655616700573837 2763565966745856262715189)
                ·
                  refine ⟨259084309382424024629549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763565966745856262715189 259084309382424024629549)
                  ·
                    rfl

theorem cell23_4541084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_4541084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541084 prefixEnd_4541084 := by exact prefixLift 4541084
  have htrace : WordTrace (prefixWord ++ tailWord_4541084) baseStart_4541084 baseEnd_4541084 := by
    simpa [prefixWord, tailWord_4541084, baseEnd_4541084] using wordTrace_append hprefix tailTrace_4541084
  have hstable : (prefixWord ++ tailWord_4541084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541084).length < 2 ^ (prefixWord ++ tailWord_4541084).sum := by decide
  have hdescent : baseEnd_4541084 < baseStart_4541084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541095 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4541095 : Nat := 118140960795 + 4541095 * 2 ^ 59
def prefixEnd_4541095 : Nat := 4983230072969 + 3 ^ 40 * 4541095 * 2
def baseEnd_4541095 : Nat := 2331764432729015678628391

theorem tailTrace_4541095 : CollatzResearch.WordTrace tailWord_4541095 prefixEnd_4541095 2331764432729015678628391 := by
  unfold tailWord_4541095
  simp only [CollatzResearch.WordTrace]
  refine ⟨165627341483395847125840739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110418227655597231417227159 165627341483395847125840739)
  ·
    refine ⟨248441012225093770688761109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165627341483395847125840739 248441012225093770688761109)
    ·
      refine ⟨11645672448051270501035677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 248441012225093770688761109 11645672448051270501035677)
      ·
        refine ⟨4367127168019226437888379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11645672448051270501035677 4367127168019226437888379)
        ·
          refine ⟨6550690752028839656832569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367127168019226437888379 6550690752028839656832569)
          ·
            refine ⟨4913018064021629742624427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6550690752028839656832569 4913018064021629742624427)
            ·
              refine ⟨7369527096032444613936641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913018064021629742624427 7369527096032444613936641)
              ·
                refine ⟨5527145322024333460452481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7369527096032444613936641 5527145322024333460452481)
                ·
                  refine ⟨4145358991518250095339361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527145322024333460452481 4145358991518250095339361)
                  ·
                    refine ⟨3109019243638687571504521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4145358991518250095339361 3109019243638687571504521)
                    ·
                      refine ⟨2331764432729015678628391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109019243638687571504521 2331764432729015678628391)
                      ·
                        rfl

theorem cell23_4541095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4541095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541095 prefixEnd_4541095 := by exact prefixLift 4541095
  have htrace : WordTrace (prefixWord ++ tailWord_4541095) baseStart_4541095 baseEnd_4541095 := by
    simpa [prefixWord, tailWord_4541095, baseEnd_4541095] using wordTrace_append hprefix tailTrace_4541095
  have hstable : (prefixWord ++ tailWord_4541095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541095).length < 2 ^ (prefixWord ++ tailWord_4541095).sum := by decide
  have hdescent : baseEnd_4541095 < baseStart_4541095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541137 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_4541137 : Nat := 118140960795 + 4541137 * 2 ^ 59
def prefixEnd_4541137 : Nat := 4983230072969 + 3 ^ 40 * 4541137 * 2
def baseEnd_4541137 : Nat := 2331785998916504514303197

theorem tailTrace_4541137 : CollatzResearch.WordTrace tailWord_4541137 prefixEnd_4541137 2331785998916504514303197 := by
  unfold tailWord_4541137
  simp only [CollatzResearch.WordTrace]
  refine ⟨165628873349243688298869665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110419248899495792199246443 165628873349243688298869665)
  ·
    refine ⟨124221655011932766224152249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165628873349243688298869665 124221655011932766224152249)
    ·
      refine ⟨93166241258949574668114187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124221655011932766224152249 93166241258949574668114187)
      ·
        refine ⟨139749361888424362002171281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93166241258949574668114187 139749361888424362002171281)
        ·
          refine ⟨104812021416318271501628461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139749361888424362002171281 104812021416318271501628461)
          ·
            refine ⟨39304508031119351813110673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104812021416318271501628461 39304508031119351813110673)
            ·
              refine ⟨29478381023339513859833005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39304508031119351813110673 29478381023339513859833005)
              ·
                refine ⟨11054392883752317697437377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29478381023339513859833005 11054392883752317697437377)
                ·
                  refine ⟨8290794662814238273078033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11054392883752317697437377 8290794662814238273078033)
                  ·
                    refine ⟨6218095997110678704808525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8290794662814238273078033 6218095997110678704808525)
                    ·
                      refine ⟨2331785998916504514303197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218095997110678704808525 2331785998916504514303197)
                      ·
                        rfl

theorem cell23_4541137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_4541137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541137 prefixEnd_4541137 := by exact prefixLift 4541137
  have htrace : WordTrace (prefixWord ++ tailWord_4541137) baseStart_4541137 baseEnd_4541137 := by
    simpa [prefixWord, tailWord_4541137, baseEnd_4541137] using wordTrace_append hprefix tailTrace_4541137
  have hstable : (prefixWord ++ tailWord_4541137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541137).length < 2 ^ (prefixWord ++ tailWord_4541137).sum := by decide
  have hdescent : baseEnd_4541137 < baseStart_4541137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541177 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 5, 2]
def baseStart_4541177 : Nat := 118140960795 + 4541177 * 2 ^ 59
def prefixEnd_4541177 : Nat := 4983230072969 + 3 ^ 40 * 4541177 * 2
def baseEnd_4541177 : Nat := 2331806538142684357803013

theorem tailTrace_4541177 : CollatzResearch.WordTrace tailWord_4541177 prefixEnd_4541177 2331806538142684357803013 := by
  unfold tailWord_4541177
  simp only [CollatzResearch.WordTrace]
  refine ⟨165630332269098775130325785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110420221512732516753550523 165630332269098775130325785)
  ·
    refine ⟨124222749201824081347744339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165630332269098775130325785 124222749201824081347744339)
    ·
      refine ⟨186334123802736122021616509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124222749201824081347744339 186334123802736122021616509)
      ·
        refine ⟨69875296426026045758106191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186334123802736122021616509 69875296426026045758106191)
        ·
          refine ⟨104812944639039068637159287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69875296426026045758106191 104812944639039068637159287)
          ·
            refine ⟨157219416958558602955738931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104812944639039068637159287 157219416958558602955738931)
            ·
              refine ⟨235829125437837904433608397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157219416958558602955738931 235829125437837904433608397)
              ·
                refine ⟨88435922039189214162603149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235829125437837904433608397 88435922039189214162603149)
                ·
                  refine ⟨33163470764695955310976181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88435922039189214162603149 33163470764695955310976181)
                  ·
                    refine ⟨3109075384190245810404017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33163470764695955310976181 3109075384190245810404017)
                    ·
                      refine ⟨2331806538142684357803013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109075384190245810404017 2331806538142684357803013)
                      ·
                        rfl

theorem cell23_4541177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_4541177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541177 prefixEnd_4541177 := by exact prefixLift 4541177
  have htrace : WordTrace (prefixWord ++ tailWord_4541177) baseStart_4541177 baseEnd_4541177 := by
    simpa [prefixWord, tailWord_4541177, baseEnd_4541177] using wordTrace_append hprefix tailTrace_4541177
  have hstable : (prefixWord ++ tailWord_4541177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541177).length < 2 ^ (prefixWord ++ tailWord_4541177).sum := by decide
  have hdescent : baseEnd_4541177 < baseStart_4541177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541218 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_4541218 : Nat := 118140960795 + 4541218 * 2 ^ 59
def prefixEnd_4541218 : Nat := 4983230072969 + 3 ^ 40 * 4541218 * 2
def baseEnd_4541218 : Nat := 2331827590849518697390325

theorem tailTrace_4541218 : CollatzResearch.WordTrace tailWord_4541218 prefixEnd_4541218 2331827590849518697390325 := by
  unfold tailWord_4541218
  simp only [CollatzResearch.WordTrace]
  refine ⟨41407956915487559783142077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110421218441300159421712205 41407956915487559783142077)
  ·
    refine ⟨15527983843307834918678279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41407956915487559783142077 15527983843307834918678279)
    ·
      refine ⟨23291975764961752378017419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15527983843307834918678279 23291975764961752378017419)
      ·
        refine ⟨34937963647442628567026129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23291975764961752378017419 34937963647442628567026129)
        ·
          refine ⟨26203472735581971425269597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34937963647442628567026129 26203472735581971425269597)
          ·
            refine ⟨9826302275843239284476099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26203472735581971425269597 9826302275843239284476099)
            ·
              refine ⟨14739453413764858926714149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9826302275843239284476099 14739453413764858926714149)
              ·
                refine ⟨2763647515080911048758903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14739453413764858926714149 2763647515080911048758903)
                ·
                  refine ⟨4145471272621366573138355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763647515080911048758903 4145471272621366573138355)
                  ·
                    refine ⟨6218206908932049859707533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4145471272621366573138355 6218206908932049859707533)
                    ·
                      refine ⟨2331827590849518697390325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218206908932049859707533 2331827590849518697390325)
                      ·
                        rfl

theorem cell23_4541218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_4541218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541218 prefixEnd_4541218 := by exact prefixLift 4541218
  have htrace : WordTrace (prefixWord ++ tailWord_4541218) baseStart_4541218 baseEnd_4541218 := by
    simpa [prefixWord, tailWord_4541218, baseEnd_4541218] using wordTrace_append hprefix tailTrace_4541218
  have hstable : (prefixWord ++ tailWord_4541218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541218).length < 2 ^ (prefixWord ++ tailWord_4541218).sum := by decide
  have hdescent : baseEnd_4541218 < baseStart_4541218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541227 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3]
def baseStart_4541227 : Nat := 118140960795 + 4541227 * 2 ^ 59
def prefixEnd_4541227 : Nat := 4983230072969 + 3 ^ 40 * 4541227 * 2
def baseEnd_4541227 : Nat := 2331832212175409162177783

theorem tailTrace_4541227 : CollatzResearch.WordTrace tailWord_4541227 prefixEnd_4541227 2331832212175409162177783 := by
  unfold tailWord_4541227
  simp only [CollatzResearch.WordTrace]
  refine ⟨165632155918917633669645935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110421437279278422446430623 165632155918917633669645935)
  ·
    refine ⟨248448233878376450504468903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165632155918917633669645935 248448233878376450504468903)
    ·
      refine ⟨372672350817564675756703355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248448233878376450504468903 372672350817564675756703355)
      ·
        refine ⟨559008526226347013635055033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372672350817564675756703355 559008526226347013635055033)
        ·
          refine ⟨419256394669760260226291275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559008526226347013635055033 419256394669760260226291275)
          ·
            refine ⟨628884592004640390339436913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419256394669760260226291275 628884592004640390339436913)
            ·
              refine ⟨471663444003480292754577685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628884592004640390339436913 471663444003480292754577685)
              ·
                refine ⟨22109223937663138722870829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 471663444003480292754577685 22109223937663138722870829)
                ·
                  refine ⟨8290958976623677021076561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22109223937663138722870829 8290958976623677021076561)
                  ·
                    refine ⟨6218219232467757765807421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8290958976623677021076561 6218219232467757765807421)
                    ·
                      refine ⟨2331832212175409162177783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218219232467757765807421 2331832212175409162177783)
                      ·
                        rfl

theorem cell23_4541227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3].length) (baseStart_4541227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541227 prefixEnd_4541227 := by exact prefixLift 4541227
  have htrace : WordTrace (prefixWord ++ tailWord_4541227) baseStart_4541227 baseEnd_4541227 := by
    simpa [prefixWord, tailWord_4541227, baseEnd_4541227] using wordTrace_append hprefix tailTrace_4541227
  have hstable : (prefixWord ++ tailWord_4541227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541227).length < 2 ^ (prefixWord ++ tailWord_4541227).sum := by decide
  have hdescent : baseEnd_4541227 < baseStart_4541227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541234 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_4541234 : Nat := 118140960795 + 4541234 * 2 ^ 59
def prefixEnd_4541234 : Nat := 4983230072969 + 3 ^ 40 * 4541234 * 2
def baseEnd_4541234 : Nat := 777278602179996878263417

theorem tailTrace_4541234 : CollatzResearch.WordTrace tailWord_4541234 prefixEnd_4541234 777278602179996878263417 := by
  unfold tailWord_4541234
  simp only [CollatzResearch.WordTrace]
  refine ⟨41408102807473068466287689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110421607486594849243433837 41408102807473068466287689)
  ·
    refine ⟨31056077105604801349715767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41408102807473068466287689 31056077105604801349715767)
    ·
      refine ⟨46584115658407202024573651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31056077105604801349715767 46584115658407202024573651)
      ·
        refine ⟨69876173487610803036860477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46584115658407202024573651 69876173487610803036860477)
        ·
          refine ⟨26203565057854051138822679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69876173487610803036860477 26203565057854051138822679)
          ·
            refine ⟨39305347586781076708234019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26203565057854051138822679 39305347586781076708234019)
            ·
              refine ⟨58958021380171615062351029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39305347586781076708234019 58958021380171615062351029)
              ·
                refine ⟨5527314504391088912095409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58958021380171615062351029 5527314504391088912095409)
                ·
                  refine ⟨4145485878293316684071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527314504391088912095409 4145485878293316684071557)
                  ·
                    refine ⟨777278602179996878263417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145485878293316684071557 777278602179996878263417)
                    ·
                      rfl

theorem cell23_4541234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_4541234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541234 prefixEnd_4541234 := by exact prefixLift 4541234
  have htrace : WordTrace (prefixWord ++ tailWord_4541234) baseStart_4541234 baseEnd_4541234 := by
    simpa [prefixWord, tailWord_4541234, baseEnd_4541234] using wordTrace_append hprefix tailTrace_4541234
  have hstable : (prefixWord ++ tailWord_4541234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541234).length < 2 ^ (prefixWord ++ tailWord_4541234).sum := by decide
  have hdescent : baseEnd_4541234 < baseStart_4541234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541244 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_4541244 : Nat := 118140960795 + 4541244 * 2 ^ 59
def prefixEnd_4541244 : Nat := 4983230072969 + 3 ^ 40 * 4541244 * 2
def baseEnd_4541244 : Nat := 2331840941346535595665205

theorem tailTrace_4541244 : CollatzResearch.WordTrace tailWord_4541244 prefixEnd_4541244 2331840941346535595665205 := by
  unfold tailWord_4541244
  simp only [CollatzResearch.WordTrace]
  refine ⟨82816387979928022786507393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110421850639904030382009857 82816387979928022786507393)
  ·
    refine ⟨62112290984946017089880545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82816387979928022786507393 62112290984946017089880545)
    ·
      refine ⟨46584218238709512817410409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62112290984946017089880545 46584218238709512817410409)
      ·
        refine ⟨34938163679032134613057807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46584218238709512817410409 34938163679032134613057807)
        ·
          refine ⟨52407245518548201919586711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34938163679032134613057807 52407245518548201919586711)
          ·
            refine ⟨78610868277822302879380067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52407245518548201919586711 78610868277822302879380067)
            ·
              refine ⟨117916302416733454319070101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78610868277822302879380067 117916302416733454319070101)
              ·
                refine ⟨5527326675784380671206411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117916302416733454319070101 5527326675784380671206411)
                ·
                  refine ⟨8290990013676571006809617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527326675784380671206411 8290990013676571006809617)
                  ·
                    refine ⟨6218242510257428255107213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8290990013676571006809617 6218242510257428255107213)
                    ·
                      refine ⟨2331840941346535595665205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218242510257428255107213 2331840941346535595665205)
                      ·
                        rfl

theorem cell23_4541244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_4541244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541244 prefixEnd_4541244 := by exact prefixLift 4541244
  have htrace : WordTrace (prefixWord ++ tailWord_4541244) baseStart_4541244 baseEnd_4541244 := by
    simpa [prefixWord, tailWord_4541244, baseEnd_4541244] using wordTrace_append hprefix tailTrace_4541244
  have hstable : (prefixWord ++ tailWord_4541244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541244).length < 2 ^ (prefixWord ++ tailWord_4541244).sum := by decide
  have hdescent : baseEnd_4541244 < baseStart_4541244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541245 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4541245 : Nat := 118140960795 + 4541245 * 2 ^ 59
def prefixEnd_4541245 : Nat := 4983230072969 + 3 ^ 40 * 4541245 * 2
def baseEnd_4541245 : Nat := 2331841454827190091752701

theorem tailTrace_4541245 : CollatzResearch.WordTrace tailWord_4541245 prefixEnd_4541245 2331841454827190091752701 := by
  unfold tailWord_4541245
  simp only [CollatzResearch.WordTrace]
  refine ⟨165632812432852422743801189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110421874955234948495867459 165632812432852422743801189)
  ·
    refine ⟨31056152331159829264462723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165632812432852422743801189 31056152331159829264462723)
    ·
      refine ⟨46584228496739743896694085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31056152331159829264462723 46584228496739743896694085)
      ·
        refine ⟨8734542843138701980630141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46584228496739743896694085 8734542843138701980630141)
        ·
          refine ⟨3275453566177013242736303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8734542843138701980630141 3275453566177013242736303)
          ·
            refine ⟨4913180349265519864104455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275453566177013242736303 4913180349265519864104455)
            ·
              refine ⟨7369770523898279796156683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913180349265519864104455 7369770523898279796156683)
              ·
                refine ⟨11054655785847419694235025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7369770523898279796156683 11054655785847419694235025)
                ·
                  refine ⟨8290991839385564770676269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11054655785847419694235025 8290991839385564770676269)
                  ·
                    refine ⟨3109121939769586789003601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8290991839385564770676269 3109121939769586789003601)
                    ·
                      refine ⟨2331841454827190091752701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109121939769586789003601 2331841454827190091752701)
                      ·
                        rfl

theorem cell23_4541245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4541245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541245 prefixEnd_4541245 := by exact prefixLift 4541245
  have htrace : WordTrace (prefixWord ++ tailWord_4541245) baseStart_4541245 baseEnd_4541245 := by
    simpa [prefixWord, tailWord_4541245, baseEnd_4541245] using wordTrace_append hprefix tailTrace_4541245
  have hstable : (prefixWord ++ tailWord_4541245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541245).length < 2 ^ (prefixWord ++ tailWord_4541245).sum := by decide
  have hdescent : baseEnd_4541245 < baseStart_4541245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541252 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4541252 : Nat := 118140960795 + 4541252 * 2 ^ 59
def prefixEnd_4541252 : Nat := 4983230072969 + 3 ^ 40 * 4541252 * 2
def baseEnd_4541252 : Nat := 2331845049191771564365169

theorem tailTrace_4541252 : CollatzResearch.WordTrace tailWord_4541252 prefixEnd_4541252 2331845049191771564365169 := by
  unfold tailWord_4541252
  simp only [CollatzResearch.WordTrace]
  refine ⟨82816533871913531469653005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110422045162551375292870673 82816533871913531469653005)
  ·
    refine ⟨31056200201967574301119877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82816533871913531469653005 31056200201967574301119877)
    ·
      refine ⟨5823037537868920181459977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31056200201967574301119877 5823037537868920181459977)
      ·
        refine ⟨4367278153401690136094983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5823037537868920181459977 4367278153401690136094983)
        ·
          refine ⟨6550917230102535204142475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367278153401690136094983 6550917230102535204142475)
          ·
            refine ⟨9826375845153802806213713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550917230102535204142475 9826375845153802806213713)
            ·
              refine ⟨7369781883865352104660285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9826375845153802806213713 7369781883865352104660285)
              ·
                refine ⟨2763668206449507039247607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7369781883865352104660285 2763668206449507039247607)
                ·
                  refine ⟨4145502309674260558871411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763668206449507039247607 4145502309674260558871411)
                  ·
                    refine ⟨6218253464511390838307117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4145502309674260558871411 6218253464511390838307117)
                    ·
                      refine ⟨2331845049191771564365169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218253464511390838307117 2331845049191771564365169)
                      ·
                        rfl

theorem cell23_4541252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4541252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541252 prefixEnd_4541252 := by exact prefixLift 4541252
  have htrace : WordTrace (prefixWord ++ tailWord_4541252) baseStart_4541252 baseEnd_4541252 := by
    simpa [prefixWord, tailWord_4541252, baseEnd_4541252] using wordTrace_append hprefix tailTrace_4541252
  have hstable : (prefixWord ++ tailWord_4541252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541252).length < 2 ^ (prefixWord ++ tailWord_4541252).sum := by decide
  have hdescent : baseEnd_4541252 < baseStart_4541252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541268 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4541268 : Nat := 118140960795 + 4541268 * 2 ^ 59
def prefixEnd_4541268 : Nat := 4983230072969 + 3 ^ 40 * 4541268 * 2
def baseEnd_4541268 : Nat := 777284421627414500588365

theorem tailTrace_4541268 : CollatzResearch.WordTrace tailWord_4541268 prefixEnd_4541268 777284421627414500588365 := by
  unfold tailWord_4541268
  simp only [CollatzResearch.WordTrace]
  refine ⟨82816825655884548835944229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110422434207846065114592305 82816825655884548835944229)
  ·
    refine ⟨15528154810478352906739543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82816825655884548835944229 15528154810478352906739543)
    ·
      refine ⟨23292232215717529360109315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15528154810478352906739543 23292232215717529360109315)
      ·
        refine ⟨34938348323576294040163973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23292232215717529360109315 34938348323576294040163973)
        ·
          refine ⟨6550940310670555132530745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34938348323576294040163973 6550940310670555132530745)
          ·
            refine ⟨4913205233002916349398059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6550940310670555132530745 4913205233002916349398059)
            ·
              refine ⟨7369807849504374524097089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913205233002916349398059 7369807849504374524097089)
              ·
                refine ⟨5527355887128280893072817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7369807849504374524097089 5527355887128280893072817)
                ·
                  refine ⟨4145516915346210669804613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527355887128280893072817 4145516915346210669804613)
                  ·
                    refine ⟨777284421627414500588365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145516915346210669804613 777284421627414500588365)
                    ·
                      rfl

theorem cell23_4541268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4541268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541268 prefixEnd_4541268 := by exact prefixLift 4541268
  have htrace : WordTrace (prefixWord ++ tailWord_4541268) baseStart_4541268 baseEnd_4541268 := by
    simpa [prefixWord, tailWord_4541268, baseEnd_4541268] using wordTrace_append hprefix tailTrace_4541268
  have hstable : (prefixWord ++ tailWord_4541268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541268).length < 2 ^ (prefixWord ++ tailWord_4541268).sum := by decide
  have hdescent : baseEnd_4541268 < baseStart_4541268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541317 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_4541317 : Nat := 118140960795 + 4541317 * 2 ^ 59
def prefixEnd_4541317 : Nat := 4983230072969 + 3 ^ 40 * 4541317 * 2
def baseEnd_4541317 : Nat := 2331878425434313810052369

theorem tailTrace_4541317 : CollatzResearch.WordTrace tailWord_4541317 prefixEnd_4541317 2331878425434313810052369 := by
  unfold tailWord_4541317
  simp only [CollatzResearch.WordTrace]
  refine ⟨165635438488591579040422205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110423625659061052693614803 165635438488591579040422205)
  ·
    refine ⟨62113289433221842140158327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165635438488591579040422205 62113289433221842140158327)
    ·
      refine ⟨93169934149832763210237491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62113289433221842140158327 93169934149832763210237491)
      ·
        refine ⟨139754901224749144815356237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93169934149832763210237491 139754901224749144815356237)
        ·
          refine ⟨52408087959280929305758589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139754901224749144815356237 52408087959280929305758589)
          ·
            refine ⟨19653032984730348489659471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52408087959280929305758589 19653032984730348489659471)
            ·
              refine ⟨29479549477095522734489207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19653032984730348489659471 29479549477095522734489207)
              ·
                refine ⟨44219324215643284101733811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29479549477095522734489207 44219324215643284101733811)
                ·
                  refine ⟨66328986323464926152600717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44219324215643284101733811 66328986323464926152600717)
                  ·
                    refine ⟨24873369871299347307225269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66328986323464926152600717 24873369871299347307225269)
                    ·
                      refine ⟨2331878425434313810052369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24873369871299347307225269 2331878425434313810052369)
                      ·
                        rfl

theorem cell23_4541317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_4541317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541317 prefixEnd_4541317 := by exact prefixLift 4541317
  have htrace : WordTrace (prefixWord ++ tailWord_4541317) baseStart_4541317 baseEnd_4541317 := by
    simpa [prefixWord, tailWord_4541317, baseEnd_4541317] using wordTrace_append hprefix tailTrace_4541317
  have hstable : (prefixWord ++ tailWord_4541317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541317).length < 2 ^ (prefixWord ++ tailWord_4541317).sum := by decide
  have hdescent : baseEnd_4541317 < baseStart_4541317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541348 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_4541348 : Nat := 118140960795 + 4541348 * 2 ^ 59
def prefixEnd_4541348 : Nat := 4983230072969 + 3 ^ 40 * 4541348 * 2
def baseEnd_4541348 : Nat := 2331894343334603188764727

theorem tailTrace_4541348 : CollatzResearch.WordTrace tailWord_4541348 prefixEnd_4541348 2331894343334603188764727 := by
  unfold tailWord_4541348
  simp only [CollatzResearch.WordTrace]
  refine ⟨82818284575739635667400349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110424379434319514223200465 82818284575739635667400349)
  ·
    refine ⟨31056856715902363375275131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82818284575739635667400349 31056856715902363375275131)
    ·
      refine ⟨46585285073853545062912697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31056856715902363375275131 46585285073853545062912697)
      ·
        refine ⟨34938963805390158797184523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46585285073853545062912697 34938963805390158797184523)
        ·
          refine ⟨52408445708085238195776785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34938963805390158797184523 52408445708085238195776785)
          ·
            refine ⟨39306334281063928646832589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52408445708085238195776785 39306334281063928646832589)
            ·
              refine ⟨14739875355398973242562221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39306334281063928646832589 14739875355398973242562221)
              ·
                refine ⟨5527453258274614965960833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14739875355398973242562221 5527453258274614965960833)
                ·
                  refine ⟨4145589943705961224470625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527453258274614965960833 4145589943705961224470625)
                  ·
                    refine ⟨3109192457779470918352969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4145589943705961224470625 3109192457779470918352969)
                    ·
                      refine ⟨2331894343334603188764727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109192457779470918352969 2331894343334603188764727)
                      ·
                        rfl

theorem cell23_4541348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_4541348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541348 prefixEnd_4541348 := by exact prefixLift 4541348
  have htrace : WordTrace (prefixWord ++ tailWord_4541348) baseStart_4541348 baseEnd_4541348 := by
    simpa [prefixWord, tailWord_4541348, baseEnd_4541348] using wordTrace_append hprefix tailTrace_4541348
  have hstable : (prefixWord ++ tailWord_4541348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541348).length < 2 ^ (prefixWord ++ tailWord_4541348).sum := by decide
  have hdescent : baseEnd_4541348 < baseStart_4541348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541367 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 7]
def baseStart_4541367 : Nat := 118140960795 + 4541367 * 2 ^ 59
def prefixEnd_4541367 : Nat := 4983230072969 + 3 ^ 40 * 4541367 * 2
def baseEnd_4541367 : Nat := 777301366489012871475713

theorem tailTrace_4541367 : CollatzResearch.WordTrace tailWord_4541367 prefixEnd_4541367 777301366489012871475713 := by
  unfold tailWord_4541367
  simp only [CollatzResearch.WordTrace]
  refine ⟨165637262138410437579742355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110424841425606958386494903 165637262138410437579742355)
  ·
    refine ⟨248455893207615656369613533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165637262138410437579742355 248455893207615656369613533)
    ·
      refine ⟨93170959952855871138605075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248455893207615656369613533 93170959952855871138605075)
      ·
        refine ⟨139756439929283806707907613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93170959952855871138605075 139756439929283806707907613)
        ·
          refine ⟨52408664973481427515465355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139756439929283806707907613 52408664973481427515465355)
          ·
            refine ⟨78612997460222141273198033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52408664973481427515465355 78612997460222141273198033)
            ·
              refine ⟨58959748095166605954898525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78612997460222141273198033 58959748095166605954898525)
              ·
                refine ⟨22109905535687477233086947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58959748095166605954898525 22109905535687477233086947)
                ·
                  refine ⟨33164858303531215849630421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22109905535687477233086947 33164858303531215849630421)
                  ·
                    refine ⟨777301366489012871475713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33164858303531215849630421 777301366489012871475713)
                    ·
                      rfl

theorem cell23_4541367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_4541367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541367 prefixEnd_4541367 := by exact prefixLift 4541367
  have htrace : WordTrace (prefixWord ++ tailWord_4541367) baseStart_4541367 baseEnd_4541367 := by
    simpa [prefixWord, tailWord_4541367, baseEnd_4541367] using wordTrace_append hprefix tailTrace_4541367
  have hstable : (prefixWord ++ tailWord_4541367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541367).length < 2 ^ (prefixWord ++ tailWord_4541367).sum := by decide
  have hdescent : baseEnd_4541367 < baseStart_4541367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541398 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_4541398 : Nat := 118140960795 + 4541398 * 2 ^ 59
def prefixEnd_4541398 : Nat := 4983230072969 + 3 ^ 40 * 4541398 * 2
def baseEnd_4541398 : Nat := 2331920017367327993139497

theorem tailTrace_4541398 : CollatzResearch.WordTrace tailWord_4541398 prefixEnd_4541398 2331920017367327993139497 := by
  unfold tailWord_4541398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10352399550081133117132553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110425595200865419916080565 10352399550081133117132553)
  ·
    refine ⟨7764299662560849837849415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10352399550081133117132553 7764299662560849837849415)
    ·
      refine ⟨11646449493841274756774123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7764299662560849837849415 11646449493841274756774123)
      ·
        refine ⟨17469674240761912135161185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11646449493841274756774123 17469674240761912135161185)
        ·
          refine ⟨13102255680571434101370889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17469674240761912135161185 13102255680571434101370889)
          ·
            refine ⟨9826691760428575576028167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13102255680571434101370889 9826691760428575576028167)
            ·
              refine ⟨14740037640642863364042251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9826691760428575576028167 14740037640642863364042251)
              ·
                refine ⟨22110056460964295046063377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14740037640642863364042251 22110056460964295046063377)
                ·
                  refine ⟨16582542345723221284547533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22110056460964295046063377 16582542345723221284547533)
                  ·
                    refine ⟨6218453379646207981705325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16582542345723221284547533 6218453379646207981705325)
                    ·
                      refine ⟨2331920017367327993139497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218453379646207981705325 2331920017367327993139497)
                      ·
                        rfl

theorem cell23_4541398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_4541398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541398 prefixEnd_4541398 := by exact prefixLift 4541398
  have htrace : WordTrace (prefixWord ++ tailWord_4541398) baseStart_4541398 baseEnd_4541398 := by
    simpa [prefixWord, tailWord_4541398, baseEnd_4541398] using wordTrace_append hprefix tailTrace_4541398
  have hstable : (prefixWord ++ tailWord_4541398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541398).length < 2 ^ (prefixWord ++ tailWord_4541398).sum := by decide
  have hdescent : baseEnd_4541398 < baseStart_4541398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541417 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_4541417 : Nat := 118140960795 + 4541417 * 2 ^ 59
def prefixEnd_4541417 : Nat := 4983230072969 + 3 ^ 40 * 4541417 * 2
def baseEnd_4541417 : Nat := 2331929773499763418801909

theorem tailTrace_4541417 : CollatzResearch.WordTrace tailWord_4541417 prefixEnd_4541417 2331929773499763418801909 := by
  unfold tailWord_4541417
  simp only [CollatzResearch.WordTrace]
  refine ⟨165639085788229296119062505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110426057192152864079375003 165639085788229296119062505)
  ·
    refine ⟨124229314341171972089296879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165639085788229296119062505 124229314341171972089296879)
    ·
      refine ⟨186343971511757958133945319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124229314341171972089296879 186343971511757958133945319)
      ·
        refine ⟨279515957267636937200917979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186343971511757958133945319 279515957267636937200917979)
        ·
          refine ⟨419273935901455405801376969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279515957267636937200917979 419273935901455405801376969)
          ·
            refine ⟨314455451926091554351032727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419273935901455405801376969 314455451926091554351032727)
            ·
              refine ⟨471683177889137331526549091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314455451926091554351032727 471683177889137331526549091)
              ·
                refine ⟨707524766833705997289823637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471683177889137331526549091 707524766833705997289823637)
                ·
                  refine ⟨33165223445329968622960483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 707524766833705997289823637 33165223445329968622960483)
                  ·
                    refine ⟨49747835167994952934440725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33165223445329968622960483 49747835167994952934440725)
                    ·
                      refine ⟨2331929773499763418801909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49747835167994952934440725 2331929773499763418801909)
                      ·
                        rfl

theorem cell23_4541417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_4541417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541417 prefixEnd_4541417 := by exact prefixLift 4541417
  have htrace : WordTrace (prefixWord ++ tailWord_4541417) baseStart_4541417 baseEnd_4541417 := by
    simpa [prefixWord, tailWord_4541417, baseEnd_4541417] using wordTrace_append hprefix tailTrace_4541417
  have hstable : (prefixWord ++ tailWord_4541417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541417).length < 2 ^ (prefixWord ++ tailWord_4541417).sum := by decide
  have hdescent : baseEnd_4541417 < baseStart_4541417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541448 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 1, 4]
def baseStart_4541448 : Nat := 118140960795 + 4541448 * 2 ^ 59
def prefixEnd_4541448 : Nat := 4983230072969 + 3 ^ 40 * 4541448 * 2
def baseEnd_4541448 : Nat := 777315230466684265838089

theorem tailTrace_4541448 : CollatzResearch.WordTrace tailWord_4541448 prefixEnd_4541448 777315230466684265838089 := by
  unfold tailWord_4541448
  simp only [CollatzResearch.WordTrace]
  refine ⟨82820108225558494206720499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110426810967411325608960665 82820108225558494206720499)
  ·
    refine ⟨124230162338337741310080749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82820108225558494206720499 124230162338337741310080749)
    ·
      refine ⟨46586310876876652991280281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124230162338337741310080749 46586310876876652991280281)
      ·
        refine ⟨34939733157657489743460211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46586310876876652991280281 34939733157657489743460211)
        ·
          refine ⟨52409599736486234615190317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34939733157657489743460211 52409599736486234615190317)
          ·
            refine ⟨19653599901182337980696369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52409599736486234615190317 19653599901182337980696369)
            ·
              refine ⟨14740199925886753485522277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19653599901182337980696369 14740199925886753485522277)
              ·
                refine ⟨2763787486103766278535427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14740199925886753485522277 2763787486103766278535427)
                ·
                  refine ⟨4145681229155649417803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763787486103766278535427 4145681229155649417803141)
                  ·
                    refine ⟨777315230466684265838089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145681229155649417803141 777315230466684265838089)
                    ·
                      rfl

theorem cell23_4541448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_4541448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541448 prefixEnd_4541448 := by exact prefixLift 4541448
  have htrace : WordTrace (prefixWord ++ tailWord_4541448) baseStart_4541448 baseEnd_4541448 := by
    simpa [prefixWord, tailWord_4541448, baseEnd_4541448] using wordTrace_append hprefix tailTrace_4541448
  have hstable : (prefixWord ++ tailWord_4541448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541448).length < 2 ^ (prefixWord ++ tailWord_4541448).sum := by decide
  have hdescent : baseEnd_4541448 < baseStart_4541448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541482 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4541482 : Nat := 118140960795 + 4541482 * 2 ^ 59
def prefixEnd_4541482 : Nat := 4983230072969 + 3 ^ 40 * 4541482 * 2
def baseEnd_4541482 : Nat := 777321049914101888163037

theorem tailTrace_4541482 : CollatzResearch.WordTrace tailWord_4541482 prefixEnd_4541482 777321049914101888163037 := by
  unfold tailWord_4541482
  simp only [CollatzResearch.WordTrace]
  refine ⟨41410364133248453055044675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110427637688662541480119133 41410364133248453055044675)
  ·
    refine ⟨62115546199872679582567013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41410364133248453055044675 62115546199872679582567013)
    ·
      refine ⟨11646664912476127421731315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62115546199872679582567013 11646664912476127421731315)
      ·
        refine ⟨17469997368714191132596973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11646664912476127421731315 17469997368714191132596973)
        ·
          refine ⟨6551249013267821674723865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17469997368714191132596973 6551249013267821674723865)
          ·
            refine ⟨4913436759950866256042899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6551249013267821674723865 4913436759950866256042899)
            ·
              refine ⟨7370155139926299384064349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913436759950866256042899 7370155139926299384064349)
              ·
                refine ⟨2763808177472362269024131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7370155139926299384064349 2763808177472362269024131)
                ·
                  refine ⟨4145712266208543403536197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763808177472362269024131 4145712266208543403536197)
                  ·
                    refine ⟨777321049914101888163037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145712266208543403536197 777321049914101888163037)
                    ·
                      rfl

theorem cell23_4541482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4541482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541482 prefixEnd_4541482 := by exact prefixLift 4541482
  have htrace : WordTrace (prefixWord ++ tailWord_4541482) baseStart_4541482 baseEnd_4541482 := by
    simpa [prefixWord, tailWord_4541482, baseEnd_4541482] using wordTrace_append hprefix tailTrace_4541482
  have hstable : (prefixWord ++ tailWord_4541482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541482).length < 2 ^ (prefixWord ++ tailWord_4541482).sum := by decide
  have hdescent : baseEnd_4541482 < baseStart_4541482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541528 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_4541528 : Nat := 118140960795 + 4541528 * 2 ^ 59
def prefixEnd_4541528 : Nat := 4983230072969 + 3 ^ 40 * 4541528 * 2
def baseEnd_4541528 : Nat := 2331986769852412484513899

theorem tailTrace_4541528 : CollatzResearch.WordTrace tailWord_4541528 prefixEnd_4541528 2331986769852412484513899 := by
  unfold tailWord_4541528
  simp only [CollatzResearch.WordTrace]
  refine ⟨82821567145413581038176619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110428756193884774717568825 82821567145413581038176619)
  ·
    refine ⟨124232350718120371557264929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82821567145413581038176619 124232350718120371557264929)
    ·
      refine ⟨93174263038590278667948697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124232350718120371557264929 93174263038590278667948697)
      ·
        refine ⟨69880697278942709000961523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93174263038590278667948697 69880697278942709000961523)
        ·
          refine ⟨104821045918414063501442285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69880697278942709000961523 104821045918414063501442285)
          ·
            refine ⟨39307892219405273813040857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104821045918414063501442285 39307892219405273813040857)
            ·
              refine ⟨29480919164553955359780643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39307892219405273813040857 29480919164553955359780643)
              ·
                refine ⟨44221378746830933039670965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29480919164553955359780643 44221378746830933039670965)
                ·
                  refine ⟨4145754257515399972469153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44221378746830933039670965 4145754257515399972469153)
                  ·
                    refine ⟨3109315693136549979351865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4145754257515399972469153 3109315693136549979351865)
                    ·
                      refine ⟨2331986769852412484513899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109315693136549979351865 2331986769852412484513899)
                      ·
                        rfl

theorem cell23_4541528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_4541528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541528 prefixEnd_4541528 := by exact prefixLift 4541528
  have htrace : WordTrace (prefixWord ++ tailWord_4541528) baseStart_4541528 baseEnd_4541528 := by
    simpa [prefixWord, tailWord_4541528, baseEnd_4541528] using wordTrace_append hprefix tailTrace_4541528
  have hstable : (prefixWord ++ tailWord_4541528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541528).length < 2 ^ (prefixWord ++ tailWord_4541528).sum := by decide
  have hdescent : baseEnd_4541528 < baseStart_4541528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541538 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4541538 : Nat := 118140960795 + 4541538 * 2 ^ 59
def prefixEnd_4541538 : Nat := 4983230072969 + 3 ^ 40 * 4541538 * 2
def baseEnd_4541538 : Nat := 777330634886319148462951

theorem tailTrace_4541538 : CollatzResearch.WordTrace tailWord_4541538 prefixEnd_4541538 777330634886319148462951 := by
  unfold tailWord_4541538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41410874755197733446054317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110428999347193955856144845 41410874755197733446054317)
  ·
    refine ⟨15529078033199150042270369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41410874755197733446054317 15529078033199150042270369)
    ·
      refine ⟨11646808524899362531702777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15529078033199150042270369 11646808524899362531702777)
      ·
        refine ⟨8735106393674521898777083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11646808524899362531702777 8735106393674521898777083)
        ·
          refine ⟨13102659590511782848165625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8735106393674521898777083 13102659590511782848165625)
          ·
            refine ⟨9826994692883837136124219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13102659590511782848165625 9826994692883837136124219)
            ·
              refine ⟨14740492039325755704186329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9826994692883837136124219 14740492039325755704186329)
              ·
                refine ⟨11055369029494316778139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14740492039325755704186329 11055369029494316778139747)
                ·
                  refine ⟨16583053544241475167209621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11055369029494316778139747 16583053544241475167209621)
                  ·
                    refine ⟨777330634886319148462951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16583053544241475167209621 777330634886319148462951)
                    ·
                      rfl

theorem cell23_4541538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4541538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541538 prefixEnd_4541538 := by exact prefixLift 4541538
  have htrace : WordTrace (prefixWord ++ tailWord_4541538) baseStart_4541538 baseEnd_4541538 := by
    simpa [prefixWord, tailWord_4541538, baseEnd_4541538] using wordTrace_append hprefix tailTrace_4541538
  have hstable : (prefixWord ++ tailWord_4541538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541538).length < 2 ^ (prefixWord ++ tailWord_4541538).sum := by decide
  have hdescent : baseEnd_4541538 < baseStart_4541538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541541 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_4541541 : Nat := 118140960795 + 4541541 * 2 ^ 59
def prefixEnd_4541541 : Nat := 4983230072969 + 3 ^ 40 * 4541541 * 2
def baseEnd_4541541 : Nat := 2331993445100920933651339

theorem tailTrace_4541541 : CollatzResearch.WordTrace tailWord_4541541 prefixEnd_4541541 2331993445100920933651339 := by
  unfold tailWord_4541541
  simp only [CollatzResearch.WordTrace]
  refine ⟨165643608439780065296576477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110429072293186710197717651 165643608439780065296576477)
  ·
    refine ⟨62116353164917524486216179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165643608439780065296576477 62116353164917524486216179)
    ·
      refine ⟨93174529747376286729324269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62116353164917524486216179 93174529747376286729324269)
      ·
        refine ⟨34940448655266107523496601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93174529747376286729324269 34940448655266107523496601)
        ·
          refine ⟨26205336491449580642622451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34940448655266107523496601 26205336491449580642622451)
          ·
            refine ⟨39308004737174370963933677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26205336491449580642622451 39308004737174370963933677)
            ·
              refine ⟨14740501776440389111475129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39308004737174370963933677 14740501776440389111475129)
              ·
                refine ⟨11055376332330291833606347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14740501776440389111475129 11055376332330291833606347)
                ·
                  refine ⟨16583064498495437750409521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11055376332330291833606347 16583064498495437750409521)
                  ·
                    refine ⟨12437298373871578312807141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16583064498495437750409521 12437298373871578312807141)
                    ·
                      refine ⟨2331993445100920933651339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12437298373871578312807141 2331993445100920933651339)
                      ·
                        rfl

theorem cell23_4541541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_4541541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541541 prefixEnd_4541541 := by exact prefixLift 4541541
  have htrace : WordTrace (prefixWord ++ tailWord_4541541) baseStart_4541541 baseEnd_4541541 := by
    simpa [prefixWord, tailWord_4541541, baseEnd_4541541] using wordTrace_append hprefix tailTrace_4541541
  have hstable : (prefixWord ++ tailWord_4541541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541541).length < 2 ^ (prefixWord ++ tailWord_4541541).sum := by decide
  have hdescent : baseEnd_4541541 < baseStart_4541541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541564 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_4541564 : Nat := 118140960795 + 4541564 * 2 ^ 59
def prefixEnd_4541564 : Nat := 4983230072969 + 3 ^ 40 * 4541564 * 2
def baseEnd_4541564 : Nat := 777335085051991447887911

theorem tailTrace_4541564 : CollatzResearch.WordTrace tailWord_4541564 prefixEnd_4541564 777335085051991447887911 := by
  unfold tailWord_4541564
  simp only [CollatzResearch.WordTrace]
  refine ⟨82822223659348370112331873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110429631545797826816442497 82822223659348370112331873)
  ·
    refine ⟨62116667744511277584248905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82822223659348370112331873 62116667744511277584248905)
    ·
      refine ⟨46587500808383458188186679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62116667744511277584248905 46587500808383458188186679)
      ·
        refine ⟨69881251212575187282280019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46587500808383458188186679 69881251212575187282280019)
        ·
          refine ⟨104821876818862780923420029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69881251212575187282280019 104821876818862780923420029)
          ·
            refine ⟨39308203807073542846282511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104821876818862780923420029 39308203807073542846282511)
            ·
              refine ⟨58962305710610314269423767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39308203807073542846282511 58962305710610314269423767)
              ·
                refine ⟨88443458565915471404135651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58962305710610314269423767 88443458565915471404135651)
                ·
                  refine ⟨132665187848873207106203477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88443458565915471404135651 132665187848873207106203477)
                  ·
                    refine ⟨777335085051991447887911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 132665187848873207106203477 777335085051991447887911)
                    ·
                      rfl

theorem cell23_4541564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_4541564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541564 prefixEnd_4541564 := by exact prefixLift 4541564
  have htrace : WordTrace (prefixWord ++ tailWord_4541564) baseStart_4541564 baseEnd_4541564 := by
    simpa [prefixWord, tailWord_4541564, baseEnd_4541564] using wordTrace_append hprefix tailTrace_4541564
  have hstable : (prefixWord ++ tailWord_4541564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541564).length < 2 ^ (prefixWord ++ tailWord_4541564).sum := by decide
  have hdescent : baseEnd_4541564 < baseStart_4541564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541578 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_4541578 : Nat := 118140960795 + 4541578 * 2 ^ 59
def prefixEnd_4541578 : Nat := 4983230072969 + 3 ^ 40 * 4541578 * 2
def baseEnd_4541578 : Nat := 2332012443885137288888669

theorem tailTrace_4541578 : CollatzResearch.WordTrace tailWord_4541578 prefixEnd_4541578 2332012443885137288888669 := by
  unfold tailWord_4541578
  simp only [CollatzResearch.WordTrace]
  refine ⟨41411239485161505153918347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110429971960430680410448925 41411239485161505153918347)
  ·
    refine ⟨62116859227742257730877521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41411239485161505153918347 62116859227742257730877521)
    ·
      refine ⟨46587644420806693298158141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62116859227742257730877521 46587644420806693298158141)
      ·
        refine ⟨17470366657802509986809303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46587644420806693298158141 17470366657802509986809303)
        ·
          refine ⟨26205549986703764980213955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17470366657802509986809303 26205549986703764980213955)
          ·
            refine ⟨39308324980055647470320933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26205549986703764980213955 39308324980055647470320933)
            ·
              refine ⟨7370310933760433900685175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39308324980055647470320933 7370310933760433900685175)
              ·
                refine ⟨11055466400640650851027763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370310933760433900685175 11055466400640650851027763)
                ·
                  refine ⟨16583199600960976276541645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11055466400640650851027763 16583199600960976276541645)
                  ·
                    refine ⟨6218699850360366103703117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16583199600960976276541645 6218699850360366103703117)
                    ·
                      refine ⟨2332012443885137288888669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218699850360366103703117 2332012443885137288888669)
                      ·
                        rfl

theorem cell23_4541578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_4541578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541578 prefixEnd_4541578 := by exact prefixLift 4541578
  have htrace : WordTrace (prefixWord ++ tailWord_4541578) baseStart_4541578 baseEnd_4541578 := by
    simpa [prefixWord, tailWord_4541578, baseEnd_4541578] using wordTrace_append hprefix tailTrace_4541578
  have hstable : (prefixWord ++ tailWord_4541578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541578).length < 2 ^ (prefixWord ++ tailWord_4541578).sum := by decide
  have hdescent : baseEnd_4541578 < baseStart_4541578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541599 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4541599 : Nat := 118140960795 + 4541599 * 2 ^ 59
def prefixEnd_4541599 : Nat := 4983230072969 + 3 ^ 40 * 4541599 * 2
def baseEnd_4541599 : Nat := 2332023226978881706726073

theorem tailTrace_4541599 : CollatzResearch.WordTrace tailWord_4541599 prefixEnd_4541599 2332023226978881706726073 := by
  unfold tailWord_4541599
  simp only [CollatzResearch.WordTrace]
  refine ⟨165645723873569941202187851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110430482582379960801458567 165645723873569941202187851)
  ·
    refine ⟨248468585810354911803281777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165645723873569941202187851 248468585810354911803281777)
    ·
      refine ⟨186351439357766183852461333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248468585810354911803281777 186351439357766183852461333)
      ·
        refine ⟨8735223719895289868084125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186351439357766183852461333 8735223719895289868084125)
        ·
          refine ⟨3275708894960733700531547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735223719895289868084125 3275708894960733700531547)
          ·
            refine ⟨4913563342441100550797321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275708894960733700531547 4913563342441100550797321)
            ·
              refine ⟨3685172506830825413097991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913563342441100550797321 3685172506830825413097991)
              ·
                refine ⟨5527758760246238119646987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685172506830825413097991 5527758760246238119646987)
                ·
                  refine ⟨8291638140369357179470481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527758760246238119646987 8291638140369357179470481)
                  ·
                    refine ⟨6218728605277017884602861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8291638140369357179470481 6218728605277017884602861)
                    ·
                      refine ⟨2332023226978881706726073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218728605277017884602861 2332023226978881706726073)
                      ·
                        rfl

theorem cell23_4541599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4541599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541599 prefixEnd_4541599 := by exact prefixLift 4541599
  have htrace : WordTrace (prefixWord ++ tailWord_4541599) baseStart_4541599 baseEnd_4541599 := by
    simpa [prefixWord, tailWord_4541599, baseEnd_4541599] using wordTrace_append hprefix tailTrace_4541599
  have hstable : (prefixWord ++ tailWord_4541599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541599).length < 2 ^ (prefixWord ++ tailWord_4541599).sum := by decide
  have hdescent : baseEnd_4541599 < baseStart_4541599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541605 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_4541605 : Nat := 118140960795 + 4541605 * 2 ^ 59
def prefixEnd_4541605 : Nat := 4983230072969 + 3 ^ 40 * 4541605 * 2
def baseEnd_4541605 : Nat := 2332026307862808683251045

theorem tailTrace_4541605 : CollatzResearch.WordTrace tailWord_4541605 prefixEnd_4541605 2332026307862808683251045 := by
  unfold tailWord_4541605
  simp only [CollatzResearch.WordTrace]
  refine ⟨165645942711548204226906269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110430628474365469484604179 165645942711548204226906269)
  ·
    refine ⟨62117228516830576585089851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165645942711548204226906269 62117228516830576585089851)
    ·
      refine ⟨93175842775245864877634777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62117228516830576585089851 93175842775245864877634777)
      ·
        refine ⟨69881882081434398658226083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93175842775245864877634777 69881882081434398658226083)
        ·
          refine ⟨104822823122151597987339125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69881882081434398658226083 104822823122151597987339125)
          ·
            refine ⟨9827139667701712311313043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104822823122151597987339125 9827139667701712311313043)
            ·
              refine ⟨14740709501552568466969565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9827139667701712311313043 14740709501552568466969565)
              ·
                refine ⟨5527766063082213175113587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14740709501552568466969565 5527766063082213175113587)
                ·
                  refine ⟨8291649094623319762670381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527766063082213175113587 8291649094623319762670381)
                  ·
                    refine ⟨3109368410483744911001393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8291649094623319762670381 3109368410483744911001393)
                    ·
                      refine ⟨2332026307862808683251045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109368410483744911001393 2332026307862808683251045)
                      ·
                        rfl

theorem cell23_4541605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_4541605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541605 prefixEnd_4541605 := by exact prefixLift 4541605
  have htrace : WordTrace (prefixWord ++ tailWord_4541605) baseStart_4541605 baseEnd_4541605 := by
    simpa [prefixWord, tailWord_4541605, baseEnd_4541605] using wordTrace_append hprefix tailTrace_4541605
  have hstable : (prefixWord ++ tailWord_4541605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541605).length < 2 ^ (prefixWord ++ tailWord_4541605).sum := by decide
  have hdescent : baseEnd_4541605 < baseStart_4541605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541631 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_4541631 : Nat := 118140960795 + 4541631 * 2 ^ 59
def prefixEnd_4541631 : Nat := 4983230072969 + 3 ^ 40 * 4541631 * 2
def baseEnd_4541631 : Nat := 2332039658359825581525925

theorem tailTrace_4541631 : CollatzResearch.WordTrace tailWord_4541631 prefixEnd_4541631 2332039658359825581525925 := by
  unfold tailWord_4541631
  simp only [CollatzResearch.WordTrace]
  refine ⟨165646891009454010667352747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110431260672969340444901831 165646891009454010667352747)
  ·
    refine ⟨248470336514181016001029121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165646891009454010667352747 248470336514181016001029121)
    ·
      refine ⟨186352752385635762000771841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248470336514181016001029121 186352752385635762000771841)
      ·
        refine ⟨139764564289226821500578881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186352752385635762000771841 139764564289226821500578881)
        ·
          refine ⟨104823423216920116125434161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139764564289226821500578881 104823423216920116125434161)
          ·
            refine ⟨78617567412690087094075621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104823423216920116125434161 78617567412690087094075621)
            ·
              refine ⟨14740793889879391330139179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78617567412690087094075621 14740793889879391330139179)
              ·
                refine ⟨22111190834819086995208769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14740793889879391330139179 22111190834819086995208769)
                ·
                  refine ⟨16583393126114315246406577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22111190834819086995208769 16583393126114315246406577)
                  ·
                    refine ⟨12437544844585736434804933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16583393126114315246406577 12437544844585736434804933)
                    ·
                      refine ⟨2332039658359825581525925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12437544844585736434804933 2332039658359825581525925)
                      ·
                        rfl

theorem cell23_4541631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_4541631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541631 prefixEnd_4541631 := by exact prefixLift 4541631
  have htrace : WordTrace (prefixWord ++ tailWord_4541631) baseStart_4541631 baseEnd_4541631 := by
    simpa [prefixWord, tailWord_4541631, baseEnd_4541631] using wordTrace_append hprefix tailTrace_4541631
  have hstable : (prefixWord ++ tailWord_4541631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541631).length < 2 ^ (prefixWord ++ tailWord_4541631).sum := by decide
  have hdescent : baseEnd_4541631 < baseStart_4541631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541675 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 5]
def baseStart_4541675 : Nat := 118140960795 + 4541675 * 2 ^ 59
def prefixEnd_4541675 : Nat := 4983230072969 + 3 ^ 40 * 4541675 * 2
def baseEnd_4541675 : Nat := 259118027945402601041747

theorem tailTrace_4541675 : CollatzResearch.WordTrace tailWord_4541675 prefixEnd_4541675 259118027945402601041747 := by
  unfold tailWord_4541675
  simp only [CollatzResearch.WordTrace]
  refine ⟨165648495821294606181954479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110432330547529737454636319 165648495821294606181954479)
  ·
    refine ⟨248472743731941909272931719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165648495821294606181954479 248472743731941909272931719)
    ·
      refine ⟨372709115597912863909397579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248472743731941909272931719 372709115597912863909397579)
      ·
        refine ⟨559063673396869295864096369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372709115597912863909397579 559063673396869295864096369)
        ·
          refine ⟨419297755047651971898072277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559063673396869295864096369 419297755047651971898072277)
          ·
            refine ⟨9827291133929343091361069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 419297755047651971898072277 9827291133929343091361069)
            ·
              refine ⟨3685234175223503659260401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9827291133929343091361069 3685234175223503659260401)
              ·
                refine ⟨2763925631417627744445301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685234175223503659260401 2763925631417627744445301)
                ·
                  refine ⟨259118027945402601041747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763925631417627744445301 259118027945402601041747)
                  ·
                    rfl

theorem cell23_4541675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 5].length) (baseStart_4541675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541675 prefixEnd_4541675 := by exact prefixLift 4541675
  have htrace : WordTrace (prefixWord ++ tailWord_4541675) baseStart_4541675 baseEnd_4541675 := by
    simpa [prefixWord, tailWord_4541675, baseEnd_4541675] using wordTrace_append hprefix tailTrace_4541675
  have hstable : (prefixWord ++ tailWord_4541675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541675).length < 2 ^ (prefixWord ++ tailWord_4541675).sum := by decide
  have hdescent : baseEnd_4541675 < baseStart_4541675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541708 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4541708 : Nat := 118140960795 + 4541708 * 2 ^ 59
def prefixEnd_4541708 : Nat := 4983230072969 + 3 ^ 40 * 4541708 * 2
def baseEnd_4541708 : Nat := 2332079196370221780263071

theorem tailTrace_4541708 : CollatzResearch.WordTrace tailWord_4541708 prefixEnd_4541708 2332079196370221780263071 := by
  unfold tailWord_4541708
  simp only [CollatzResearch.WordTrace]
  refine ⟨82824849715087526408952889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110433132953450035211937185 82824849715087526408952889)
  ·
    refine ⟨62118637286315644806714667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82824849715087526408952889 62118637286315644806714667)
    ·
      refine ⟨93177955929473467210072001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62118637286315644806714667 93177955929473467210072001)
      ·
        refine ⟨69883466947105100407554001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93177955929473467210072001 69883466947105100407554001)
        ·
          refine ⟨52412600210328825305665501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69883466947105100407554001 52412600210328825305665501)
          ·
            refine ⟨19654725078873309489624563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52412600210328825305665501 19654725078873309489624563)
            ·
              refine ⟨29482087618309964234436845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19654725078873309489624563 29482087618309964234436845)
              ·
                refine ⟨11055782856866236587913817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29482087618309964234436845 11055782856866236587913817)
                ·
                  refine ⟨8291837142649677440935363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11055782856866236587913817 8291837142649677440935363)
                  ·
                    refine ⟨12437755713974516161403045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8291837142649677440935363 12437755713974516161403045)
                    ·
                      refine ⟨2332079196370221780263071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12437755713974516161403045 2332079196370221780263071)
                      ·
                        rfl

theorem cell23_4541708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4541708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541708 prefixEnd_4541708 := by exact prefixLift 4541708
  have htrace : WordTrace (prefixWord ++ tailWord_4541708) baseStart_4541708 baseEnd_4541708 := by
    simpa [prefixWord, tailWord_4541708, baseEnd_4541708] using wordTrace_append hprefix tailTrace_4541708
  have hstable : (prefixWord ++ tailWord_4541708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541708).length < 2 ^ (prefixWord ++ tailWord_4541708).sum := by decide
  have hdescent : baseEnd_4541708 < baseStart_4541708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541725 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4541725 : Nat := 118140960795 + 4541725 * 2 ^ 59
def prefixEnd_4541725 : Nat := 4983230072969 + 3 ^ 40 * 4541725 * 2
def baseEnd_4541725 : Nat := 2332087925541348213750493

theorem tailTrace_4541725 : CollatzResearch.WordTrace tailWord_4541725 prefixEnd_4541725 2332087925541348213750493 := by
  unfold tailWord_4541725
  simp only [CollatzResearch.WordTrace]
  refine ⟨165650319471113464721274629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110433546314075643147516419 165650319471113464721274629)
  ·
    refine ⟨31059434900833774635238993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165650319471113464721274629 31059434900833774635238993)
    ·
      refine ⟨23294576175625330976429245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31059434900833774635238993 23294576175625330976429245)
      ·
        refine ⟨8735466065859499116160967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23294576175625330976429245 8735466065859499116160967)
        ·
          refine ⟨13103199098789248674241451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8735466065859499116160967 13103199098789248674241451)
          ·
            refine ⟨19654798648183873011362177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13103199098789248674241451 19654798648183873011362177)
            ·
              refine ⟨14741098986137904758521633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19654798648183873011362177 14741098986137904758521633)
              ·
                refine ⟨11055824239603428568891225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14741098986137904758521633 11055824239603428568891225)
                ·
                  refine ⟨8291868179702571426668419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11055824239603428568891225 8291868179702571426668419)
                  ·
                    refine ⟨12437802269553857140002629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8291868179702571426668419 12437802269553857140002629)
                    ·
                      refine ⟨2332087925541348213750493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12437802269553857140002629 2332087925541348213750493)
                      ·
                        rfl

theorem cell23_4541725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4541725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541725 prefixEnd_4541725 := by exact prefixLift 4541725
  have htrace : WordTrace (prefixWord ++ tailWord_4541725) baseStart_4541725 baseEnd_4541725 := by
    simpa [prefixWord, tailWord_4541725, baseEnd_4541725] using wordTrace_append hprefix tailTrace_4541725
  have hstable : (prefixWord ++ tailWord_4541725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541725).length < 2 ^ (prefixWord ++ tailWord_4541725).sum := by decide
  have hdescent : baseEnd_4541725 < baseStart_4541725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
