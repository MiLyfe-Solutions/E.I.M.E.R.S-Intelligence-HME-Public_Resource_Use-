import V185TrunkScan23Chunk0498

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2951372 : List Nat := [2, 2, 1, 6, 12]
def baseStart_2951372 : Nat := 118140960795 + 2951372 * 2 ^ 59
def prefixEnd_2951372 : Nat := 4983230072969 + 3 ^ 40 * 2951372 * 2
def baseEnd_2951372 : Nat := 2078837347354639200517

theorem tailTrace_2951372 : CollatzResearch.WordTrace tailWord_2951372 prefixEnd_2951372 2078837347354639200517 := by
  unfold tailWord_2951372
  simp only [CollatzResearch.WordTrace]
  refine ⟨53822690131845386526452185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71763586842460515368602913 53822690131845386526452185)
  ·
    refine ⟨40367017598884039894839139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53822690131845386526452185 40367017598884039894839139)
    ·
      refine ⟨60550526398326059842258709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40367017598884039894839139 60550526398326059842258709)
      ·
        refine ⟨2838305924921534055105877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60550526398326059842258709 2838305924921534055105877)
        ·
          refine ⟨2078837347354639200517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2838305924921534055105877 2078837347354639200517)
          ·
            rfl

theorem cell23_2951372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 12].length) (baseStart_2951372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951372 prefixEnd_2951372 := by exact prefixLift 2951372
  have htrace : WordTrace (prefixWord ++ tailWord_2951372) baseStart_2951372 baseEnd_2951372 := by
    simpa [prefixWord, tailWord_2951372, baseEnd_2951372] using wordTrace_append hprefix tailTrace_2951372
  have hstable : (prefixWord ++ tailWord_2951372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951372).length < 2 ^ (prefixWord ++ tailWord_2951372).sum := by decide
  have hdescent : baseEnd_2951372 < baseStart_2951372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951389 : List Nat := [1, 4, 3, 2, 1, 1, 3, 8]
def baseStart_2951389 : Nat := 118140960795 + 2951389 * 2 ^ 59
def prefixEnd_2951389 : Nat := 4983230072969 + 3 ^ 40 * 2951389 * 2
def baseEnd_2951389 : Nat := 56128931681209570765345

theorem tailTrace_2951389 : CollatzResearch.WordTrace tailWord_2951389 prefixEnd_2951389 56128931681209570765345 := by
  unfold tailWord_2951389
  simp only [CollatzResearch.WordTrace]
  refine ⟨107646000304629184956273221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71764000203086123304182147 107646000304629184956273221)
  ·
    refine ⟨20183625057117972179301229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107646000304629184956273221 20183625057117972179301229)
    ·
      refine ⟨7568859396419239567237961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20183625057117972179301229 7568859396419239567237961)
      ·
        refine ⟨5676644547314429675428471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7568859396419239567237961 5676644547314429675428471)
        ·
          refine ⟨8514966820971644513142707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676644547314429675428471 8514966820971644513142707)
          ·
            refine ⟨12772450231457466769714061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514966820971644513142707 12772450231457466769714061)
            ·
              refine ⟨4789668836796550038642773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12772450231457466769714061 4789668836796550038642773)
              ·
                refine ⟨56128931681209570765345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4789668836796550038642773 56128931681209570765345)
                ·
                  rfl

theorem cell23_2951389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 8].length) (baseStart_2951389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951389 prefixEnd_2951389 := by exact prefixLift 2951389
  have htrace : WordTrace (prefixWord ++ tailWord_2951389) baseStart_2951389 baseEnd_2951389 := by
    simpa [prefixWord, tailWord_2951389, baseEnd_2951389] using wordTrace_append hprefix tailTrace_2951389
  have hstable : (prefixWord ++ tailWord_2951389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951389).length < 2 ^ (prefixWord ++ tailWord_2951389).sum := by decide
  have hdescent : baseEnd_2951389 < baseStart_2951389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951402 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2951402 : Nat := 118140960795 + 2951402 * 2 ^ 59
def prefixEnd_2951402 : Nat := 4983230072969 + 3 ^ 40 * 2951402 * 2
def baseEnd_2951402 : Nat := 505162610213722286600585

theorem tailTrace_2951402 : CollatzResearch.WordTrace tailWord_2951402 prefixEnd_2951402 505162610213722286600585 := by
  unfold tailWord_2951402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26911618613395522044124115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71764316302388058784330973 26911618613395522044124115)
  ·
    refine ⟨40367427920093283066186173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26911618613395522044124115 40367427920093283066186173)
    ·
      refine ⟨15137785470034981149819815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40367427920093283066186173 15137785470034981149819815)
      ·
        refine ⟨22706678205052471724729723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15137785470034981149819815 22706678205052471724729723)
        ·
          refine ⟨34060017307578707587094585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22706678205052471724729723 34060017307578707587094585)
          ·
            refine ⟨25545012980684030690320939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34060017307578707587094585 25545012980684030690320939)
            ·
              refine ⟨38317519471026046035481409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25545012980684030690320939 38317519471026046035481409)
              ·
                refine ⟨28738139603269534526611057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38317519471026046035481409 28738139603269534526611057)
                ·
                  refine ⟨21553604702452150894958293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28738139603269534526611057 21553604702452150894958293)
                  ·
                    refine ⟨505162610213722286600585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21553604702452150894958293 505162610213722286600585)
                    ·
                      rfl

theorem cell23_2951402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2951402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951402 prefixEnd_2951402 := by exact prefixLift 2951402
  have htrace : WordTrace (prefixWord ++ tailWord_2951402) baseStart_2951402 baseEnd_2951402 := by
    simpa [prefixWord, tailWord_2951402, baseEnd_2951402] using wordTrace_append hprefix tailTrace_2951402
  have hstable : (prefixWord ++ tailWord_2951402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951402).length < 2 ^ (prefixWord ++ tailWord_2951402).sum := by decide
  have hdescent : baseEnd_2951402 < baseStart_2951402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951433 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 3]
def baseStart_2951433 : Nat := 118140960795 + 2951433 * 2 ^ 59
def prefixEnd_2951433 : Nat := 4983230072969 + 3 ^ 40 * 2951433 * 2
def baseEnd_2951433 : Nat := 1515503748541456238514113

theorem tailTrace_2951433 : CollatzResearch.WordTrace tailWord_2951433 prefixEnd_2951433 1515503748541456238514113 := by
  unfold tailWord_2951433
  simp only [CollatzResearch.WordTrace]
  refine ⟨107647605116469780470874953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71765070077646520313916635 107647605116469780470874953)
  ·
    refine ⟨80735703837352335353156215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107647605116469780470874953 80735703837352335353156215)
    ·
      refine ⟨121103555756028503029734323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80735703837352335353156215 121103555756028503029734323)
      ·
        refine ⟨181655333634042754544601485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121103555756028503029734323 181655333634042754544601485)
        ·
          refine ⟨68120750112766032954225557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181655333634042754544601485 68120750112766032954225557)
          ·
            refine ⟨3193160161535907794729323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68120750112766032954225557 3193160161535907794729323)
            ·
              refine ⟨4789740242303861692093985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193160161535907794729323 4789740242303861692093985)
              ·
                refine ⟨3592305181727896269070489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789740242303861692093985 3592305181727896269070489)
                ·
                  refine ⟨2694228886295922201802867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3592305181727896269070489 2694228886295922201802867)
                  ·
                    refine ⟨4041343329443883302704301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694228886295922201802867 4041343329443883302704301)
                    ·
                      refine ⟨1515503748541456238514113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041343329443883302704301 1515503748541456238514113)
                      ·
                        rfl

theorem cell23_2951433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_2951433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951433 prefixEnd_2951433 := by exact prefixLift 2951433
  have htrace : WordTrace (prefixWord ++ tailWord_2951433) baseStart_2951433 baseEnd_2951433 := by
    simpa [prefixWord, tailWord_2951433, baseEnd_2951433] using wordTrace_append hprefix tailTrace_2951433
  have hstable : (prefixWord ++ tailWord_2951433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951433).length < 2 ^ (prefixWord ++ tailWord_2951433).sum := by decide
  have hdescent : baseEnd_2951433 < baseStart_2951433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951439 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 3, 4, 2]
def baseStart_2951439 : Nat := 118140960795 + 2951439 * 2 ^ 59
def prefixEnd_2951439 : Nat := 4983230072969 + 3 ^ 40 * 2951439 * 2
def baseEnd_2951439 : Nat := 1515506829425383215039085

theorem tailTrace_2951439 : CollatzResearch.WordTrace tailWord_2951439 prefixEnd_2951439 1515506829425383215039085 := by
  unfold tailWord_2951439
  simp only [CollatzResearch.WordTrace]
  refine ⟨107647823954448043495593371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71765215969632028997062247 107647823954448043495593371)
  ·
    refine ⟨161471735931672065243390057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107647823954448043495593371 161471735931672065243390057)
    ·
      refine ⟨121103801948754048932542543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161471735931672065243390057 121103801948754048932542543)
      ·
        refine ⟨181655702923131073398813815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121103801948754048932542543 181655702923131073398813815)
        ·
          refine ⟨272483554384696610098220723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181655702923131073398813815 272483554384696610098220723)
          ·
            refine ⟨408725331577044915147331085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272483554384696610098220723 408725331577044915147331085)
            ·
              refine ⟨153271999341391843180249157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408725331577044915147331085 153271999341391843180249157)
              ·
                refine ⟨28738499876510970596296717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153271999341391843180249157 28738499876510970596296717)
                ·
                  refine ⟨10776937453691613973611269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28738499876510970596296717 10776937453691613973611269)
                  ·
                    refine ⟨2020675772567177620052113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10776937453691613973611269 2020675772567177620052113)
                    ·
                      refine ⟨1515506829425383215039085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020675772567177620052113 1515506829425383215039085)
                      ·
                        rfl

theorem cell23_2951439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4, 2].length) (baseStart_2951439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951439 prefixEnd_2951439 := by exact prefixLift 2951439
  have htrace : WordTrace (prefixWord ++ tailWord_2951439) baseStart_2951439 baseEnd_2951439 := by
    simpa [prefixWord, tailWord_2951439, baseEnd_2951439] using wordTrace_append hprefix tailTrace_2951439
  have hstable : (prefixWord ++ tailWord_2951439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951439).length < 2 ^ (prefixWord ++ tailWord_2951439).sum := by decide
  have hdescent : baseEnd_2951439 < baseStart_2951439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951450 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_2951450 : Nat := 118140960795 + 2951450 * 2 ^ 59
def prefixEnd_2951450 : Nat := 4983230072969 + 3 ^ 40 * 2951450 * 2
def baseEnd_2951450 : Nat := 1515512477712582672001535

theorem tailTrace_2951450 : CollatzResearch.WordTrace tailWord_2951450 prefixEnd_2951450 1515512477712582672001535 := by
  unfold tailWord_2951450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26912056289352048093560951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71765483438272128249495869 26912056289352048093560951)
  ·
    refine ⟨40368084434028072140341427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26912056289352048093560951 40368084434028072140341427)
    ·
      refine ⟨60552126651042108210512141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40368084434028072140341427 60552126651042108210512141)
      ·
        refine ⟨22707047494140790578942053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60552126651042108210512141 22707047494140790578942053)
        ·
          refine ⟨4257571405151398233551635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22707047494140790578942053 4257571405151398233551635)
          ·
            refine ⟨6386357107727097350327453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257571405151398233551635 6386357107727097350327453)
            ·
              refine ⟨2394883915397661506372795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6386357107727097350327453 2394883915397661506372795)
              ·
                refine ⟨3592325873096492259559193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394883915397661506372795 3592325873096492259559193)
                ·
                  refine ⟨2694244404822369194669395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3592325873096492259559193 2694244404822369194669395)
                  ·
                    refine ⟨4041366607233553792004093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694244404822369194669395 4041366607233553792004093)
                    ·
                      refine ⟨1515512477712582672001535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041366607233553792004093 1515512477712582672001535)
                      ·
                        rfl

theorem cell23_2951450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_2951450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951450 prefixEnd_2951450 := by exact prefixLift 2951450
  have htrace : WordTrace (prefixWord ++ tailWord_2951450) baseStart_2951450 baseEnd_2951450 := by
    simpa [prefixWord, tailWord_2951450, baseEnd_2951450] using wordTrace_append hprefix tailTrace_2951450
  have hstable : (prefixWord ++ tailWord_2951450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951450).length < 2 ^ (prefixWord ++ tailWord_2951450).sum := by decide
  have hdescent : baseEnd_2951450 < baseStart_2951450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951476 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2951476 : Nat := 118140960795 + 2951476 * 2 ^ 59
def prefixEnd_2951476 : Nat := 4983230072969 + 3 ^ 40 * 2951476 * 2
def baseEnd_2951476 : Nat := 1515525828209599570276415

theorem tailTrace_2951476 : CollatzResearch.WordTrace tailWord_2951476 prefixEnd_2951476 1515525828209599570276415 := by
  unfold tailWord_2951476
  simp only [CollatzResearch.WordTrace]
  refine ⟨53824586727656999407345141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71766115636875999209793521 53824586727656999407345141)
  ·
    refine ⟨5046055005717843694438607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53824586727656999407345141 5046055005717843694438607)
    ·
      refine ⟨7569082508576765541657911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5046055005717843694438607 7569082508576765541657911)
      ·
        refine ⟨11353623762865148312486867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569082508576765541657911 11353623762865148312486867)
        ·
          refine ⟨17030435644297722468730301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11353623762865148312486867 17030435644297722468730301)
          ·
            refine ⟨6386413366611645925773863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17030435644297722468730301 6386413366611645925773863)
            ·
              refine ⟨9579620049917468888660795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386413366611645925773863 9579620049917468888660795)
              ·
                refine ⟨14369430074876203332991193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9579620049917468888660795 14369430074876203332991193)
                ·
                  refine ⟨10777072556157152499743395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14369430074876203332991193 10777072556157152499743395)
                  ·
                    refine ⟨16165608834235728749615093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10777072556157152499743395 16165608834235728749615093)
                    ·
                      refine ⟨1515525828209599570276415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16165608834235728749615093 1515525828209599570276415)
                      ·
                        rfl

theorem cell23_2951476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2951476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951476 prefixEnd_2951476 := by exact prefixLift 2951476
  have htrace : WordTrace (prefixWord ++ tailWord_2951476) baseStart_2951476 baseEnd_2951476 := by
    simpa [prefixWord, tailWord_2951476, baseEnd_2951476] using wordTrace_append hprefix tailTrace_2951476
  have hstable : (prefixWord ++ tailWord_2951476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951476).length < 2 ^ (prefixWord ++ tailWord_2951476).sum := by decide
  have hdescent : baseEnd_2951476 < baseStart_2951476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951539 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 5, 4]
def baseStart_2951539 : Nat := 118140960795 + 2951539 * 2 ^ 59
def prefixEnd_2951539 : Nat := 4983230072969 + 3 ^ 40 * 2951539 * 2
def baseEnd_2951539 : Nat := 505186059163610941262875

theorem tailTrace_2951539 : CollatzResearch.WordTrace tailWord_2951539 prefixEnd_2951539 505186059163610941262875 := by
  unfold tailWord_2951539
  simp only [CollatzResearch.WordTrace]
  refine ⟨107651471254085760574233671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71767647502723840382822447 107651471254085760574233671)
  ·
    refine ⟨161477206881128640861350507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107651471254085760574233671 161477206881128640861350507)
    ·
      refine ⟨242215810321692961292025761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161477206881128640861350507 242215810321692961292025761)
      ·
        refine ⟨181661857741269720969019321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242215810321692961292025761 181661857741269720969019321)
        ·
          refine ⟨136246393305952290726764491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181661857741269720969019321 136246393305952290726764491)
          ·
            refine ⟨204369589958928436090146737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136246393305952290726764491 204369589958928436090146737)
            ·
              refine ⟨153277192469196327067610053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204369589958928436090146737 153277192469196327067610053)
              ·
                refine ⟨28739473587974311325176885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153277192469196327067610053 28739473587974311325176885)
                ·
                  refine ⟨2694325648872591686735333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28739473587974311325176885 2694325648872591686735333)
                  ·
                    refine ⟨505186059163610941262875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694325648872591686735333 505186059163610941262875)
                    ·
                      rfl

theorem cell23_2951539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 4].length) (baseStart_2951539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951539 prefixEnd_2951539 := by exact prefixLift 2951539
  have htrace : WordTrace (prefixWord ++ tailWord_2951539) baseStart_2951539 baseEnd_2951539 := by
    simpa [prefixWord, tailWord_2951539, baseEnd_2951539] using wordTrace_append hprefix tailTrace_2951539
  have hstable : (prefixWord ++ tailWord_2951539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951539).length < 2 ^ (prefixWord ++ tailWord_2951539).sum := by decide
  have hdescent : baseEnd_2951539 < baseStart_2951539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951556 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2951556 : Nat := 118140960795 + 2951556 * 2 ^ 59
def prefixEnd_2951556 : Nat := 4983230072969 + 3 ^ 40 * 2951556 * 2
def baseEnd_2951556 : Nat := 505188968887319752425349

theorem tailTrace_2951556 : CollatzResearch.WordTrace tailWord_2951556 prefixEnd_2951556 505188968887319752425349 := by
  unfold tailWord_2951556
  simp only [CollatzResearch.WordTrace]
  refine ⟨53826045647512086238801261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71768060863349448318401681 53826045647512086238801261)
  ·
    refine ⟨20184767117817032339550473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53826045647512086238801261 20184767117817032339550473)
    ·
      refine ⟨15138575338362774254662855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20184767117817032339550473 15138575338362774254662855)
      ·
        refine ⟨22707863007544161381994283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15138575338362774254662855 22707863007544161381994283)
        ·
          refine ⟨34061794511316242072991425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22707863007544161381994283 34061794511316242072991425)
          ·
            refine ⟨25546345883487181554743569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34061794511316242072991425 25546345883487181554743569)
            ·
              refine ⟨19159759412615386166057677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25546345883487181554743569 19159759412615386166057677)
              ·
                refine ⟨7184909779730769812271629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19159759412615386166057677 7184909779730769812271629)
                ·
                  refine ⟨2694341167399038679601861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7184909779730769812271629 2694341167399038679601861)
                  ·
                    refine ⟨505188968887319752425349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694341167399038679601861 505188968887319752425349)
                    ·
                      rfl

theorem cell23_2951556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2951556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951556 prefixEnd_2951556 := by exact prefixLift 2951556
  have htrace : WordTrace (prefixWord ++ tailWord_2951556) baseStart_2951556 baseEnd_2951556 := by
    simpa [prefixWord, tailWord_2951556, baseEnd_2951556] using wordTrace_append hprefix tailTrace_2951556
  have hstable : (prefixWord ++ tailWord_2951556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951556).length < 2 ^ (prefixWord ++ tailWord_2951556).sum := by decide
  have hdescent : baseEnd_2951556 < baseStart_2951556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951596 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_2951596 : Nat := 118140960795 + 2951596 * 2 ^ 59
def prefixEnd_2951596 : Nat := 4983230072969 + 3 ^ 40 * 2951596 * 2
def baseEnd_2951596 : Nat := 1515587445888139100775863

theorem tailTrace_2951596 : CollatzResearch.WordTrace tailWord_2951596 prefixEnd_2951596 1515587445888139100775863 := by
  unfold tailWord_2951596
  simp only [CollatzResearch.WordTrace]
  refine ⟨53826775107439629654529321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71769033476586172872705761 53826775107439629654529321)
  ·
    refine ⟨40370081330579722240896991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53826775107439629654529321 40370081330579722240896991)
    ·
      refine ⟨60555121995869583361345487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40370081330579722240896991 60555121995869583361345487)
      ·
        refine ⟨90832682993804375042018231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60555121995869583361345487 90832682993804375042018231)
        ·
          refine ⟨136249024490706562563027347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90832682993804375042018231 136249024490706562563027347)
          ·
            refine ⟨204373536736059843844541021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136249024490706562563027347 204373536736059843844541021)
            ·
              refine ⟨76640076276022441441702883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204373536736059843844541021 76640076276022441441702883)
              ·
                refine ⟨114960114414033662162554325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76640076276022441441702883 114960114414033662162554325)
                ·
                  refine ⟨2694377681578913956934867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 114960114414033662162554325 2694377681578913956934867)
                  ·
                    refine ⟨4041566522368370935402301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694377681578913956934867 4041566522368370935402301)
                    ·
                      refine ⟨1515587445888139100775863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041566522368370935402301 1515587445888139100775863)
                      ·
                        rfl

theorem cell23_2951596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_2951596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951596 prefixEnd_2951596 := by exact prefixLift 2951596
  have htrace : WordTrace (prefixWord ++ tailWord_2951596) baseStart_2951596 baseEnd_2951596 := by
    simpa [prefixWord, tailWord_2951596, baseEnd_2951596] using wordTrace_append hprefix tailTrace_2951596
  have hstable : (prefixWord ++ tailWord_2951596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951596).length < 2 ^ (prefixWord ++ tailWord_2951596).sum := by decide
  have hdescent : baseEnd_2951596 < baseStart_2951596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951613 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2951613 : Nat := 118140960795 + 2951613 * 2 ^ 59
def prefixEnd_2951613 : Nat := 4983230072969 + 3 ^ 40 * 2951613 * 2
def baseEnd_2951613 : Nat := 1515596175059265534263285

theorem tailTrace_2951613 : CollatzResearch.WordTrace tailWord_2951613 prefixEnd_2951613 1515596175059265534263285 := by
  unfold tailWord_2951613
  simp only [CollatzResearch.WordTrace]
  refine ⟨107654170255817671212427493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71769446837211780808284995 107654170255817671212427493)
  ·
    refine ⟨20185156922965813352330155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107654170255817671212427493 20185156922965813352330155)
    ·
      refine ⟨30277735384448720028495233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20185156922965813352330155 30277735384448720028495233)
      ·
        refine ⟨22708301538336540021371425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30277735384448720028495233 22708301538336540021371425)
        ·
          refine ⟨17031226153752405016028569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22708301538336540021371425 17031226153752405016028569)
          ·
            refine ⟨12773419615314303762021427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17031226153752405016028569 12773419615314303762021427)
            ·
              refine ⟨19160129422971455643032141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12773419615314303762021427 19160129422971455643032141)
              ·
                refine ⟨7185048533614295866137053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19160129422971455643032141 7185048533614295866137053)
                ·
                  refine ⟨2694393200105360949801395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7185048533614295866137053 2694393200105360949801395)
                  ·
                    refine ⟨4041589800158041424702093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694393200105360949801395 4041589800158041424702093)
                    ·
                      refine ⟨1515596175059265534263285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041589800158041424702093 1515596175059265534263285)
                      ·
                        rfl

theorem cell23_2951613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2951613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951613 prefixEnd_2951613 := by exact prefixLift 2951613
  have htrace : WordTrace (prefixWord ++ tailWord_2951613) baseStart_2951613 baseEnd_2951613 := by
    simpa [prefixWord, tailWord_2951613, baseEnd_2951613] using wordTrace_append hprefix tailTrace_2951613
  have hstable : (prefixWord ++ tailWord_2951613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951613).length < 2 ^ (prefixWord ++ tailWord_2951613).sum := by decide
  have hdescent : baseEnd_2951613 < baseStart_2951613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951620 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 6]
def baseStart_2951620 : Nat := 118140960795 + 2951620 * 2 ^ 59
def prefixEnd_2951620 : Nat := 4983230072969 + 3 ^ 40 * 2951620 * 2
def baseEnd_2951620 : Nat := 168399974380427445208417

theorem tailTrace_2951620 : CollatzResearch.WordTrace tailWord_2951620 prefixEnd_2951620 168399974380427445208417 := by
  unfold tailWord_2951620
  simp only [CollatzResearch.WordTrace]
  refine ⟨53827212783396155703966157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71769617044528207605288209 53827212783396155703966157)
  ·
    refine ⟨20185204793773558388987309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53827212783396155703966157 20185204793773558388987309)
    ·
      refine ⟨7569451797665084395870241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20185204793773558388987309 7569451797665084395870241)
      ·
        refine ⟨5677088848248813296902681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7569451797665084395870241 5677088848248813296902681)
        ·
          refine ⟨4257816636186609972677011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5677088848248813296902681 4257816636186609972677011)
          ·
            refine ⟨6386724954279914959015517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257816636186609972677011 6386724954279914959015517)
            ·
              refine ⟨2395021857854968109630819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6386724954279914959015517 2395021857854968109630819)
              ·
                refine ⟨3592532786782452164446229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395021857854968109630819 3592532786782452164446229)
                ·
                  refine ⟨168399974380427445208417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3592532786782452164446229 168399974380427445208417)
                  ·
                    rfl

theorem cell23_2951620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_2951620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951620 prefixEnd_2951620 := by exact prefixLift 2951620
  have htrace : WordTrace (prefixWord ++ tailWord_2951620) baseStart_2951620 baseEnd_2951620 := by
    simpa [prefixWord, tailWord_2951620, baseEnd_2951620] using wordTrace_append hprefix tailTrace_2951620
  have hstable : (prefixWord ++ tailWord_2951620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951620).length < 2 ^ (prefixWord ++ tailWord_2951620).sum := by decide
  have hdescent : baseEnd_2951620 < baseStart_2951620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951647 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 1, 1, 3]
def baseStart_2951647 : Nat := 118140960795 + 2951647 * 2 ^ 59
def prefixEnd_2951647 : Nat := 4983230072969 + 3 ^ 40 * 2951647 * 2
def baseEnd_2951647 : Nat := 1515613633401518401238129

theorem tailTrace_2951647 : CollatzResearch.WordTrace tailWord_2951647 prefixEnd_2951647 1515613633401518401238129 := by
  unfold tailWord_2951647
  simp only [CollatzResearch.WordTrace]
  refine ⟨107655410337694495019165195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71770273558462996679443463 107655410337694495019165195)
  ·
    refine ⟨161483115506541742528747793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107655410337694495019165195 161483115506541742528747793)
    ·
      refine ⟨121112336629906306896560845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161483115506541742528747793 121112336629906306896560845)
      ·
        refine ⟨45417126236214865086210317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121112336629906306896560845 45417126236214865086210317)
        ·
          refine ⟨17031422338580574407328869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45417126236214865086210317 17031422338580574407328869)
          ·
            refine ⟨3193391688483857701374163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17031422338580574407328869 3193391688483857701374163)
            ·
              refine ⟨4790087532725786552061245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193391688483857701374163 4790087532725786552061245)
              ·
                refine ⟨1796282824772169957022967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4790087532725786552061245 1796282824772169957022967)
                ·
                  refine ⟨2694424237158254935534451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796282824772169957022967 2694424237158254935534451)
                  ·
                    refine ⟨4041636355737382403301677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694424237158254935534451 4041636355737382403301677)
                    ·
                      refine ⟨1515613633401518401238129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041636355737382403301677 1515613633401518401238129)
                      ·
                        rfl

theorem cell23_2951647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_2951647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951647 prefixEnd_2951647 := by exact prefixLift 2951647
  have htrace : WordTrace (prefixWord ++ tailWord_2951647) baseStart_2951647 baseEnd_2951647 := by
    simpa [prefixWord, tailWord_2951647, baseEnd_2951647] using wordTrace_append hprefix tailTrace_2951647
  have hstable : (prefixWord ++ tailWord_2951647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951647).length < 2 ^ (prefixWord ++ tailWord_2951647).sum := by decide
  have hdescent : baseEnd_2951647 < baseStart_2951647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951656 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2951656 : Nat := 118140960795 + 2951656 * 2 ^ 59
def prefixEnd_2951656 : Nat := 4983230072969 + 3 ^ 40 * 2951656 * 2
def baseEnd_2951656 : Nat := 1515618254727408866025587

theorem tailTrace_2951656 : CollatzResearch.WordTrace tailWord_2951656 prefixEnd_2951656 1515618254727408866025587 := by
  unfold tailWord_2951656
  simp only [CollatzResearch.WordTrace]
  refine ⟨53827869297330944778121411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71770492396441259704161881 53827869297330944778121411)
  ·
    refine ⟨80741803945996417167182117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53827869297330944778121411 80741803945996417167182117)
    ·
      refine ⟨15139088239874328218846647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80741803945996417167182117 15139088239874328218846647)
      ·
        refine ⟨22708632359811492328269971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15139088239874328218846647 22708632359811492328269971)
        ·
          refine ⟨34062948539717238492404957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22708632359811492328269971 34062948539717238492404957)
          ·
            refine ⟨12773605702393964434651859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34062948539717238492404957 12773605702393964434651859)
            ·
              refine ⟨19160408553590946651977789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12773605702393964434651859 19160408553590946651977789)
              ·
                refine ⟨7185153207596604994491671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19160408553590946651977789 7185153207596604994491671)
                ·
                  refine ⟨10777729811394907491737507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185153207596604994491671 10777729811394907491737507)
                  ·
                    refine ⟨16166594717092361237606261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10777729811394907491737507 16166594717092361237606261)
                    ·
                      refine ⟨1515618254727408866025587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16166594717092361237606261 1515618254727408866025587)
                      ·
                        rfl

theorem cell23_2951656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2951656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951656 prefixEnd_2951656 := by exact prefixLift 2951656
  have htrace : WordTrace (prefixWord ++ tailWord_2951656) baseStart_2951656 baseEnd_2951656 := by
    simpa [prefixWord, tailWord_2951656, baseEnd_2951656] using wordTrace_append hprefix tailTrace_2951656
  have hstable : (prefixWord ++ tailWord_2951656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951656).length < 2 ^ (prefixWord ++ tailWord_2951656).sum := by decide
  have hdescent : baseEnd_2951656 < baseStart_2951656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951679 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_2951679 : Nat := 118140960795 + 2951679 * 2 ^ 59
def prefixEnd_2951679 : Nat := 4983230072969 + 3 ^ 40 * 2951679 * 2
def baseEnd_2951679 : Nat := 1515630064782462276037981

theorem tailTrace_2951679 : CollatzResearch.WordTrace tailWord_2951679 prefixEnd_2951679 1515630064782462276037981 := by
  unfold tailWord_2951679
  simp only [CollatzResearch.WordTrace]
  refine ⟨107656577473578564484330091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71771051649052376322886727 107656577473578564484330091)
  ·
    refine ⟨161484866210367846726495137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107656577473578564484330091 161484866210367846726495137)
    ·
      refine ⟨121113649657775885044871353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161484866210367846726495137 121113649657775885044871353)
      ·
        refine ⟨90835237243331913783653515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121113649657775885044871353 90835237243331913783653515)
        ·
          refine ⟨136252855864997870675480273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90835237243331913783653515 136252855864997870675480273)
          ·
            refine ⟨102189641898748403006610205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136252855864997870675480273 102189641898748403006610205)
            ·
              refine ⟨38321115712030651127478827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102189641898748403006610205 38321115712030651127478827)
              ·
                refine ⟨57481673568045976691218241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38321115712030651127478827 57481673568045976691218241)
                ·
                  refine ⟨43111255176034482518413681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57481673568045976691218241 43111255176034482518413681)
                  ·
                    refine ⟨32333441382025861888810261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43111255176034482518413681 32333441382025861888810261)
                    ·
                      refine ⟨1515630064782462276037981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32333441382025861888810261 1515630064782462276037981)
                      ·
                        rfl

theorem cell23_2951679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_2951679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951679 prefixEnd_2951679 := by exact prefixLift 2951679
  have htrace : WordTrace (prefixWord ++ tailWord_2951679) baseStart_2951679 baseEnd_2951679 := by
    simpa [prefixWord, tailWord_2951679, baseEnd_2951679] using wordTrace_append hprefix tailTrace_2951679
  have hstable : (prefixWord ++ tailWord_2951679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951679).length < 2 ^ (prefixWord ++ tailWord_2951679).sum := by decide
  have hdescent : baseEnd_2951679 < baseStart_2951679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951687 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2951687 : Nat := 118140960795 + 2951687 * 2 ^ 59
def prefixEnd_2951687 : Nat := 4983230072969 + 3 ^ 40 * 2951687 * 2
def baseEnd_2951687 : Nat := 1515634172627698244737945

theorem tailTrace_2951687 : CollatzResearch.WordTrace tailWord_2951687 prefixEnd_2951687 1515634172627698244737945 := by
  unfold tailWord_2951687
  simp only [CollatzResearch.WordTrace]
  refine ⟨107656869257549581850621315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71771246171699721233747543 107656869257549581850621315)
  ·
    refine ⟨161485303886324372775931973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107656869257549581850621315 161485303886324372775931973)
    ·
      refine ⟨30278494478685819895487245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161485303886324372775931973 30278494478685819895487245)
      ·
        refine ⟨11354435429507182460807717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30278494478685819895487245 11354435429507182460807717)
        ·
          refine ⟨2128956643032596711401447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11354435429507182460807717 2128956643032596711401447)
          ·
            refine ⟨3193434964548895067102171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128956643032596711401447 3193434964548895067102171)
            ·
              refine ⟨4790152446823342600653257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193434964548895067102171 4790152446823342600653257)
              ·
                refine ⟨3592614335117506950489943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790152446823342600653257 3592614335117506950489943)
                ·
                  refine ⟨5388921502676260425734915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592614335117506950489943 5388921502676260425734915)
                  ·
                    refine ⟨8083382254014390638602373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388921502676260425734915 8083382254014390638602373)
                    ·
                      refine ⟨1515634172627698244737945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8083382254014390638602373 1515634172627698244737945)
                      ·
                        rfl

theorem cell23_2951687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2951687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951687 prefixEnd_2951687 := by exact prefixLift 2951687
  have htrace : WordTrace (prefixWord ++ tailWord_2951687) baseStart_2951687 baseEnd_2951687 := by
    simpa [prefixWord, tailWord_2951687, baseEnd_2951687] using wordTrace_append hprefix tailTrace_2951687
  have hstable : (prefixWord ++ tailWord_2951687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951687).length < 2 ^ (prefixWord ++ tailWord_2951687).sum := by decide
  have hdescent : baseEnd_2951687 < baseStart_2951687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951689 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_2951689 : Nat := 118140960795 + 2951689 * 2 ^ 59
def prefixEnd_2951689 : Nat := 4983230072969 + 3 ^ 40 * 2951689 * 2
def baseEnd_2951689 : Nat := 505211733196335745637645

theorem tailTrace_2951689 : CollatzResearch.WordTrace tailWord_2951689 prefixEnd_2951689 505211733196335745637645 := by
  unfold tailWord_2951689
  simp only [CollatzResearch.WordTrace]
  refine ⟨107656942203542336192194121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71771294802361557461462747 107656942203542336192194121)
  ·
    refine ⟨80742706652656752144145591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107656942203542336192194121 80742706652656752144145591)
    ·
      refine ⟨121114059978985128216218387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80742706652656752144145591 121114059978985128216218387)
      ·
        refine ⟨181671089968477692324327581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121114059978985128216218387 181671089968477692324327581)
        ·
          refine ⟨68126658738179134621622843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181671089968477692324327581 68126658738179134621622843)
          ·
            refine ⟨102189988107268701932434265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68126658738179134621622843 102189988107268701932434265)
            ·
              refine ⟨76642491080451526449325699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102189988107268701932434265 76642491080451526449325699)
              ·
                refine ⟨114963736620677289673988549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76642491080451526449325699 114963736620677289673988549)
                ·
                  refine ⟨21555700616376991813872853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114963736620677289673988549 21555700616376991813872853)
                  ·
                    refine ⟨505211733196335745637645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21555700616376991813872853 505211733196335745637645)
                    ·
                      rfl

theorem cell23_2951689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_2951689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951689 prefixEnd_2951689 := by exact prefixLift 2951689
  have htrace : WordTrace (prefixWord ++ tailWord_2951689) baseStart_2951689 baseEnd_2951689 := by
    simpa [prefixWord, tailWord_2951689, baseEnd_2951689] using wordTrace_append hprefix tailTrace_2951689
  have hstable : (prefixWord ++ tailWord_2951689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951689).length < 2 ^ (prefixWord ++ tailWord_2951689).sum := by decide
  have hdescent : baseEnd_2951689 < baseStart_2951689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951700 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2951700 : Nat := 118140960795 + 2951700 * 2 ^ 59
def prefixEnd_2951700 : Nat := 4983230072969 + 3 ^ 40 * 2951700 * 2
def baseEnd_2951700 : Nat := 1515640847876206693875385

theorem tailTrace_2951700 : CollatzResearch.WordTrace tailWord_2951700 prefixEnd_2951700 1515640847876206693875385 := by
  unfold tailWord_2951700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53828671703251242535422277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71771562271001656713896369 53828671703251242535422277)
  ·
    refine ⟨10092875944359607975391677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53828671703251242535422277 10092875944359607975391677)
    ·
      refine ⟨3784828479134852990771879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10092875944359607975391677 3784828479134852990771879)
      ·
        refine ⟨5677242718702279486157819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784828479134852990771879 5677242718702279486157819)
        ·
          refine ⟨8515864078053419229236729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677242718702279486157819 8515864078053419229236729)
          ·
            refine ⟨6386898058540064421927547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515864078053419229236729 6386898058540064421927547)
            ·
              refine ⟨9580347087810096632891321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386898058540064421927547 9580347087810096632891321)
              ·
                refine ⟨7185260315857572474668491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9580347087810096632891321 7185260315857572474668491)
                ·
                  refine ⟨10777890473786358712002737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185260315857572474668491 10777890473786358712002737)
                  ·
                    refine ⟨8083417855339769034002053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10777890473786358712002737 8083417855339769034002053)
                    ·
                      refine ⟨1515640847876206693875385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8083417855339769034002053 1515640847876206693875385)
                      ·
                        rfl

theorem cell23_2951700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2951700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951700 prefixEnd_2951700 := by exact prefixLift 2951700
  have htrace : WordTrace (prefixWord ++ tailWord_2951700) baseStart_2951700 baseEnd_2951700 := by
    simpa [prefixWord, tailWord_2951700, baseEnd_2951700] using wordTrace_append hprefix tailTrace_2951700
  have hstable : (prefixWord ++ tailWord_2951700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951700).length < 2 ^ (prefixWord ++ tailWord_2951700).sum := by decide
  have hdescent : baseEnd_2951700 < baseStart_2951700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951736 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_2951736 : Nat := 118140960795 + 2951736 * 2 ^ 59
def prefixEnd_2951736 : Nat := 4983230072969 + 3 ^ 40 * 2951736 * 2
def baseEnd_2951736 : Nat := 505219777726589517675073

theorem tailTrace_2951736 : CollatzResearch.WordTrace tailWord_2951736 prefixEnd_2951736 505219777726589517675073 := by
  unfold tailWord_2951736
  simp only [CollatzResearch.WordTrace]
  refine ⟨53829328217186031609577531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71772437622914708812770041 53829328217186031609577531)
  ·
    refine ⟨80743992325779047414366297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53829328217186031609577531 80743992325779047414366297)
    ·
      refine ⟨60557994244334285560774723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80743992325779047414366297 60557994244334285560774723)
      ·
        refine ⟨90836991366501428341162085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60557994244334285560774723 90836991366501428341162085)
        ·
          refine ⟨17031935881219017813967891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90836991366501428341162085 17031935881219017813967891)
          ·
            refine ⟨25547903821828526720951837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17031935881219017813967891 25547903821828526720951837)
            ·
              refine ⟨9580463933185697520356939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25547903821828526720951837 9580463933185697520356939)
              ·
                refine ⟨14370695899778546280535409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9580463933185697520356939 14370695899778546280535409)
                ·
                  refine ⟨10778021924833909710401557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14370695899778546280535409 10778021924833909710401557)
                  ·
                    refine ⟨505219777726589517675073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10778021924833909710401557 505219777726589517675073)
                    ·
                      rfl

theorem cell23_2951736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_2951736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951736 prefixEnd_2951736 := by exact prefixLift 2951736
  have htrace : WordTrace (prefixWord ++ tailWord_2951736) baseStart_2951736 baseEnd_2951736 := by
    simpa [prefixWord, tailWord_2951736, baseEnd_2951736] using wordTrace_append hprefix tailTrace_2951736
  have hstable : (prefixWord ++ tailWord_2951736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951736).length < 2 ^ (prefixWord ++ tailWord_2951736).sum := by decide
  have hdescent : baseEnd_2951736 < baseStart_2951736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951756 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2951756 : Nat := 118140960795 + 2951756 * 2 ^ 59
def prefixEnd_2951756 : Nat := 4983230072969 + 3 ^ 40 * 2951756 * 2
def baseEnd_2951756 : Nat := 1515669602792858474775127

theorem tailTrace_2951756 : CollatzResearch.WordTrace tailWord_2951756 prefixEnd_2951756 1515669602792858474775127 := by
  unfold tailWord_2951756
  simp only [CollatzResearch.WordTrace]
  refine ⟨53829692947149803317441561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71772923929533071089922081 53829692947149803317441561)
  ·
    refine ⟨40372269710362352488081171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53829692947149803317441561 40372269710362352488081171)
    ·
      refine ⟨60558404565543528732121757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40372269710362352488081171 60558404565543528732121757)
      ·
        refine ⟨22709401712078823274545659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60558404565543528732121757 22709401712078823274545659)
        ·
          refine ⟨34064102568118234911818489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22709401712078823274545659 34064102568118234911818489)
          ·
            refine ⟨25548076926088676183863867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34064102568118234911818489 25548076926088676183863867)
            ·
              refine ⟨38322115389133014275795801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548076926088676183863867 38322115389133014275795801)
              ·
                refine ⟨28741586541849760706846851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38322115389133014275795801 28741586541849760706846851)
                ·
                  refine ⟨43112379812774641060270277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28741586541849760706846851 43112379812774641060270277)
                  ·
                    refine ⟨8083571214895245198800677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43112379812774641060270277 8083571214895245198800677)
                    ·
                      refine ⟨1515669602792858474775127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8083571214895245198800677 1515669602792858474775127)
                      ·
                        rfl

theorem cell23_2951756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2951756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951756 prefixEnd_2951756 := by exact prefixLift 2951756
  have htrace : WordTrace (prefixWord ++ tailWord_2951756) baseStart_2951756 baseEnd_2951756 := by
    simpa [prefixWord, tailWord_2951756, baseEnd_2951756] using wordTrace_append hprefix tailTrace_2951756
  have hstable : (prefixWord ++ tailWord_2951756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951756).length < 2 ^ (prefixWord ++ tailWord_2951756).sum := by decide
  have hdescent : baseEnd_2951756 < baseStart_2951756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951764 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_2951764 : Nat := 118140960795 + 2951764 * 2 ^ 59
def prefixEnd_2951764 : Nat := 4983230072969 + 3 ^ 40 * 2951764 * 2
def baseEnd_2951764 : Nat := 1515673710638094443475091

theorem tailTrace_2951764 : CollatzResearch.WordTrace tailWord_2951764 prefixEnd_2951764 1515673710638094443475091 := by
  unfold tailWord_2951764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53829838839135312000587173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71773118452180416000782897 53829838839135312000587173)
  ·
    refine ⟨10093094782337871000110095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53829838839135312000587173 10093094782337871000110095)
    ·
      refine ⟨15139642173506806500165143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10093094782337871000110095 15139642173506806500165143)
      ·
        refine ⟨22709463260260209750247715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15139642173506806500165143 22709463260260209750247715)
        ·
          refine ⟨34064194890390314625371573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22709463260260209750247715 34064194890390314625371573)
          ·
            refine ⟨3193518270974091996128585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34064194890390314625371573 3193518270974091996128585)
            ·
              refine ⟨2395138703230568997096439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3193518270974091996128585 2395138703230568997096439)
              ·
                refine ⟨3592708054845853495644659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395138703230568997096439 3592708054845853495644659)
                ·
                  refine ⟨5389062082268780243466989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592708054845853495644659 5389062082268780243466989)
                  ·
                    refine ⟨2020898280850792591300121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5389062082268780243466989 2020898280850792591300121)
                    ·
                      refine ⟨1515673710638094443475091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020898280850792591300121 1515673710638094443475091)
                      ·
                        rfl

theorem cell23_2951764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_2951764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951764 prefixEnd_2951764 := by exact prefixLift 2951764
  have htrace : WordTrace (prefixWord ++ tailWord_2951764) baseStart_2951764 baseEnd_2951764 := by
    simpa [prefixWord, tailWord_2951764, baseEnd_2951764] using wordTrace_append hprefix tailTrace_2951764
  have hstable : (prefixWord ++ tailWord_2951764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951764).length < 2 ^ (prefixWord ++ tailWord_2951764).sum := by decide
  have hdescent : baseEnd_2951764 < baseStart_2951764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951777 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_2951777 : Nat := 118140960795 + 2951777 * 2 ^ 59
def prefixEnd_2951777 : Nat := 4983230072969 + 3 ^ 40 * 2951777 * 2
def baseEnd_2951777 : Nat := 1515680385886602892612531

theorem tailTrace_2951777 : CollatzResearch.WordTrace tailWord_2951777 prefixEnd_2951777 1515680385886602892612531 := by
  unfold tailWord_2951777
  simp only [CollatzResearch.WordTrace]
  refine ⟨107660151827223527221397585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71773434551482351480931723 107660151827223527221397585)
  ·
    refine ⟨80745113870417645416048189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107660151827223527221397585 80745113870417645416048189)
    ·
      refine ⟨30279417701406617031018071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80745113870417645416048189 30279417701406617031018071)
      ·
        refine ⟨45419126552109925546527107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30279417701406617031018071 45419126552109925546527107)
        ·
          refine ⟨68128689828164888319790661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45419126552109925546527107 68128689828164888319790661)
          ·
            refine ⟨12774129342780916559960749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68128689828164888319790661 12774129342780916559960749)
            ·
              refine ⟨4790298503542843709985281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12774129342780916559960749 4790298503542843709985281)
              ·
                refine ⟨3592723877657132782488961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790298503542843709985281 3592723877657132782488961)
                ·
                  refine ⟨2694542908242849586866721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3592723877657132782488961 2694542908242849586866721)
                  ·
                    refine ⟨2020907181182137190150041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2694542908242849586866721 2020907181182137190150041)
                    ·
                      refine ⟨1515680385886602892612531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020907181182137190150041 1515680385886602892612531)
                      ·
                        rfl

theorem cell23_2951777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_2951777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951777 prefixEnd_2951777 := by exact prefixLift 2951777
  have htrace : WordTrace (prefixWord ++ tailWord_2951777) baseStart_2951777 baseEnd_2951777 := by
    simpa [prefixWord, tailWord_2951777, baseEnd_2951777] using wordTrace_append hprefix tailTrace_2951777
  have hstable : (prefixWord ++ tailWord_2951777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951777).length < 2 ^ (prefixWord ++ tailWord_2951777).sum := by decide
  have hdescent : baseEnd_2951777 < baseStart_2951777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951794 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_2951794 : Nat := 118140960795 + 2951794 * 2 ^ 59
def prefixEnd_2951794 : Nat := 4983230072969 + 3 ^ 40 * 2951794 * 2
def baseEnd_2951794 : Nat := 1515689115057729326099953

theorem tailTrace_2951794 : CollatzResearch.WordTrace tailWord_2951794 prefixEnd_2951794 1515689115057729326099953 := by
  unfold tailWord_2951794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915192967040484781191609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71773847912107959416510957 26915192967040484781191609)
  ·
    refine ⟨20186394725280363585893707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26915192967040484781191609 20186394725280363585893707)
    ·
      refine ⟨30279592087920545378840561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20186394725280363585893707 30279592087920545378840561)
      ·
        refine ⟨22709694065940409034130421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30279592087920545378840561 22709694065940409034130421)
        ·
          refine ⟨2129033818681913346949727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22709694065940409034130421 2129033818681913346949727)
          ·
            refine ⟨3193550728022870020424591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129033818681913346949727 3193550728022870020424591)
            ·
              refine ⟨4790326092034305030636887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193550728022870020424591 4790326092034305030636887)
              ·
                refine ⟨7185489138051457545955331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790326092034305030636887 7185489138051457545955331)
                ·
                  refine ⟨10778233707077186318932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185489138051457545955331 10778233707077186318932997)
                  ·
                    refine ⟨2020918820076972434799937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10778233707077186318932997 2020918820076972434799937)
                    ·
                      refine ⟨1515689115057729326099953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020918820076972434799937 1515689115057729326099953)
                      ·
                        rfl

theorem cell23_2951794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_2951794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951794 prefixEnd_2951794 := by exact prefixLift 2951794
  have htrace : WordTrace (prefixWord ++ tailWord_2951794) baseStart_2951794 baseEnd_2951794 := by
    simpa [prefixWord, tailWord_2951794, baseEnd_2951794] using wordTrace_append hprefix tailTrace_2951794
  have hstable : (prefixWord ++ tailWord_2951794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951794).length < 2 ^ (prefixWord ++ tailWord_2951794).sum := by decide
  have hdescent : baseEnd_2951794 < baseStart_2951794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951833 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2951833 : Nat := 118140960795 + 2951833 * 2 ^ 59
def prefixEnd_2951833 : Nat := 4983230072969 + 3 ^ 40 * 2951833 * 2
def baseEnd_2951833 : Nat := 1515709140803254673512273

theorem tailTrace_2951833 : CollatzResearch.WordTrace tailWord_2951833 prefixEnd_2951833 1515709140803254673512273 := by
  unfold tailWord_2951833
  simp only [CollatzResearch.WordTrace]
  refine ⟨107662194315020648785436153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71774796210013765856957435 107662194315020648785436153)
  ·
    refine ⟨80746645736265486589077115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107662194315020648785436153 80746645736265486589077115)
    ·
      refine ⟨121119968604398229883615673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80746645736265486589077115 121119968604398229883615673)
      ·
        refine ⟨90839976453298672412711755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121119968604398229883615673 90839976453298672412711755)
        ·
          refine ⟨136259964679948008619067633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90839976453298672412711755 136259964679948008619067633)
          ·
            refine ⟨102194973509961006464300725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136259964679948008619067633 102194973509961006464300725)
            ·
              refine ⟨9580778766558844356028193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102194973509961006464300725 9580778766558844356028193)
              ·
                refine ⟨7185584074919133267021145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9580778766558844356028193 7185584074919133267021145)
                ·
                  refine ⟨5389188056189349950265859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185584074919133267021145 5389188056189349950265859)
                  ·
                    refine ⟨8083782084284024925398789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5389188056189349950265859 8083782084284024925398789)
                    ·
                      refine ⟨1515709140803254673512273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8083782084284024925398789 1515709140803254673512273)
                      ·
                        rfl

theorem cell23_2951833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2951833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951833 prefixEnd_2951833 := by exact prefixLift 2951833
  have htrace : WordTrace (prefixWord ++ tailWord_2951833) baseStart_2951833 baseEnd_2951833 := by
    simpa [prefixWord, tailWord_2951833, baseEnd_2951833] using wordTrace_append hprefix tailTrace_2951833
  have hstable : (prefixWord ++ tailWord_2951833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951833).length < 2 ^ (prefixWord ++ tailWord_2951833).sum := by decide
  have hdescent : baseEnd_2951833 < baseStart_2951833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951834 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_2951834 : Nat := 118140960795 + 2951834 * 2 ^ 59
def prefixEnd_2951834 : Nat := 4983230072969 + 3 ^ 40 * 2951834 * 2
def baseEnd_2951834 : Nat := 168412183809323241066641

theorem tailTrace_2951834 : CollatzResearch.WordTrace tailWord_2951834 prefixEnd_2951834 168412183809323241066641 := by
  unfold tailWord_2951834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915557697004256489055639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71774820525344683970815037 26915557697004256489055639)
  ·
    refine ⟨40373336545506384733583459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26915557697004256489055639 40373336545506384733583459)
    ·
      refine ⟨60560004818259577100375189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40373336545506384733583459 60560004818259577100375189)
      ·
        refine ⟨2838750225855917676580087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60560004818259577100375189 2838750225855917676580087)
        ·
          refine ⟨4258125338783876514870131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838750225855917676580087 4258125338783876514870131)
          ·
            refine ⟨6387188008175814772305197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258125338783876514870131 6387188008175814772305197)
            ·
              refine ⟨2395195503065930539614449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6387188008175814772305197 2395195503065930539614449)
              ·
                refine ⟨1796396627299447904710837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395195503065930539614449 1796396627299447904710837)
                ·
                  refine ⟨168412183809323241066641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1796396627299447904710837 168412183809323241066641)
                  ·
                    rfl

theorem cell23_2951834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_2951834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951834 prefixEnd_2951834 := by exact prefixLift 2951834
  have htrace : WordTrace (prefixWord ++ tailWord_2951834) baseStart_2951834 baseEnd_2951834 := by
    simpa [prefixWord, tailWord_2951834, baseEnd_2951834] using wordTrace_append hprefix tailTrace_2951834
  have hstable : (prefixWord ++ tailWord_2951834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951834).length < 2 ^ (prefixWord ++ tailWord_2951834).sum := by decide
  have hdescent : baseEnd_2951834 < baseStart_2951834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951843 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 3, 4]
def baseStart_2951843 : Nat := 118140960795 + 2951843 * 2 ^ 59
def prefixEnd_2951843 : Nat := 4983230072969 + 3 ^ 40 * 2951843 * 2
def baseEnd_2951843 : Nat := 505238091869933211462409

theorem tailTrace_2951843 : CollatzResearch.WordTrace tailWord_2951843 prefixEnd_2951843 505238091869933211462409 := by
  unfold tailWord_2951843
  simp only [CollatzResearch.WordTrace]
  refine ⟨107662559044984420493300183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71775039363322946995533455 107662559044984420493300183)
  ·
    refine ⟨161493838567476630739950275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107662559044984420493300183 161493838567476630739950275)
    ·
      refine ⟨242240757851214946109925413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161493838567476630739950275 242240757851214946109925413)
      ·
        refine ⟨45420142097102802395611015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242240757851214946109925413 45420142097102802395611015)
        ·
          refine ⟨68130213145654203593416523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45420142097102802395611015 68130213145654203593416523)
          ·
            refine ⟨102195319718481305390124785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68130213145654203593416523 102195319718481305390124785)
            ·
              refine ⟨76646489788860979042593589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102195319718481305390124785 76646489788860979042593589)
              ·
                refine ⟨7185608417705716785243149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76646489788860979042593589 7185608417705716785243149)
                ·
                  refine ⟨2694603156639643794466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7185608417705716785243149 2694603156639643794466181)
                  ·
                    refine ⟨505238091869933211462409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694603156639643794466181 505238091869933211462409)
                    ·
                      rfl

theorem cell23_2951843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 4].length) (baseStart_2951843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951843 prefixEnd_2951843 := by exact prefixLift 2951843
  have htrace : WordTrace (prefixWord ++ tailWord_2951843) baseStart_2951843 baseEnd_2951843 := by
    simpa [prefixWord, tailWord_2951843, baseEnd_2951843] using wordTrace_append hprefix tailTrace_2951843
  have hstable : (prefixWord ++ tailWord_2951843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951843).length < 2 ^ (prefixWord ++ tailWord_2951843).sum := by decide
  have hdescent : baseEnd_2951843 < baseStart_2951843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951903 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 3, 5]
def baseStart_2951903 : Nat := 118140960795 + 2951903 * 2 ^ 59
def prefixEnd_2951903 : Nat := 4983230072969 + 3 ^ 40 * 2951903 * 2
def baseEnd_2951903 : Nat := 505248361483023133212317

theorem tailTrace_2951903 : CollatzResearch.WordTrace tailWord_2951903 prefixEnd_2951903 505248361483023133212317 := by
  unfold tailWord_2951903
  simp only [CollatzResearch.WordTrace]
  refine ⟨107664747424767050740484363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71776498283178033826989575 107664747424767050740484363)
  ·
    refine ⟨161497121137150576110726545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107664747424767050740484363 161497121137150576110726545)
    ·
      refine ⟨121122840852862932083044909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161497121137150576110726545 121122840852862932083044909)
      ·
        refine ⟨45421065319823599531141841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121122840852862932083044909 45421065319823599531141841)
        ·
          refine ⟨34065798989867699648356381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45421065319823599531141841 34065798989867699648356381)
          ·
            refine ⟨12774674621200387368133643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34065798989867699648356381 12774674621200387368133643)
            ·
              refine ⟨19162011931800581052200465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12774674621200387368133643 19162011931800581052200465)
              ·
                refine ⟨14371508948850435789150349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19162011931800581052200465 14371508948850435789150349)
                ·
                  refine ⟨5389315855818913420931381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14371508948850435789150349 5389315855818913420931381)
                  ·
                    refine ⟨505248361483023133212317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5389315855818913420931381 505248361483023133212317)
                    ·
                      rfl

theorem cell23_2951903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_2951903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951903 prefixEnd_2951903 := by exact prefixLift 2951903
  have htrace : WordTrace (prefixWord ++ tailWord_2951903) baseStart_2951903 baseEnd_2951903 := by
    simpa [prefixWord, tailWord_2951903, baseEnd_2951903] using wordTrace_append hprefix tailTrace_2951903
  have hstable : (prefixWord ++ tailWord_2951903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951903).length < 2 ^ (prefixWord ++ tailWord_2951903).sum := by decide
  have hdescent : baseEnd_2951903 < baseStart_2951903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951917 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2951917 : Nat := 118140960795 + 2951917 * 2 ^ 59
def prefixEnd_2951917 : Nat := 4983230072969 + 3 ^ 40 * 2951917 * 2
def baseEnd_2951917 : Nat := 1515752273178232344861887

theorem tailTrace_2951917 : CollatzResearch.WordTrace tailWord_2951917 prefixEnd_2951917 1515752273178232344861887 := by
  unfold tailWord_2951917
  simp only [CollatzResearch.WordTrace]
  refine ⟨107665258046716331131494005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71776838697810887420996003 107665258046716331131494005)
  ·
    refine ⟨10093617941879656043577563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107665258046716331131494005 10093617941879656043577563)
    ·
      refine ⟨15140426912819484065366345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10093617941879656043577563 15140426912819484065366345)
      ·
        refine ⟨11355320184614613049024759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15140426912819484065366345 11355320184614613049024759)
        ·
          refine ⟨17032980276921919573537139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11355320184614613049024759 17032980276921919573537139)
          ·
            refine ⟨25549470415382879360305709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17032980276921919573537139 25549470415382879360305709)
            ·
              refine ⟨9581051405768579760114641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25549470415382879360305709 9581051405768579760114641)
              ·
                refine ⟨7185788554326434820085981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9581051405768579760114641 7185788554326434820085981)
                ·
                  refine ⟨2694670707872413057532243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7185788554326434820085981 2694670707872413057532243)
                  ·
                    refine ⟨4042006061808619586298365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694670707872413057532243 4042006061808619586298365)
                    ·
                      refine ⟨1515752273178232344861887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4042006061808619586298365 1515752273178232344861887)
                      ·
                        rfl

theorem cell23_2951917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2951917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951917 prefixEnd_2951917 := by exact prefixLift 2951917
  have htrace : WordTrace (prefixWord ++ tailWord_2951917) baseStart_2951917 baseEnd_2951917 := by
    simpa [prefixWord, tailWord_2951917, baseEnd_2951917] using wordTrace_append hprefix tailTrace_2951917
  have hstable : (prefixWord ++ tailWord_2951917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951917).length < 2 ^ (prefixWord ++ tailWord_2951917).sum := by decide
  have hdescent : baseEnd_2951917 < baseStart_2951917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951933 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2951933 : Nat := 118140960795 + 2951933 * 2 ^ 59
def prefixEnd_2951933 : Nat := 4983230072969 + 3 ^ 40 * 2951933 * 2
def baseEnd_2951933 : Nat := 505253496289568094087271

theorem tailTrace_2951933 : CollatzResearch.WordTrace tailWord_2951933 prefixEnd_2951933 505253496289568094087271 := by
  unfold tailWord_2951933
  simp only [CollatzResearch.WordTrace]
  refine ⟨107665841614658365864076453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71777227743105577242717635 107665841614658365864076453)
  ·
    refine ⟨20187345302748443599514335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107665841614658365864076453 20187345302748443599514335)
    ·
      refine ⟨30281017954122665399271503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20187345302748443599514335 30281017954122665399271503)
      ·
        refine ⟨45421526931183998098907255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30281017954122665399271503 45421526931183998098907255)
        ·
          refine ⟨68132290396775997148360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45421526931183998098907255 68132290396775997148360883)
          ·
            refine ⟨102198435595163995722541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68132290396775997148360883 102198435595163995722541325)
            ·
              refine ⟨38324413348186498395952997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102198435595163995722541325 38324413348186498395952997)
              ·
                refine ⟨7185827502784968449241187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38324413348186498395952997 7185827502784968449241187)
                ·
                  refine ⟨10778741254177452673861781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185827502784968449241187 10778741254177452673861781)
                  ·
                    refine ⟨505253496289568094087271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10778741254177452673861781 505253496289568094087271)
                    ·
                      rfl

theorem cell23_2951933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2951933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951933 prefixEnd_2951933 := by exact prefixLift 2951933
  have htrace : WordTrace (prefixWord ++ tailWord_2951933) baseStart_2951933 baseEnd_2951933 := by
    simpa [prefixWord, tailWord_2951933, baseEnd_2951933] using wordTrace_append hprefix tailTrace_2951933
  have hstable : (prefixWord ++ tailWord_2951933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951933).length < 2 ^ (prefixWord ++ tailWord_2951933).sum := by decide
  have hdescent : baseEnd_2951933 < baseStart_2951933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951953 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2951953 : Nat := 118140960795 + 2951953 * 2 ^ 59
def prefixEnd_2951953 : Nat := 4983230072969 + 3 ^ 40 * 2951953 * 2
def baseEnd_2951953 : Nat := 1515770758481794204011721

theorem tailTrace_2951953 : CollatzResearch.WordTrace tailWord_2951953 prefixEnd_2951953 1515770758481794204011721 := by
  unfold tailWord_2951953
  simp only [CollatzResearch.WordTrace]
  refine ⟨107666571074585909279804513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71777714049723939519869675 107666571074585909279804513)
  ·
    refine ⟨80749928305939431959853385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107666571074585909279804513 80749928305939431959853385)
    ·
      refine ⟨60562446229454573969890039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80749928305939431959853385 60562446229454573969890039)
      ·
        refine ⟨90843669344181860954835059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60562446229454573969890039 90843669344181860954835059)
        ·
          refine ⟨136265504016272791432252589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90843669344181860954835059 136265504016272791432252589)
          ·
            refine ⟨51099564006102296787094721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136265504016272791432252589 51099564006102296787094721)
            ·
              refine ⟨38324673004576722590321041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51099564006102296787094721 38324673004576722590321041)
              ·
                refine ⟨28743504753432541942740781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38324673004576722590321041 28743504753432541942740781)
                ·
                  refine ⟨10778814282537203228527793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28743504753432541942740781 10778814282537203228527793)
                  ·
                    refine ⟨8084110711902902421395845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10778814282537203228527793 8084110711902902421395845)
                    ·
                      refine ⟨1515770758481794204011721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8084110711902902421395845 1515770758481794204011721)
                      ·
                        rfl

theorem cell23_2951953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2951953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951953 prefixEnd_2951953 := by exact prefixLift 2951953
  have htrace : WordTrace (prefixWord ++ tailWord_2951953) baseStart_2951953 baseEnd_2951953 := by
    simpa [prefixWord, tailWord_2951953, baseEnd_2951953] using wordTrace_append hprefix tailTrace_2951953
  have hstable : (prefixWord ++ tailWord_2951953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951953).length < 2 ^ (prefixWord ++ tailWord_2951953).sum := by decide
  have hdescent : baseEnd_2951953 < baseStart_2951953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951970 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2951970 : Nat := 118140960795 + 2951970 * 2 ^ 59
def prefixEnd_2951970 : Nat := 4983230072969 + 3 ^ 40 * 2951970 * 2
def baseEnd_2951970 : Nat := 1515779487652920637499143

theorem tailTrace_2951970 : CollatzResearch.WordTrace tailWord_2951970 prefixEnd_2951970 1515779487652920637499143 := by
  unfold tailWord_2951970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26916797778881080295793341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71778127410349547455448909 26916797778881080295793341)
  ·
    refine ⟨10093799167080405110922503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26916797778881080295793341 10093799167080405110922503)
    ·
      refine ⟨15140698750620607666383755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10093799167080405110922503 15140698750620607666383755)
      ·
        refine ⟨22711048125930911499575633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15140698750620607666383755 22711048125930911499575633)
        ·
          refine ⟨17033286094448183624681725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22711048125930911499575633 17033286094448183624681725)
          ·
            refine ⟨6387482285418068859255647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17033286094448183624681725 6387482285418068859255647)
            ·
              refine ⟨9581223428127103288883471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6387482285418068859255647 9581223428127103288883471)
              ·
                refine ⟨14371835142190654933325207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9581223428127103288883471 14371835142190654933325207)
                ·
                  refine ⟨21557752713285982399987811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14371835142190654933325207 21557752713285982399987811)
                  ·
                    refine ⟨32336629069928973599981717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21557752713285982399987811 32336629069928973599981717)
                    ·
                      refine ⟨1515779487652920637499143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32336629069928973599981717 1515779487652920637499143)
                      ·
                        rfl

theorem cell23_2951970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2951970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951970 prefixEnd_2951970 := by exact prefixLift 2951970
  have htrace : WordTrace (prefixWord ++ tailWord_2951970) baseStart_2951970 baseEnd_2951970 := by
    simpa [prefixWord, tailWord_2951970, baseEnd_2951970] using wordTrace_append hprefix tailTrace_2951970
  have hstable : (prefixWord ++ tailWord_2951970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951970).length < 2 ^ (prefixWord ++ tailWord_2951970).sum := by decide
  have hdescent : baseEnd_2951970 < baseStart_2951970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951997 : List Nat := [1, 4, 1, 4, 3, 1, 9]
def baseStart_2951997 : Nat := 118140960795 + 2951997 * 2 ^ 59
def prefixEnd_2951997 : Nat := 4983230072969 + 3 ^ 40 * 2951997 * 2
def baseEnd_2951997 : Nat := 18713498168278913973599

theorem tailTrace_2951997 : CollatzResearch.WordTrace tailWord_2951997 prefixEnd_2951997 18713498168278913973599 := by
  unfold tailWord_2951997
  simp only [CollatzResearch.WordTrace]
  refine ⟨107668175886426504794406245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71778783924284336529604163 107668175886426504794406245)
  ·
    refine ⟨20187782978704969648951171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107668175886426504794406245 20187782978704969648951171)
    ·
      refine ⟨30281674468057454473426757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20187782978704969648951171 30281674468057454473426757)
      ·
        refine ⟨5677813962760772713767517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30281674468057454473426757 5677813962760772713767517)
        ·
          refine ⟨2129180236035289767662819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5677813962760772713767517 2129180236035289767662819)
          ·
            refine ⟨3193770354052934651494229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129180236035289767662819 3193770354052934651494229)
            ·
              refine ⟨18713498168278913973599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3193770354052934651494229 18713498168278913973599)
              ·
                rfl

theorem cell23_2951997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 9].length) (baseStart_2951997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951997 prefixEnd_2951997 := by exact prefixLift 2951997
  have htrace : WordTrace (prefixWord ++ tailWord_2951997) baseStart_2951997 baseEnd_2951997 := by
    simpa [prefixWord, tailWord_2951997, baseEnd_2951997] using wordTrace_append hprefix tailTrace_2951997
  have hstable : (prefixWord ++ tailWord_2951997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951997).length < 2 ^ (prefixWord ++ tailWord_2951997).sum := by decide
  have hdescent : baseEnd_2951997 < baseStart_2951997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952003 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_2952003 : Nat := 118140960795 + 2952003 * 2 ^ 59
def prefixEnd_2952003 : Nat := 4983230072969 + 3 ^ 40 * 2952003 * 2
def baseEnd_2952003 : Nat := 1515796432514519008386491

theorem tailTrace_2952003 : CollatzResearch.WordTrace tailWord_2952003 prefixEnd_2952003 1515796432514519008386491 := by
  unfold tailWord_2952003
  simp only [CollatzResearch.WordTrace]
  refine ⟨107668394724404767819124663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71778929816269845212749775 107668394724404767819124663)
  ·
    refine ⟨161502592086607151728686995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107668394724404767819124663 161502592086607151728686995)
    ·
      refine ⟨242253888129910727593030493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161502592086607151728686995 242253888129910727593030493)
      ·
        refine ⟨90845208048716522847386435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242253888129910727593030493 90845208048716522847386435)
        ·
          refine ⟨136267812073074784271079653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90845208048716522847386435 136267812073074784271079653)
          ·
            refine ⟨25550214763701522050827435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136267812073074784271079653 25550214763701522050827435)
            ·
              refine ⟨38325322145552283076241153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25550214763701522050827435 38325322145552283076241153)
              ·
                refine ⟨28743991609164212307180865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38325322145552283076241153 28743991609164212307180865)
                ·
                  refine ⟨21557993706873159230385649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28743991609164212307180865 21557993706873159230385649)
                  ·
                    refine ⟨16168495280154869422789237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21557993706873159230385649 16168495280154869422789237)
                    ·
                      refine ⟨1515796432514519008386491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16168495280154869422789237 1515796432514519008386491)
                      ·
                        rfl

theorem cell23_2952003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_2952003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952003 prefixEnd_2952003 := by exact prefixLift 2952003
  have htrace : WordTrace (prefixWord ++ tailWord_2952003) baseStart_2952003 baseEnd_2952003 := by
    simpa [prefixWord, tailWord_2952003, baseEnd_2952003] using wordTrace_append hprefix tailTrace_2952003
  have hstable : (prefixWord ++ tailWord_2952003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952003).length < 2 ^ (prefixWord ++ tailWord_2952003).sum := by decide
  have hdescent : baseEnd_2952003 < baseStart_2952003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952007 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_2952007 : Nat := 118140960795 + 2952007 * 2 ^ 59
def prefixEnd_2952007 : Nat := 4983230072969 + 3 ^ 40 * 2952007 * 2
def baseEnd_2952007 : Nat := 1515798486437136992736473

theorem tailTrace_2952007 : CollatzResearch.WordTrace tailWord_2952007 prefixEnd_2952007 1515798486437136992736473 := by
  unfold tailWord_2952007
  simp only [CollatzResearch.WordTrace]
  refine ⟨107668540616390276502270275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71779027077593517668180183 107668540616390276502270275)
  ·
    refine ⟨161502810924585414753405413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107668540616390276502270275 161502810924585414753405413)
    ·
      refine ⟨30281777048359765266263515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161502810924585414753405413 30281777048359765266263515)
      ·
        refine ⟨45422665572539647899395273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30281777048359765266263515 45422665572539647899395273)
        ·
          refine ⟨34066999179404735924546455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45422665572539647899395273 34066999179404735924546455)
          ·
            refine ⟨51100498769107103886819683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34066999179404735924546455 51100498769107103886819683)
            ·
              refine ⟨76650748153660655830229525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51100498769107103886819683 76650748153660655830229525)
              ·
                refine ⟨3593003819702843242042009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76650748153660655830229525 3593003819702843242042009)
                ·
                  refine ⟨2694752864777132431531507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593003819702843242042009 2694752864777132431531507)
                  ·
                    refine ⟨4042129297165698647297261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694752864777132431531507 4042129297165698647297261)
                    ·
                      refine ⟨1515798486437136992736473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4042129297165698647297261 1515798486437136992736473)
                      ·
                        rfl

theorem cell23_2952007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_2952007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952007 prefixEnd_2952007 := by exact prefixLift 2952007
  have htrace : WordTrace (prefixWord ++ tailWord_2952007) baseStart_2952007 baseEnd_2952007 := by
    simpa [prefixWord, tailWord_2952007, baseEnd_2952007] using wordTrace_append hprefix tailTrace_2952007
  have hstable : (prefixWord ++ tailWord_2952007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952007).length < 2 ^ (prefixWord ++ tailWord_2952007).sum := by decide
  have hdescent : baseEnd_2952007 < baseStart_2952007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952047 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 6, 2, 2]
def baseStart_2952047 : Nat := 118140960795 + 2952047 * 2 ^ 59
def prefixEnd_2952047 : Nat := 4983230072969 + 3 ^ 40 * 2952047 * 2
def baseEnd_2952047 : Nat := 1515819025663316836236289

theorem tailTrace_2952047 : CollatzResearch.WordTrace tailWord_2952047 prefixEnd_2952047 1515819025663316836236289 := by
  unfold tailWord_2952047
  simp only [CollatzResearch.WordTrace]
  refine ⟨107669999536245363333726395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71779999690830242222484263 107669999536245363333726395)
  ·
    refine ⟨161504999304368045000589593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107669999536245363333726395 161504999304368045000589593)
    ·
      refine ⟨121128749478276033750442195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161504999304368045000589593 121128749478276033750442195)
      ·
        refine ⟨181693124217414050625663293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121128749478276033750442195 181693124217414050625663293)
        ·
          refine ⟨68134921581530268984623735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181693124217414050625663293 68134921581530268984623735)
          ·
            refine ⟨102202382372295403476935603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68134921581530268984623735 102202382372295403476935603)
            ·
              refine ⟨153303573558443105215403405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102202382372295403476935603 153303573558443105215403405)
              ·
                refine ⟨57488840084416164455776277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153303573558443105215403405 57488840084416164455776277)
                ·
                  refine ⟨2694789378957007708864513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57488840084416164455776277 2694789378957007708864513)
                  ·
                    refine ⟨2021092034217755781648385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2694789378957007708864513 2021092034217755781648385)
                    ·
                      refine ⟨1515819025663316836236289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021092034217755781648385 1515819025663316836236289)
                      ·
                        rfl

theorem cell23_2952047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2, 2].length) (baseStart_2952047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952047 prefixEnd_2952047 := by exact prefixLift 2952047
  have htrace : WordTrace (prefixWord ++ tailWord_2952047) baseStart_2952047 baseEnd_2952047 := by
    simpa [prefixWord, tailWord_2952047, baseEnd_2952047] using wordTrace_append hprefix tailTrace_2952047
  have hstable : (prefixWord ++ tailWord_2952047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952047).length < 2 ^ (prefixWord ++ tailWord_2952047).sum := by decide
  have hdescent : baseEnd_2952047 < baseStart_2952047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952050 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2952050 : Nat := 118140960795 + 2952050 * 2 ^ 59
def prefixEnd_2952050 : Nat := 4983230072969 + 3 ^ 40 * 2952050 * 2
def baseEnd_2952050 : Nat := 1515820566105280324498775

theorem tailTrace_2952050 : CollatzResearch.WordTrace tailWord_2952050 prefixEnd_2952050 1515820566105280324498775 := by
  unfold tailWord_2952050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26917527238808623711521401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71780072636822996564057069 26917527238808623711521401)
  ·
    refine ⟨20188145429106467783641051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26917527238808623711521401 20188145429106467783641051)
    ·
      refine ⟨30282218143659701675461577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20188145429106467783641051 30282218143659701675461577)
      ·
        refine ⟨22711663607744776256596183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30282218143659701675461577 22711663607744776256596183)
        ·
          refine ⟨34067495411617164384894275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22711663607744776256596183 34067495411617164384894275)
          ·
            refine ⟨51101243117425746577341413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34067495411617164384894275 51101243117425746577341413)
            ·
              refine ⟨9581483084517327483251515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51101243117425746577341413 9581483084517327483251515)
              ·
                refine ⟨14372224626775991224877273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9581483084517327483251515 14372224626775991224877273)
                ·
                  refine ⟨10779168470081993418657955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14372224626775991224877273 10779168470081993418657955)
                  ·
                    refine ⟨16168752705122990127986933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10779168470081993418657955 16168752705122990127986933)
                    ·
                      refine ⟨1515820566105280324498775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16168752705122990127986933 1515820566105280324498775)
                      ·
                        rfl

theorem cell23_2952050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2952050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952050 prefixEnd_2952050 := by exact prefixLift 2952050
  have htrace : WordTrace (prefixWord ++ tailWord_2952050) baseStart_2952050 baseEnd_2952050 := by
    simpa [prefixWord, tailWord_2952050, baseEnd_2952050] using wordTrace_append hprefix tailTrace_2952050
  have hstable : (prefixWord ++ tailWord_2952050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952050).length < 2 ^ (prefixWord ++ tailWord_2952050).sum := by decide
  have hdescent : baseEnd_2952050 < baseStart_2952050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952063 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_2952063 : Nat := 118140960795 + 2952063 * 2 ^ 59
def prefixEnd_2952063 : Nat := 4983230072969 + 3 ^ 40 * 2952063 * 2
def baseEnd_2952063 : Nat := 1515827241353788773636215

theorem tailTrace_2952063 : CollatzResearch.WordTrace tailWord_2952063 prefixEnd_2952063 1515827241353788773636215 := by
  unfold tailWord_2952063
  simp only [CollatzResearch.WordTrace]
  refine ⟨107670583104187398066308843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71780388736124932044205895 107670583104187398066308843)
  ·
    refine ⟨161505874656281097099463265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107670583104187398066308843 161505874656281097099463265)
    ·
      refine ⟨121129405992210822824597449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161505874656281097099463265 121129405992210822824597449)
      ·
        refine ⟨90847054494158117118448087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121129405992210822824597449 90847054494158117118448087)
        ·
          refine ⟨136270581741237175677672131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90847054494158117118448087 136270581741237175677672131)
          ·
            refine ⟨204405872611855763516508197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136270581741237175677672131 204405872611855763516508197)
            ·
              refine ⟨38326101114722955659345287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204405872611855763516508197 38326101114722955659345287)
              ·
                refine ⟨57489151672084433489017931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38326101114722955659345287 57489151672084433489017931)
                ·
                  refine ⟨86233727508126650233526897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57489151672084433489017931 86233727508126650233526897)
                  ·
                    refine ⟨64675295631094987675145173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86233727508126650233526897 64675295631094987675145173)
                    ·
                      refine ⟨1515827241353788773636215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64675295631094987675145173 1515827241353788773636215)
                      ·
                        rfl

theorem cell23_2952063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_2952063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952063 prefixEnd_2952063 := by exact prefixLift 2952063
  have htrace : WordTrace (prefixWord ++ tailWord_2952063) baseStart_2952063 baseEnd_2952063 := by
    simpa [prefixWord, tailWord_2952063, baseEnd_2952063] using wordTrace_append hprefix tailTrace_2952063
  have hstable : (prefixWord ++ tailWord_2952063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952063).length < 2 ^ (prefixWord ++ tailWord_2952063).sum := by decide
  have hdescent : baseEnd_2952063 < baseStart_2952063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952100 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2952100 : Nat := 118140960795 + 2952100 * 2 ^ 59
def prefixEnd_2952100 : Nat := 4983230072969 + 3 ^ 40 * 2952100 * 2
def baseEnd_2952100 : Nat := 505282080046001709624515

theorem tailTrace_2952100 : CollatzResearch.WordTrace tailWord_2952100 prefixEnd_2952100 505282080046001709624515 := by
  unfold tailWord_2952100
  simp only [CollatzResearch.WordTrace]
  refine ⟨53835966302526676692702877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71781288403368902256937169 53835966302526676692702877)
  ·
    refine ⟨20188487363447503759763579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53835966302526676692702877 20188487363447503759763579)
    ·
      refine ⟨30282731045171255639645369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20188487363447503759763579 30282731045171255639645369)
      ·
        refine ⟨22712048283878441729734027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30282731045171255639645369 22712048283878441729734027)
        ·
          refine ⟨34068072425817662594601041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22712048283878441729734027 34068072425817662594601041)
          ·
            refine ⟨25551054319363246945950781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34068072425817662594601041 25551054319363246945950781)
            ·
              refine ⟨9581645369761217604731543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25551054319363246945950781 9581645369761217604731543)
              ·
                refine ⟨14372468054641826407097315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9581645369761217604731543 14372468054641826407097315)
                ·
                  refine ⟨21558702081962739610645973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14372468054641826407097315 21558702081962739610645973)
                  ·
                    refine ⟨505282080046001709624515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21558702081962739610645973 505282080046001709624515)
                    ·
                      rfl

theorem cell23_2952100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2952100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952100 prefixEnd_2952100 := by exact prefixLift 2952100
  have htrace : WordTrace (prefixWord ++ tailWord_2952100) baseStart_2952100 baseEnd_2952100 := by
    simpa [prefixWord, tailWord_2952100, baseEnd_2952100] using wordTrace_append hprefix tailTrace_2952100
  have hstable : (prefixWord ++ tailWord_2952100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952100).length < 2 ^ (prefixWord ++ tailWord_2952100).sum := by decide
  have hdescent : baseEnd_2952100 < baseStart_2952100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952164 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_2952164 : Nat := 118140960795 + 2952164 * 2 ^ 59
def prefixEnd_2952164 : Nat := 4983230072969 + 3 ^ 40 * 2952164 * 2
def baseEnd_2952164 : Nat := 505293034299964292824417

theorem tailTrace_2952164 : CollatzResearch.WordTrace tailWord_2952164 prefixEnd_2952164 505293034299964292824417 := by
  unfold tailWord_2952164
  simp only [CollatzResearch.WordTrace]
  refine ⟨53837133438410746157867773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71782844584547661543823697 53837133438410746157867773)
  ·
    refine ⟨20188925039404029809200415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53837133438410746157867773 20188925039404029809200415)
    ·
      refine ⟨30283387559106044713800623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20188925039404029809200415 30283387559106044713800623)
      ·
        refine ⟨45425081338659067070700935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30283387559106044713800623 45425081338659067070700935)
        ·
          refine ⟨68137622007988600606051403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45425081338659067070700935 68137622007988600606051403)
          ·
            refine ⟨102206433011982900909077105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68137622007988600606051403 102206433011982900909077105)
            ·
              refine ⟨76654824758987175681807829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102206433011982900909077105 76654824758987175681807829)
              ·
                refine ⟨1796597455288761930042371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76654824758987175681807829 1796597455288761930042371)
                ·
                  refine ⟨2694896182933142895063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796597455288761930042371 2694896182933142895063557)
                  ·
                    refine ⟨505293034299964292824417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694896182933142895063557 505293034299964292824417)
                    ·
                      rfl

theorem cell23_2952164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_2952164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952164 prefixEnd_2952164 := by exact prefixLift 2952164
  have htrace : WordTrace (prefixWord ++ tailWord_2952164) baseStart_2952164 baseEnd_2952164 := by
    simpa [prefixWord, tailWord_2952164, baseEnd_2952164] using wordTrace_append hprefix tailTrace_2952164
  have hstable : (prefixWord ++ tailWord_2952164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952164).length < 2 ^ (prefixWord ++ tailWord_2952164).sum := by decide
  have hdescent : baseEnd_2952164 < baseStart_2952164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952238 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_2952238 : Nat := 118140960795 + 2952238 * 2 ^ 59
def prefixEnd_2952238 : Nat := 4983230072969 + 3 ^ 40 * 2952238 * 2
def baseEnd_2952238 : Nat := 1515917100468325588947911

theorem tailTrace_2952238 : CollatzResearch.WordTrace tailWord_2952238 prefixEnd_2952238 1515917100468325588947911 := by
  unfold tailWord_2952238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459620734819175369241171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71784643919035601969286245 13459620734819175369241171)
  ·
    refine ⟨20189431102228763053861757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13459620734819175369241171 20189431102228763053861757)
    ·
      refine ⟨7571036663335786145198159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20189431102228763053861757 7571036663335786145198159)
      ·
        refine ⟨11356554995003679217797239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571036663335786145198159 11356554995003679217797239)
        ·
          refine ⟨17034832492505518826695859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11356554995003679217797239 17034832492505518826695859)
          ·
            refine ⟨25552248738758278240043789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17034832492505518826695859 25552248738758278240043789)
            ·
              refine ⟨9582093277034354340016421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25552248738758278240043789 9582093277034354340016421)
              ·
                refine ⟨1796642489443941438753079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9582093277034354340016421 1796642489443941438753079)
                ·
                  refine ⟨2694963734165912158129619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796642489443941438753079 2694963734165912158129619)
                  ·
                    refine ⟨4042445601248868237194429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694963734165912158129619 4042445601248868237194429)
                    ·
                      refine ⟨1515917100468325588947911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4042445601248868237194429 1515917100468325588947911)
                      ·
                        rfl

theorem cell23_2952238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_2952238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952238 prefixEnd_2952238 := by exact prefixLift 2952238
  have htrace : WordTrace (prefixWord ++ tailWord_2952238) baseStart_2952238 baseEnd_2952238 := by
    simpa [prefixWord, tailWord_2952238, baseEnd_2952238] using wordTrace_append hprefix tailTrace_2952238
  have hstable : (prefixWord ++ tailWord_2952238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952238).length < 2 ^ (prefixWord ++ tailWord_2952238).sum := by decide
  have hdescent : baseEnd_2952238 < baseStart_2952238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952254 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2952254 : Nat := 118140960795 + 2952254 * 2 ^ 59
def prefixEnd_2952254 : Nat := 4983230072969 + 3 ^ 40 * 2952254 * 2
def baseEnd_2952254 : Nat := 505308438719599175449279

theorem tailTrace_2952254 : CollatzResearch.WordTrace tailWord_2952254 prefixEnd_2952254 505308438719599175449279 := by
  unfold tailWord_2952254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459693680811929710813977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71785032964330291791007877 13459693680811929710813977)
  ·
    refine ⟨10094770260608947283110483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13459693680811929710813977 10094770260608947283110483)
    ·
      refine ⟨15142155390913420924665725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10094770260608947283110483 15142155390913420924665725)
      ·
        refine ⟨5678308271592532846749647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15142155390913420924665725 5678308271592532846749647)
        ·
          refine ⟨8517462407388799270124471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678308271592532846749647 8517462407388799270124471)
          ·
            refine ⟨12776193611083198905186707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517462407388799270124471 12776193611083198905186707)
            ·
              refine ⟨19164290416624798357780061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12776193611083198905186707 19164290416624798357780061)
              ·
                refine ⟨7186608906234299384167523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19164290416624798357780061 7186608906234299384167523)
                ·
                  refine ⟨10779913359351449076251285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186608906234299384167523 10779913359351449076251285)
                  ·
                    refine ⟨505308438719599175449279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10779913359351449076251285 505308438719599175449279)
                    ·
                      rfl

theorem cell23_2952254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2952254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952254 prefixEnd_2952254 := by exact prefixLift 2952254
  have htrace : WordTrace (prefixWord ++ tailWord_2952254) baseStart_2952254 baseEnd_2952254 := by
    simpa [prefixWord, tailWord_2952254, baseEnd_2952254] using wordTrace_append hprefix tailTrace_2952254
  have hstable : (prefixWord ++ tailWord_2952254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952254).length < 2 ^ (prefixWord ++ tailWord_2952254).sum := by decide
  have hdescent : baseEnd_2952254 < baseStart_2952254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952264 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_2952264 : Nat := 118140960795 + 2952264 * 2 ^ 59
def prefixEnd_2952264 : Nat := 4983230072969 + 3 ^ 40 * 2952264 * 2
def baseEnd_2952264 : Nat := 1515930450965342487222791

theorem tailTrace_2952264 : CollatzResearch.WordTrace tailWord_2952264 prefixEnd_2952264 1515930450965342487222791 := by
  unfold tailWord_2952264
  simp only [CollatzResearch.WordTrace]
  refine ⟨53838957088229604697187923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71785276117639472929583897 53838957088229604697187923)
  ·
    refine ⟨80758435632344407045781885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53838957088229604697187923 80758435632344407045781885)
    ·
      refine ⟨30284413362129152642168207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80758435632344407045781885 30284413362129152642168207)
      ·
        refine ⟨45426620043193728963252311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30284413362129152642168207 45426620043193728963252311)
        ·
          refine ⟨68139930064790593444878467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45426620043193728963252311 68139930064790593444878467)
          ·
            refine ⟨102209895097185890167317701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68139930064790593444878467 102209895097185890167317701)
            ·
              refine ⟨19164355330722354406372069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102209895097185890167317701 19164355330722354406372069)
              ·
                refine ⟨3593316624510441451194763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19164355330722354406372069 3593316624510441451194763)
                ·
                  refine ⟨5389974936765662176792145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593316624510441451194763 5389974936765662176792145)
                  ·
                    refine ⟨4042481202574246632594109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5389974936765662176792145 4042481202574246632594109)
                    ·
                      refine ⟨1515930450965342487222791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4042481202574246632594109 1515930450965342487222791)
                      ·
                        rfl

theorem cell23_2952264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_2952264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952264 prefixEnd_2952264 := by exact prefixLift 2952264
  have htrace : WordTrace (prefixWord ++ tailWord_2952264) baseStart_2952264 baseEnd_2952264 := by
    simpa [prefixWord, tailWord_2952264, baseEnd_2952264] using wordTrace_append hprefix tailTrace_2952264
  have hstable : (prefixWord ++ tailWord_2952264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952264).length < 2 ^ (prefixWord ++ tailWord_2952264).sum := by decide
  have hdescent : baseEnd_2952264 < baseStart_2952264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952274 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2952274 : Nat := 118140960795 + 2952274 * 2 ^ 59
def prefixEnd_2952274 : Nat := 4983230072969 + 3 ^ 40 * 2952274 * 2
def baseEnd_2952274 : Nat := 1515935585771887448097745

theorem tailTrace_2952274 : CollatzResearch.WordTrace tailWord_2952274 prefixEnd_2952274 1515935585771887448097745 := by
  unfold tailWord_2952274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919569726605745275559969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71785519270948654068159917 26919569726605745275559969)
  ·
    refine ⟨20189677294954308956669977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26919569726605745275559969 20189677294954308956669977)
    ·
      refine ⟨15142257971215731717502483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20189677294954308956669977 15142257971215731717502483)
      ·
        refine ⟨22713386956823597576253725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15142257971215731717502483 22713386956823597576253725)
        ·
          refine ⟨8517520108808849091095147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22713386956823597576253725 8517520108808849091095147)
          ·
            refine ⟨12776280163213273636642721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517520108808849091095147 12776280163213273636642721)
            ·
              refine ⟨9582210122409955227482041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12776280163213273636642721 9582210122409955227482041)
              ·
                refine ⟨7186657591807466420611531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9582210122409955227482041 7186657591807466420611531)
                ·
                  refine ⟨10779986387711199630917297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186657591807466420611531 10779986387711199630917297)
                  ·
                    refine ⟨8084989790783399723187973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10779986387711199630917297 8084989790783399723187973)
                    ·
                      refine ⟨1515935585771887448097745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8084989790783399723187973 1515935585771887448097745)
                      ·
                        rfl

theorem cell23_2952274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2952274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952274 prefixEnd_2952274 := by exact prefixLift 2952274
  have htrace : WordTrace (prefixWord ++ tailWord_2952274) baseStart_2952274 baseEnd_2952274 := by
    simpa [prefixWord, tailWord_2952274, baseEnd_2952274] using wordTrace_append hprefix tailTrace_2952274
  have hstable : (prefixWord ++ tailWord_2952274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952274).length < 2 ^ (prefixWord ++ tailWord_2952274).sum := by decide
  have hdescent : baseEnd_2952274 < baseStart_2952274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952318 : List Nat := [4, 2, 4, 1, 1, 1, 1, 9]
def baseStart_2952318 : Nat := 118140960795 + 2952318 * 2 ^ 59
def prefixEnd_2952318 : Nat := 4983230072969 + 3 ^ 40 * 2952318 * 2
def baseEnd_2952318 : Nat := 56146599219284639849909

theorem tailTrace_2952318 : CollatzResearch.WordTrace tailWord_2952318 prefixEnd_2952318 56146599219284639849909 := by
  unfold tailWord_2952318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459985464782947077105201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71786589145509051077894405 13459985464782947077105201)
  ·
    refine ⟨10094989098587210307828901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13459985464782947077105201 10094989098587210307828901)
    ·
      refine ⟨1892810455985101932717919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10094989098587210307828901 1892810455985101932717919)
      ·
        refine ⟨2839215683977652899076879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892810455985101932717919 2839215683977652899076879)
        ·
          refine ⟨4258823525966479348615319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839215683977652899076879 4258823525966479348615319)
          ·
            refine ⟨6388235288949719022922979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258823525966479348615319 6388235288949719022922979)
            ·
              refine ⟨9582352933424578534384469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388235288949719022922979 9582352933424578534384469)
              ·
                refine ⟨56146599219284639849909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9582352933424578534384469 56146599219284639849909)
                ·
                  rfl

theorem cell23_2952318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_2952318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952318 prefixEnd_2952318 := by exact prefixLift 2952318
  have htrace : WordTrace (prefixWord ++ tailWord_2952318) baseStart_2952318 baseEnd_2952318 := by
    simpa [prefixWord, tailWord_2952318, baseEnd_2952318] using wordTrace_append hprefix tailTrace_2952318
  have hstable : (prefixWord ++ tailWord_2952318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952318).length < 2 ^ (prefixWord ++ tailWord_2952318).sum := by decide
  have hdescent : baseEnd_2952318 < baseStart_2952318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952338 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2952338 : Nat := 118140960795 + 2952338 * 2 ^ 59
def prefixEnd_2952338 : Nat := 4983230072969 + 3 ^ 40 * 2952338 * 2
def baseEnd_2952338 : Nat := 1515968448533775197697451

theorem tailTrace_2952338 : CollatzResearch.WordTrace tailWord_2952338 prefixEnd_2952338 1515968448533775197697451 := by
  unfold tailWord_2952338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26920153294547780008142417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71787075452127413355046445 26920153294547780008142417)
  ·
    refine ⟨20190114970910835006106813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26920153294547780008142417 20190114970910835006106813)
    ·
      refine ⟨7571293114091563127290055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20190114970910835006106813 7571293114091563127290055)
      ·
        refine ⟨11356939671137344690935083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571293114091563127290055 11356939671137344690935083)
        ·
          refine ⟨17035409506706017036402625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11356939671137344690935083 17035409506706017036402625)
          ·
            refine ⟨12776557130029512777301969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17035409506706017036402625 12776557130029512777301969)
            ·
              refine ⟨9582417847522134582976477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12776557130029512777301969 9582417847522134582976477)
              ·
                refine ⟨3593406692820800468616179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9582417847522134582976477 3593406692820800468616179)
                ·
                  refine ⟨5390110039231200702924269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593406692820800468616179 5390110039231200702924269)
                  ·
                    refine ⟨2021291264711700263596601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5390110039231200702924269 2021291264711700263596601)
                    ·
                      refine ⟨1515968448533775197697451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021291264711700263596601 1515968448533775197697451)
                      ·
                        rfl

theorem cell23_2952338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2952338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952338 prefixEnd_2952338 := by exact prefixLift 2952338
  have htrace : WordTrace (prefixWord ++ tailWord_2952338) baseStart_2952338 baseEnd_2952338 := by
    simpa [prefixWord, tailWord_2952338, baseEnd_2952338] using wordTrace_append hprefix tailTrace_2952338
  have hstable : (prefixWord ++ tailWord_2952338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952338).length < 2 ^ (prefixWord ++ tailWord_2952338).sum := by decide
  have hdescent : baseEnd_2952338 < baseStart_2952338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952362 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2952362 : Nat := 118140960795 + 2952362 * 2 ^ 59
def prefixEnd_2952362 : Nat := 4983230072969 + 3 ^ 40 * 2952362 * 2
def baseEnd_2952362 : Nat := 1515980772069483103797341

theorem tailTrace_2952362 : CollatzResearch.WordTrace tailWord_2952362 prefixEnd_2952362 1515980772069483103797341 := by
  unfold tailWord_2952362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26920372132526043032860835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71787659020069448087628893 26920372132526043032860835)
  ·
    refine ⟨40380558198789064549291253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26920372132526043032860835 40380558198789064549291253)
    ·
      refine ⟨3785677331136474801496055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40380558198789064549291253 3785677331136474801496055)
      ·
        refine ⟨5678515996704712202244083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785677331136474801496055 5678515996704712202244083)
        ·
          refine ⟨8517773995057068303366125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678515996704712202244083 8517773995057068303366125)
          ·
            refine ⟨3194165248146400613762297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8517773995057068303366125 3194165248146400613762297)
            ·
              refine ⟨2395623936109800460321723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194165248146400613762297 2395623936109800460321723)
              ·
                refine ⟨3593435904164700690482585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395623936109800460321723 3593435904164700690482585)
                ·
                  refine ⟨2695076928123525517861939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593435904164700690482585 2695076928123525517861939)
                  ·
                    refine ⟨4042615392185288276792909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695076928123525517861939 4042615392185288276792909)
                    ·
                      refine ⟨1515980772069483103797341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4042615392185288276792909 1515980772069483103797341)
                      ·
                        rfl

theorem cell23_2952362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2952362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952362 prefixEnd_2952362 := by exact prefixLift 2952362
  have htrace : WordTrace (prefixWord ++ tailWord_2952362) baseStart_2952362 baseEnd_2952362 := by
    simpa [prefixWord, tailWord_2952362, baseEnd_2952362] using wordTrace_append hprefix tailTrace_2952362
  have hstable : (prefixWord ++ tailWord_2952362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952362).length < 2 ^ (prefixWord ++ tailWord_2952362).sum := by decide
  have hdescent : baseEnd_2952362 < baseStart_2952362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952424 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2952424 : Nat := 118140960795 + 2952424 * 2 ^ 59
def prefixEnd_2952424 : Nat := 4983230072969 + 3 ^ 40 * 2952424 * 2
def baseEnd_2952424 : Nat := 1516012607870061861222055

theorem tailTrace_2952424 : CollatzResearch.WordTrace tailWord_2952424 prefixEnd_2952424 1516012607870061861222055 := by
  unfold tailWord_2952424
  simp only [CollatzResearch.WordTrace]
  refine ⟨53841874927939778360100163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71789166570586371146800217 53841874927939778360100163)
  ·
    refine ⟨80762812391909667540150245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53841874927939778360100163 80762812391909667540150245)
    ·
      refine ⟨15143027323483062663778171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80762812391909667540150245 15143027323483062663778171)
      ·
        refine ⟨22714540985224593995667257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15143027323483062663778171 22714540985224593995667257)
        ·
          refine ⟨17035905738918445496750443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22714540985224593995667257 17035905738918445496750443)
          ·
            refine ⟨25553858608377668245125665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17035905738918445496750443 25553858608377668245125665)
            ·
              refine ⟨19165393956283251183844249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25553858608377668245125665 19165393956283251183844249)
              ·
                refine ⟨14374045467212438387883187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19165393956283251183844249 14374045467212438387883187)
                ·
                  refine ⟨21561068200818657581824781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14374045467212438387883187 21561068200818657581824781)
                  ·
                    refine ⟨8085400575306996593184293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21561068200818657581824781 8085400575306996593184293)
                    ·
                      refine ⟨1516012607870061861222055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8085400575306996593184293 1516012607870061861222055)
                      ·
                        rfl

theorem cell23_2952424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2952424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952424 prefixEnd_2952424 := by exact prefixLift 2952424
  have htrace : WordTrace (prefixWord ++ tailWord_2952424) baseStart_2952424 baseEnd_2952424 := by
    simpa [prefixWord, tailWord_2952424, baseEnd_2952424] using wordTrace_append hprefix tailTrace_2952424
  have hstable : (prefixWord ++ tailWord_2952424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952424).length < 2 ^ (prefixWord ++ tailWord_2952424).sum := by decide
  have hdescent : baseEnd_2952424 < baseStart_2952424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952484 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2952484 : Nat := 118140960795 + 2952484 * 2 ^ 59
def prefixEnd_2952484 : Nat := 4983230072969 + 3 ^ 40 * 2952484 * 2
def baseEnd_2952484 : Nat := 1516043416709331626471779

theorem tailTrace_2952484 : CollatzResearch.WordTrace tailWord_2952484 prefixEnd_2952484 1516043416709331626471779 := by
  unfold tailWord_2952484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53842969117831093483692253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71790625490441457978256337 53842969117831093483692253)
  ·
    refine ⟨20191113419186660056384595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53842969117831093483692253 20191113419186660056384595)
    ·
      refine ⟨30286670128779990084576893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20191113419186660056384595 30286670128779990084576893)
      ·
        refine ⟨11357501298292496281716335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30286670128779990084576893 11357501298292496281716335)
        ·
          refine ⟨17036251947438744422574503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11357501298292496281716335 17036251947438744422574503)
          ·
            refine ⟨25554377921158116633861755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17036251947438744422574503 25554377921158116633861755)
            ·
              refine ⟨38331566881737174950792633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25554377921158116633861755 38331566881737174950792633)
              ·
                refine ⟨28748675161302881213094475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38331566881737174950792633 28748675161302881213094475)
                ·
                  refine ⟨43123012741954321819641713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28748675161302881213094475 43123012741954321819641713)
                  ·
                    refine ⟨32342259556465741364731285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43123012741954321819641713 32342259556465741364731285)
                    ·
                      refine ⟨1516043416709331626471779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32342259556465741364731285 1516043416709331626471779)
                      ·
                        rfl

theorem cell23_2952484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2952484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952484 prefixEnd_2952484 := by exact prefixLift 2952484
  have htrace : WordTrace (prefixWord ++ tailWord_2952484) baseStart_2952484 baseEnd_2952484 := by
    simpa [prefixWord, tailWord_2952484, baseEnd_2952484] using wordTrace_append hprefix tailTrace_2952484
  have hstable : (prefixWord ++ tailWord_2952484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952484).length < 2 ^ (prefixWord ++ tailWord_2952484).sum := by decide
  have hdescent : baseEnd_2952484 < baseStart_2952484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952511 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 1, 5]
def baseStart_2952511 : Nat := 118140960795 + 2952511 * 2 ^ 59
def prefixEnd_2952511 : Nat := 4983230072969 + 3 ^ 40 * 2952511 * 2
def baseEnd_2952511 : Nat := 505352426895667673611385

theorem tailTrace_2952511 : CollatzResearch.WordTrace tailWord_2952511 prefixEnd_2952511 505352426895667673611385 := by
  unfold tailWord_2952511
  simp only [CollatzResearch.WordTrace]
  refine ⟨107686923006564370578617387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71791282004376247052411591 107686923006564370578617387)
  ·
    refine ⟨161530384509846555867926081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107686923006564370578617387 161530384509846555867926081)
    ·
      refine ⟨121147788382384916900944561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161530384509846555867926081 121147788382384916900944561)
      ·
        refine ⟨90860841286788687675708421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121147788382384916900944561 90860841286788687675708421)
        ·
          refine ⟨17036407741272878939195329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90860841286788687675708421 17036407741272878939195329)
          ·
            refine ⟨12777305805954659204396497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17036407741272878939195329 12777305805954659204396497)
            ·
              refine ⟨9582979354465994403297373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12777305805954659204396497 9582979354465994403297373)
              ·
                refine ⟨3593617257924747901236515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9582979354465994403297373 3593617257924747901236515)
                ·
                  refine ⟨5390425886887121851854773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593617257924747901236515 5390425886887121851854773)
                  ·
                    refine ⟨505352426895667673611385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5390425886887121851854773 505352426895667673611385)
                    ·
                      rfl

theorem cell23_2952511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_2952511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952511 prefixEnd_2952511 := by exact prefixLift 2952511
  have htrace : WordTrace (prefixWord ++ tailWord_2952511) baseStart_2952511 baseEnd_2952511 := by
    simpa [prefixWord, tailWord_2952511, baseEnd_2952511] using wordTrace_append hprefix tailTrace_2952511
  have hstable : (prefixWord ++ tailWord_2952511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952511).length < 2 ^ (prefixWord ++ tailWord_2952511).sum := by decide
  have hdescent : baseEnd_2952511 < baseStart_2952511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952548 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_2952548 : Nat := 118140960795 + 2952548 * 2 ^ 59
def prefixEnd_2952548 : Nat := 4983230072969 + 3 ^ 40 * 2952548 * 2
def baseEnd_2952548 : Nat := 1516076279471219376071485

theorem tailTrace_2952548 : CollatzResearch.WordTrace tailWord_2952548 prefixEnd_2952548 1516076279471219376071485 := by
  unfold tailWord_2952548
  simp only [CollatzResearch.WordTrace]
  refine ⟨53844136253715162948857149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71792181671620217265142865 53844136253715162948857149)
  ·
    refine ⟨20191551095143186105821431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53844136253715162948857149 20191551095143186105821431)
    ·
      refine ⟨30287326642714779158732147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20191551095143186105821431 30287326642714779158732147)
      ·
        refine ⟨45430989964072168738098221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30287326642714779158732147 45430989964072168738098221)
        ·
          refine ⟨17036621236527063276786833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45430989964072168738098221 17036621236527063276786833)
          ·
            refine ⟨12777465927395297457590125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17036621236527063276786833 12777465927395297457590125)
            ·
              refine ⟨4791549722773236546596297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12777465927395297457590125 4791549722773236546596297)
              ·
                refine ⟨3593662292079927409947223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791549722773236546596297 3593662292079927409947223)
                ·
                  refine ⟨5390493438119891114920835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593662292079927409947223 5390493438119891114920835)
                  ·
                    refine ⟨8085740157179836672381253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5390493438119891114920835 8085740157179836672381253)
                    ·
                      refine ⟨1516076279471219376071485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8085740157179836672381253 1516076279471219376071485)
                      ·
                        rfl

theorem cell23_2952548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_2952548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952548 prefixEnd_2952548 := by exact prefixLift 2952548
  have htrace : WordTrace (prefixWord ++ tailWord_2952548) baseStart_2952548 baseEnd_2952548 := by
    simpa [prefixWord, tailWord_2952548, baseEnd_2952548] using wordTrace_append hprefix tailTrace_2952548
  have hstable : (prefixWord ++ tailWord_2952548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952548).length < 2 ^ (prefixWord ++ tailWord_2952548).sum := by decide
  have hdescent : baseEnd_2952548 < baseStart_2952548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952608 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2]
def baseStart_2952608 : Nat := 118140960795 + 2952608 * 2 ^ 59
def prefixEnd_2952608 : Nat := 4983230072969 + 3 ^ 40 * 2952608 * 2
def baseEnd_2952608 : Nat := 1516107088310489141321209

theorem tailTrace_2952608 : CollatzResearch.WordTrace tailWord_2952608 prefixEnd_2952608 1516107088310489141321209 := by
  unfold tailWord_2952608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53845230443606478072449239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71793640591475304096598985 53845230443606478072449239)
  ·
    refine ⟨80767845665409717108673859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53845230443606478072449239 80767845665409717108673859)
    ·
      refine ⟨121151768498114575663010789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80767845665409717108673859 121151768498114575663010789)
      ·
        refine ⟨22715956593396482936814523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121151768498114575663010789 22715956593396482936814523)
        ·
          refine ⟨34073934890094724405221785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22715956593396482936814523 34073934890094724405221785)
          ·
            refine ⟨25555451167571043303916339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34073934890094724405221785 25555451167571043303916339)
            ·
              refine ⟨38333176751356564955874509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25555451167571043303916339 38333176751356564955874509)
              ·
                refine ⟨14374941281758711858452941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38333176751356564955874509 14374941281758711858452941)
                ·
                  refine ⟨5390602980659516946919853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14374941281758711858452941 5390602980659516946919853)
                  ·
                    refine ⟨2021476117747318855094945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5390602980659516946919853 2021476117747318855094945)
                    ·
                      refine ⟨1516107088310489141321209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021476117747318855094945 1516107088310489141321209)
                      ·
                        rfl

theorem cell23_2952608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_2952608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952608 prefixEnd_2952608 := by exact prefixLift 2952608
  have htrace : WordTrace (prefixWord ++ tailWord_2952608) baseStart_2952608 baseEnd_2952608 := by
    simpa [prefixWord, tailWord_2952608, baseEnd_2952608] using wordTrace_append hprefix tailTrace_2952608
  have hstable : (prefixWord ++ tailWord_2952608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952608).length < 2 ^ (prefixWord ++ tailWord_2952608).sum := by decide
  have hdescent : baseEnd_2952608 < baseStart_2952608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952616 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2952616 : Nat := 118140960795 + 2952616 * 2 ^ 59
def prefixEnd_2952616 : Nat := 4983230072969 + 3 ^ 40 * 2952616 * 2
def baseEnd_2952616 : Nat := 1516111196155725110021173

theorem tailTrace_2952616 : CollatzResearch.WordTrace tailWord_2952616 prefixEnd_2952616 1516111196155725110021173 := by
  unfold tailWord_2952616
  simp only [CollatzResearch.WordTrace]
  refine ⟨53845376335591986755594851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71793835114122649007459801 53845376335591986755594851)
  ·
    refine ⟨80768064503387980133392277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53845376335591986755594851 80768064503387980133392277)
    ·
      refine ⟨3786003023596311568752763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80768064503387980133392277 3786003023596311568752763)
      ·
        refine ⟨5679004535394467353129145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786003023596311568752763 5679004535394467353129145)
        ·
          refine ⟨4259253401545850514846859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679004535394467353129145 4259253401545850514846859)
          ·
            refine ⟨6388880102318775772270289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259253401545850514846859 6388880102318775772270289)
            ·
              refine ⟨4791660076739081829202717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6388880102318775772270289 4791660076739081829202717)
              ·
                refine ⟨1796872528777155685951019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4791660076739081829202717 1796872528777155685951019)
                ·
                  refine ⟨2695308793165733528926529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796872528777155685951019 2695308793165733528926529)
                  ·
                    refine ⟨2021481594874300146694897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2695308793165733528926529 2021481594874300146694897)
                    ·
                      refine ⟨1516111196155725110021173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021481594874300146694897 1516111196155725110021173)
                      ·
                        rfl

theorem cell23_2952616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2952616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952616 prefixEnd_2952616 := by exact prefixLift 2952616
  have htrace : WordTrace (prefixWord ++ tailWord_2952616) baseStart_2952616 baseEnd_2952616 := by
    simpa [prefixWord, tailWord_2952616, baseEnd_2952616] using wordTrace_append hprefix tailTrace_2952616
  have hstable : (prefixWord ++ tailWord_2952616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952616).length < 2 ^ (prefixWord ++ tailWord_2952616).sum := by decide
  have hdescent : baseEnd_2952616 < baseStart_2952616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952625 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_2952625 : Nat := 118140960795 + 2952625 * 2 ^ 59
def prefixEnd_2952625 : Nat := 4983230072969 + 3 ^ 40 * 2952625 * 2
def baseEnd_2952625 : Nat := 1516115817481615574808631

theorem tailTrace_2952625 : CollatzResearch.WordTrace tailWord_2952625 prefixEnd_2952625 1516115817481615574808631 := by
  unfold tailWord_2952625
  simp only [CollatzResearch.WordTrace]
  refine ⟨107691080928151368048267329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71794053952100912032178219 107691080928151368048267329)
  ·
    refine ⟨80768310696113526036200497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107691080928151368048267329 80768310696113526036200497)
    ·
      refine ⟨60576233022085144527150373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80768310696113526036200497 60576233022085144527150373)
      ·
        refine ⟨11358043691640964598840695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60576233022085144527150373 11358043691640964598840695)
        ·
          refine ⟨17037065537461446898261043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358043691640964598840695 17037065537461446898261043)
          ·
            refine ⟨25555598306192170347391565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037065537461446898261043 25555598306192170347391565)
            ·
              refine ⟨9583349364822063880271837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25555598306192170347391565 9583349364822063880271837)
              ·
                refine ⟨3593756011808273955101939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9583349364822063880271837 3593756011808273955101939)
                ·
                  refine ⟨5390634017712410932652909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593756011808273955101939 5390634017712410932652909)
                  ·
                    refine ⟨2021487756642154099744841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5390634017712410932652909 2021487756642154099744841)
                    ·
                      refine ⟨1516115817481615574808631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021487756642154099744841 1516115817481615574808631)
                      ·
                        rfl

theorem cell23_2952625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_2952625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952625 prefixEnd_2952625 := by exact prefixLift 2952625
  have htrace : WordTrace (prefixWord ++ tailWord_2952625) baseStart_2952625 baseEnd_2952625 := by
    simpa [prefixWord, tailWord_2952625, baseEnd_2952625] using wordTrace_append hprefix tailTrace_2952625
  have hstable : (prefixWord ++ tailWord_2952625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952625).length < 2 ^ (prefixWord ++ tailWord_2952625).sum := by decide
  have hdescent : baseEnd_2952625 < baseStart_2952625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952651 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_2952651 : Nat := 118140960795 + 2952651 * 2 ^ 59
def prefixEnd_2952651 : Nat := 4983230072969 + 3 ^ 40 * 2952651 * 2
def baseEnd_2952651 : Nat := 1516129167978632473083511

theorem tailTrace_2952651 : CollatzResearch.WordTrace tailWord_2952651 prefixEnd_2952651 1516129167978632473083511 := by
  unfold tailWord_2952651
  simp only [CollatzResearch.WordTrace]
  refine ⟨107692029226057174488713807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71794686150704782992475871 107692029226057174488713807)
  ·
    refine ⟨161538043839085761733070711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107692029226057174488713807 161538043839085761733070711)
    ·
      refine ⟨242307065758628642599606067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161538043839085761733070711 242307065758628642599606067)
      ·
        refine ⟨363460598637942963899409101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242307065758628642599606067 363460598637942963899409101)
        ·
          refine ⟨136297724489228611462278413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363460598637942963899409101 136297724489228611462278413)
          ·
            refine ⟨51111646683460729298354405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136297724489228611462278413 51111646683460729298354405)
            ·
              refine ⟨9583433753148886743441451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51111646683460729298354405 9583433753148886743441451)
              ·
                refine ⟨14375150629723330115162177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583433753148886743441451 14375150629723330115162177)
                ·
                  refine ⟨10781362972292497586371633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375150629723330115162177 10781362972292497586371633)
                  ·
                    refine ⟨8086022229219373189778725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781362972292497586371633 8086022229219373189778725)
                    ·
                      refine ⟨1516129167978632473083511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8086022229219373189778725 1516129167978632473083511)
                      ·
                        rfl

theorem cell23_2952651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_2952651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952651 prefixEnd_2952651 := by exact prefixLift 2952651
  have htrace : WordTrace (prefixWord ++ tailWord_2952651) baseStart_2952651 baseEnd_2952651 := by
    simpa [prefixWord, tailWord_2952651, baseEnd_2952651] using wordTrace_append hprefix tailTrace_2952651
  have hstable : (prefixWord ++ tailWord_2952651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952651).length < 2 ^ (prefixWord ++ tailWord_2952651).sum := by decide
  have hdescent : baseEnd_2952651 < baseStart_2952651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952655 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 2, 2, 2]
def baseStart_2952655 : Nat := 118140960795 + 2952655 * 2 ^ 59
def prefixEnd_2952655 : Nat := 4983230072969 + 3 ^ 40 * 2952655 * 2
def baseEnd_2952655 : Nat := 1516131221901250457433493

theorem tailTrace_2952655 : CollatzResearch.WordTrace tailWord_2952655 prefixEnd_2952655 1516131221901250457433493 := by
  unfold tailWord_2952655
  simp only [CollatzResearch.WordTrace]
  refine ⟨107692175118042683171859419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71794783412028455447906279 107692175118042683171859419)
  ·
    refine ⟨161538262677064024757789129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107692175118042683171859419 161538262677064024757789129)
    ·
      refine ⟨121153697007798018568341847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161538262677064024757789129 121153697007798018568341847)
      ·
        refine ⟨181730545511697027852512771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121153697007798018568341847 181730545511697027852512771)
        ·
          refine ⟨272595818267545541778769157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181730545511697027852512771 272595818267545541778769157)
          ·
            refine ⟨51111715925164789083519217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272595818267545541778769157 51111715925164789083519217)
            ·
              refine ⟨38333786943873591812639413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51111715925164789083519217 38333786943873591812639413)
              ·
                refine ⟨3593792525988149232434945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38333786943873591812639413 3593792525988149232434945)
                ·
                  refine ⟨2695344394491111924326209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593792525988149232434945 2695344394491111924326209)
                  ·
                    refine ⟨2021508295868333943244657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2695344394491111924326209 2021508295868333943244657)
                    ·
                      refine ⟨1516131221901250457433493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021508295868333943244657 1516131221901250457433493)
                      ·
                        rfl

theorem cell23_2952655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2, 2].length) (baseStart_2952655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952655 prefixEnd_2952655 := by exact prefixLift 2952655
  have htrace : WordTrace (prefixWord ++ tailWord_2952655) baseStart_2952655 baseEnd_2952655 := by
    simpa [prefixWord, tailWord_2952655, baseEnd_2952655] using wordTrace_append hprefix tailTrace_2952655
  have hstable : (prefixWord ++ tailWord_2952655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952655).length < 2 ^ (prefixWord ++ tailWord_2952655).sum := by decide
  have hdescent : baseEnd_2952655 < baseStart_2952655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952661 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 7]
def baseStart_2952661 : Nat := 118140960795 + 2952661 * 2 ^ 59
def prefixEnd_2952661 : Nat := 4983230072969 + 3 ^ 40 * 2952661 * 2
def baseEnd_2952661 : Nat := 168459366976130825995385

theorem tailTrace_2952661 : CollatzResearch.WordTrace tailWord_2952661 prefixEnd_2952661 168459366976130825995385 := by
  unfold tailWord_2952661
  simp only [CollatzResearch.WordTrace]
  refine ⟨107692393956020946196577837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71794929304013964131051891 107692393956020946196577837)
  ·
    refine ⟨40384647733507854823716689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107692393956020946196577837 40384647733507854823716689)
    ·
      refine ⟨30288485800130891117787517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40384647733507854823716689 30288485800130891117787517)
      ·
        refine ⟨11358182175049084169170319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30288485800130891117787517 11358182175049084169170319)
        ·
          refine ⟨17037273262573626253755479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358182175049084169170319 17037273262573626253755479)
          ·
            refine ⟨25555909893860439380633219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037273262573626253755479 25555909893860439380633219)
            ·
              refine ⟨38333864840790659070949829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25555909893860439380633219 38333864840790659070949829)
              ·
                refine ⟨7187599657648248575803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38333864840790659070949829 7187599657648248575803093)
                ·
                  refine ⟨168459366976130825995385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7187599657648248575803093 168459366976130825995385)
                  ·
                    rfl

theorem cell23_2952661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_2952661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952661 prefixEnd_2952661 := by exact prefixLift 2952661
  have htrace : WordTrace (prefixWord ++ tailWord_2952661) baseStart_2952661 baseEnd_2952661 := by
    simpa [prefixWord, tailWord_2952661, baseEnd_2952661] using wordTrace_append hprefix tailTrace_2952661
  have hstable : (prefixWord ++ tailWord_2952661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952661).length < 2 ^ (prefixWord ++ tailWord_2952661).sum := by decide
  have hdescent : baseEnd_2952661 < baseStart_2952661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952698 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_2952698 : Nat := 118140960795 + 2952698 * 2 ^ 59
def prefixEnd_2952698 : Nat := 4983230072969 + 3 ^ 40 * 2952698 * 2
def baseEnd_2952698 : Nat := 1516153301569393789195795

theorem tailTrace_2952698 : CollatzResearch.WordTrace tailWord_2952698 prefixEnd_2952698 1516153301569393789195795 := by
  unfold tailWord_2952698
  simp only [CollatzResearch.WordTrace]
  refine ⟨26923435864221725378918687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71795828971257934343783165 26923435864221725378918687)
  ·
    refine ⟨40385153796332588068378031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26923435864221725378918687 40385153796332588068378031)
    ·
      refine ⟨60577730694498882102567047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40385153796332588068378031 60577730694498882102567047)
      ·
        refine ⟨90866596041748323153850571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60577730694498882102567047 90866596041748323153850571)
        ·
          refine ⟨136299894062622484730775857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90866596041748323153850571 136299894062622484730775857)
          ·
            refine ⟨102224920546966863548081893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136299894062622484730775857 102224920546966863548081893)
            ·
              refine ⟨19167172602556286915265355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102224920546966863548081893 19167172602556286915265355)
              ·
                refine ⟨28750758903834430372898033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19167172602556286915265355 28750758903834430372898033)
                ·
                  refine ⟨21563069177875822779673525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28750758903834430372898033 21563069177875822779673525)
                  ·
                    refine ⟨2021537735425858385594393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21563069177875822779673525 2021537735425858385594393)
                    ·
                      refine ⟨1516153301569393789195795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021537735425858385594393 1516153301569393789195795)
                      ·
                        rfl

theorem cell23_2952698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_2952698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952698 prefixEnd_2952698 := by exact prefixLift 2952698
  have htrace : WordTrace (prefixWord ++ tailWord_2952698) baseStart_2952698 baseEnd_2952698 := by
    simpa [prefixWord, tailWord_2952698, baseEnd_2952698] using wordTrace_append hprefix tailTrace_2952698
  have hstable : (prefixWord ++ tailWord_2952698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952698).length < 2 ^ (prefixWord ++ tailWord_2952698).sum := by decide
  have hdescent : baseEnd_2952698 < baseStart_2952698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952701 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_2952701 : Nat := 118140960795 + 2952701 * 2 ^ 59
def prefixEnd_2952701 : Nat := 4983230072969 + 3 ^ 40 * 2952701 * 2
def baseEnd_2952701 : Nat := 1516154842011357277458281

theorem tailTrace_2952701 : CollatzResearch.WordTrace tailWord_2952701 prefixEnd_2952701 1516154842011357277458281 := by
  unfold tailWord_2952701
  simp only [CollatzResearch.WordTrace]
  refine ⟨107693852875876033028033957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71795901917250688685355971 107693852875876033028033957)
  ·
    refine ⟨20192597414226756192756367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107693852875876033028033957 20192597414226756192756367)
    ·
      refine ⟨30288896121340134289134551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20192597414226756192756367 30288896121340134289134551)
      ·
        refine ⟨45433344182010201433701827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30288896121340134289134551 45433344182010201433701827)
        ·
          refine ⟨68150016273015302150552741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45433344182010201433701827 68150016273015302150552741)
          ·
            refine ⟨12778128051190369153228639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68150016273015302150552741 12778128051190369153228639)
            ·
              refine ⟨19167192076785553729842959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12778128051190369153228639 19167192076785553729842959)
              ·
                refine ⟨28750788115178330594764439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19167192076785553729842959 28750788115178330594764439)
                ·
                  refine ⟨43126182172767495892146659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28750788115178330594764439 43126182172767495892146659)
                  ·
                    refine ⟨64689273259151243838219989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43126182172767495892146659 64689273259151243838219989)
                    ·
                      refine ⟨1516154842011357277458281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64689273259151243838219989 1516154842011357277458281)
                      ·
                        rfl

theorem cell23_2952701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_2952701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952701 prefixEnd_2952701 := by exact prefixLift 2952701
  have htrace : WordTrace (prefixWord ++ tailWord_2952701) baseStart_2952701 baseEnd_2952701 := by
    simpa [prefixWord, tailWord_2952701, baseEnd_2952701] using wordTrace_append hprefix tailTrace_2952701
  have hstable : (prefixWord ++ tailWord_2952701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952701).length < 2 ^ (prefixWord ++ tailWord_2952701).sum := by decide
  have hdescent : baseEnd_2952701 < baseStart_2952701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952706 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2952706 : Nat := 118140960795 + 2952706 * 2 ^ 59
def prefixEnd_2952706 : Nat := 4983230072969 + 3 ^ 40 * 2952706 * 2
def baseEnd_2952706 : Nat := 1516157409414629757895759

theorem tailTrace_2952706 : CollatzResearch.WordTrace tailWord_2952706 prefixEnd_2952706 1516157409414629757895759 := by
  unfold tailWord_2952706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26923508810214479720491493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71796023493905279254643981 26923508810214479720491493)
  ·
    refine ⟨5048157901915214947592155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26923508810214479720491493 5048157901915214947592155)
    ·
      refine ⟨7572236852872822421388233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048157901915214947592155 7572236852872822421388233)
      ·
        refine ⟨5679177639654616816041175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7572236852872822421388233 5679177639654616816041175)
        ·
          refine ⟨8518766459481925224061763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679177639654616816041175 8518766459481925224061763)
          ·
            refine ⟨12778149689222887836092645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8518766459481925224061763 12778149689222887836092645)
            ·
              refine ⟨2395903066729291469267371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12778149689222887836092645 2395903066729291469267371)
              ·
                refine ⟨3593854600093937203901057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395903066729291469267371 3593854600093937203901057)
                ·
                  refine ⟨2695390950070452902925793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593854600093937203901057 2695390950070452902925793)
                  ·
                    refine ⟨2021543212552839677194345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2695390950070452902925793 2021543212552839677194345)
                    ·
                      refine ⟨1516157409414629757895759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021543212552839677194345 1516157409414629757895759)
                      ·
                        rfl

theorem cell23_2952706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2952706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952706 prefixEnd_2952706 := by exact prefixLift 2952706
  have htrace : WordTrace (prefixWord ++ tailWord_2952706) baseStart_2952706 baseEnd_2952706 := by
    simpa [prefixWord, tailWord_2952706, baseEnd_2952706] using wordTrace_append hprefix tailTrace_2952706
  have hstable : (prefixWord ++ tailWord_2952706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952706).length < 2 ^ (prefixWord ++ tailWord_2952706).sum := by decide
  have hdescent : baseEnd_2952706 < baseStart_2952706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952710 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2952710 : Nat := 118140960795 + 2952710 * 2 ^ 59
def prefixEnd_2952710 : Nat := 4983230072969 + 3 ^ 40 * 2952710 * 2
def baseEnd_2952710 : Nat := 1516159463337247742245741

theorem tailTrace_2952710 : CollatzResearch.WordTrace tailWord_2952710 prefixEnd_2952710 1516159463337247742245741 := by
  unfold tailWord_2952710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365443160401357111409737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71796120755228951710074389 3365443160401357111409737)
  ·
    refine ⟨2524082370301017833557303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3365443160401357111409737 2524082370301017833557303)
    ·
      refine ⟨3786123555451526750335955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524082370301017833557303 3786123555451526750335955)
      ·
        refine ⟨5679185333177290125503933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786123555451526750335955 5679185333177290125503933)
        ·
          refine ⟨2129694499941483797063975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5679185333177290125503933 2129694499941483797063975)
          ·
            refine ⟨3194541749912225695595963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129694499941483797063975 3194541749912225695595963)
            ·
              refine ⟨4791812624868338543393945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194541749912225695595963 4791812624868338543393945)
              ·
                refine ⟨3593859468651253907545459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791812624868338543393945 3593859468651253907545459)
                ·
                  refine ⟨5390789202976880861318189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593859468651253907545459 5390789202976880861318189)
                  ·
                    refine ⟨2021545951116330322994321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5390789202976880861318189 2021545951116330322994321)
                    ·
                      refine ⟨1516159463337247742245741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021545951116330322994321 1516159463337247742245741)
                      ·
                        rfl

theorem cell23_2952710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2952710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952710 prefixEnd_2952710 := by exact prefixLift 2952710
  have htrace : WordTrace (prefixWord ++ tailWord_2952710) baseStart_2952710 baseEnd_2952710 := by
    simpa [prefixWord, tailWord_2952710, baseEnd_2952710] using wordTrace_append hprefix tailTrace_2952710
  have hstable : (prefixWord ++ tailWord_2952710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952710).length < 2 ^ (prefixWord ++ tailWord_2952710).sum := by decide
  have hdescent : baseEnd_2952710 < baseStart_2952710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952741 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2952741 : Nat := 118140960795 + 2952741 * 2 ^ 59
def prefixEnd_2952741 : Nat := 4983230072969 + 3 ^ 40 * 2952741 * 2
def baseEnd_2952741 : Nat := 1516175381237537120958097

theorem tailTrace_2952741 : CollatzResearch.WordTrace tailWord_2952741 prefixEnd_2952741 1516175381237537120958097 := by
  unfold tailWord_2952741
  simp only [CollatzResearch.WordTrace]
  refine ⟨107695311795731119859490077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71796874530487413239660051 107695311795731119859490077)
  ·
    refine ⟨40385741923399169947308779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107695311795731119859490077 40385741923399169947308779)
    ·
      refine ⟨60578612885098754920963169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40385741923399169947308779 60578612885098754920963169)
      ·
        refine ⟨45433959663824066190722377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60578612885098754920963169 45433959663824066190722377)
        ·
          refine ⟨34075469747868049643041783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45433959663824066190722377 34075469747868049643041783)
          ·
            refine ⟨51113204621802074464562675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34075469747868049643041783 51113204621802074464562675)
            ·
              refine ⟨76669806932703111696844013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51113204621802074464562675 76669806932703111696844013)
              ·
                refine ⟨28751177599763666886316505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76669806932703111696844013 28751177599763666886316505)
                ·
                  refine ⟨21563383199822750164737379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28751177599763666886316505 21563383199822750164737379)
                  ·
                    refine ⟨32345074799734125247106069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21563383199822750164737379 32345074799734125247106069)
                    ·
                      refine ⟨1516175381237537120958097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32345074799734125247106069 1516175381237537120958097)
                      ·
                        rfl

theorem cell23_2952741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2952741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952741 prefixEnd_2952741 := by exact prefixLift 2952741
  have htrace : WordTrace (prefixWord ++ tailWord_2952741) baseStart_2952741 baseEnd_2952741 := by
    simpa [prefixWord, tailWord_2952741, baseEnd_2952741] using wordTrace_append hprefix tailTrace_2952741
  have hstable : (prefixWord ++ tailWord_2952741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952741).length < 2 ^ (prefixWord ++ tailWord_2952741).sum := by decide
  have hdescent : baseEnd_2952741 < baseStart_2952741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952822 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2952822 : Nat := 118140960795 + 2952822 * 2 ^ 59
def prefixEnd_2952822 : Nat := 4983230072969 + 3 ^ 40 * 2952822 * 2
def baseEnd_2952822 : Nat := 1516216973170551304045225

theorem tailTrace_2952822 : CollatzResearch.WordTrace tailWord_2952822 prefixEnd_2952822 1516216973170551304045225 := by
  unfold tailWord_2952822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731141631777354418324295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71798844072291780462125813 6731141631777354418324295)
  ·
    refine ⟨10096712447666031627486443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6731141631777354418324295 10096712447666031627486443)
    ·
      refine ⟨15145068671499047441229665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10096712447666031627486443 15145068671499047441229665)
      ·
        refine ⟨11358801503624285580922249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15145068671499047441229665 11358801503624285580922249)
        ·
          refine ⟨8519101127718214185691687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11358801503624285580922249 8519101127718214185691687)
          ·
            refine ⟨12778651691577321278537531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8519101127718214185691687 12778651691577321278537531)
            ·
              refine ⟨19167977537365981917806297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12778651691577321278537531 19167977537365981917806297)
              ·
                refine ⟨14375983153024486438354723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19167977537365981917806297 14375983153024486438354723)
                ·
                  refine ⟨21563974729536729657532085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14375983153024486438354723 21563974729536729657532085)
                  ·
                    refine ⟨2021622630894068405393633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21563974729536729657532085 2021622630894068405393633)
                    ·
                      refine ⟨1516216973170551304045225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021622630894068405393633 1516216973170551304045225)
                      ·
                        rfl

theorem cell23_2952822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2952822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952822 prefixEnd_2952822 := by exact prefixLift 2952822
  have htrace : WordTrace (prefixWord ++ tailWord_2952822) baseStart_2952822 baseEnd_2952822 := by
    simpa [prefixWord, tailWord_2952822, baseEnd_2952822] using wordTrace_append hprefix tailTrace_2952822
  have hstable : (prefixWord ++ tailWord_2952822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952822).length < 2 ^ (prefixWord ++ tailWord_2952822).sum := by decide
  have hdescent : baseEnd_2952822 < baseStart_2952822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952846 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2952846 : Nat := 118140960795 + 2952846 * 2 ^ 59
def prefixEnd_2952846 : Nat := 4983230072969 + 3 ^ 40 * 2952846 * 2
def baseEnd_2952846 : Nat := 1516229296706259210145115

theorem tailTrace_2952846 : CollatzResearch.WordTrace tailWord_2952846 prefixEnd_2952846 1516229296706259210145115 := by
  unfold tailWord_2952846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462392682543840349007799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71799427640233815194708261 13462392682543840349007799)
  ·
    refine ⟨20193589023815760523511699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13462392682543840349007799 20193589023815760523511699)
    ·
      refine ⟨30290383535723640785267549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20193589023815760523511699 30290383535723640785267549)
      ·
        refine ⟨11358893825896365294475331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30290383535723640785267549 11358893825896365294475331)
        ·
          refine ⟨17038340738844547941712997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358893825896365294475331 17038340738844547941712997)
          ·
            refine ⟨3194688888533352739071187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17038340738844547941712997 3194688888533352739071187)
            ·
              refine ⟨4792033332800029108606781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194688888533352739071187 4792033332800029108606781)
              ·
                refine ⟨1797012499800010915727543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792033332800029108606781 1797012499800010915727543)
                ·
                  refine ⟨2695518749700016373591315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797012499800010915727543 2695518749700016373591315)
                  ·
                    refine ⟨4043278124550024560386973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695518749700016373591315 4043278124550024560386973)
                    ·
                      refine ⟨1516229296706259210145115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043278124550024560386973 1516229296706259210145115)
                      ·
                        rfl

theorem cell23_2952846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2952846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952846 prefixEnd_2952846 := by exact prefixLift 2952846
  have htrace : WordTrace (prefixWord ++ tailWord_2952846) baseStart_2952846 baseEnd_2952846 := by
    simpa [prefixWord, tailWord_2952846, baseEnd_2952846] using wordTrace_append hprefix tailTrace_2952846
  have hstable : (prefixWord ++ tailWord_2952846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952846).length < 2 ^ (prefixWord ++ tailWord_2952846).sum := by decide
  have hdescent : baseEnd_2952846 < baseStart_2952846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952848 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_2952848 : Nat := 118140960795 + 2952848 * 2 ^ 59
def prefixEnd_2952848 : Nat := 4983230072969 + 3 ^ 40 * 2952848 * 2
def baseEnd_2952848 : Nat := 1516230323667568202320105

theorem tailTrace_2952848 : CollatzResearch.WordTrace tailWord_2952848 prefixEnd_2952848 1516230323667568202320105 := by
  unfold tailWord_2952848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53849607203171738566817599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71799476270895651422423465 53849607203171738566817599)
  ·
    refine ⟨80774410804757607850226399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53849607203171738566817599 80774410804757607850226399)
    ·
      refine ⟨121161616207136411775339599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80774410804757607850226399 121161616207136411775339599)
      ·
        refine ⟨181742424310704617663009399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121161616207136411775339599 181742424310704617663009399)
        ·
          refine ⟨272613636466056926494514099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181742424310704617663009399 272613636466056926494514099)
          ·
            refine ⟨408920454699085389741771149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272613636466056926494514099 408920454699085389741771149)
            ·
              refine ⟨153345170512157021153164181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408920454699085389741771149 153345170512157021153164181)
              ·
                refine ⟨7188054867757360366554571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153345170512157021153164181 7188054867757360366554571)
                ·
                  refine ⟨10782082301636040549831857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188054867757360366554571 10782082301636040549831857)
                  ·
                    refine ⟨8086561726227030412373893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10782082301636040549831857 8086561726227030412373893)
                    ·
                      refine ⟨1516230323667568202320105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8086561726227030412373893 1516230323667568202320105)
                      ·
                        rfl

theorem cell23_2952848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_2952848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952848 prefixEnd_2952848 := by exact prefixLift 2952848
  have htrace : WordTrace (prefixWord ++ tailWord_2952848) baseStart_2952848 baseEnd_2952848 := by
    simpa [prefixWord, tailWord_2952848, baseEnd_2952848] using wordTrace_append hprefix tailTrace_2952848
  have hstable : (prefixWord ++ tailWord_2952848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952848).length < 2 ^ (prefixWord ++ tailWord_2952848).sum := by decide
  have hdescent : baseEnd_2952848 < baseStart_2952848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952855 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2952855 : Nat := 118140960795 + 2952855 * 2 ^ 59
def prefixEnd_2952855 : Nat := 4983230072969 + 3 ^ 40 * 2952855 * 2
def baseEnd_2952855 : Nat := 1516233918032149674932573

theorem tailTrace_2952855 : CollatzResearch.WordTrace tailWord_2952855 prefixEnd_2952855 1516233918032149674932573 := by
  unfold tailWord_2952855
  simp only [CollatzResearch.WordTrace]
  refine ⟨107699469717318117329140019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71799646478212078219426679 107699469717318117329140019)
  ·
    refine ⟨161549204575977175993710029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107699469717318117329140019 161549204575977175993710029)
    ·
      refine ⟨60580951715991440997641261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161549204575977175993710029 60580951715991440997641261)
      ·
        refine ⟨22717856893496790374115473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60580951715991440997641261 22717856893496790374115473)
        ·
          refine ⟨17038392670122592780586605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22717856893496790374115473 17038392670122592780586605)
          ·
            refine ⟨6389397251295972292719977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17038392670122592780586605 6389397251295972292719977)
            ·
              refine ⟨4792047938471979219539983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6389397251295972292719977 4792047938471979219539983)
              ·
                refine ⟨7188071907707968829309975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792047938471979219539983 7188071907707968829309975)
                ·
                  refine ⟨10782107861561953243964963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188071907707968829309975 10782107861561953243964963)
                  ·
                    refine ⟨16173161792342929865947445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10782107861561953243964963 16173161792342929865947445)
                    ·
                      refine ⟨1516233918032149674932573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16173161792342929865947445 1516233918032149674932573)
                      ·
                        rfl

theorem cell23_2952855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2952855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952855 prefixEnd_2952855 := by exact prefixLift 2952855
  have htrace : WordTrace (prefixWord ++ tailWord_2952855) baseStart_2952855 baseEnd_2952855 := by
    simpa [prefixWord, tailWord_2952855, baseEnd_2952855] using wordTrace_append hprefix tailTrace_2952855
  have hstable : (prefixWord ++ tailWord_2952855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952855).length < 2 ^ (prefixWord ++ tailWord_2952855).sum := by decide
  have hdescent : baseEnd_2952855 < baseStart_2952855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952862 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2952862 : Nat := 118140960795 + 2952862 * 2 ^ 59
def prefixEnd_2952862 : Nat := 4983230072969 + 3 ^ 40 * 2952862 * 2
def baseEnd_2952862 : Nat := 505412504132243715848347

theorem tailTrace_2952862 : CollatzResearch.WordTrace tailWord_2952862 prefixEnd_2952862 505412504132243715848347 := by
  unfold tailWord_2952862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462465628536594690580605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71799816685528505016429893 13462465628536594690580605)
  ·
    refine ⟨5048424610701223008967727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13462465628536594690580605 5048424610701223008967727)
    ·
      refine ⟨7572636916051834513451591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048424610701223008967727 7572636916051834513451591)
      ·
        refine ⟨11358955374077751770177387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7572636916051834513451591 11358955374077751770177387)
        ·
          refine ⟨17038433061116627655266081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358955374077751770177387 17038433061116627655266081)
          ·
            refine ⟨12778824795837470741449561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17038433061116627655266081 12778824795837470741449561)
            ·
              refine ⟨9584118596878103056087171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12778824795837470741449561 9584118596878103056087171)
              ·
                refine ⟨14376177895317154584130757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584118596878103056087171 14376177895317154584130757)
                ·
                  refine ⟨2695533355371966484524517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14376177895317154584130757 2695533355371966484524517)
                  ·
                    refine ⟨505412504132243715848347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695533355371966484524517 505412504132243715848347)
                    ·
                      rfl

theorem cell23_2952862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2952862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952862 prefixEnd_2952862 := by exact prefixLift 2952862
  have htrace : WordTrace (prefixWord ++ tailWord_2952862) baseStart_2952862 baseEnd_2952862 := by
    simpa [prefixWord, tailWord_2952862, baseEnd_2952862] using wordTrace_append hprefix tailTrace_2952862
  have hstable : (prefixWord ++ tailWord_2952862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952862).length < 2 ^ (prefixWord ++ tailWord_2952862).sum := by decide
  have hdescent : baseEnd_2952862 < baseStart_2952862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952863 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2952863 : Nat := 118140960795 + 2952863 * 2 ^ 59
def prefixEnd_2952863 : Nat := 4983230072969 + 3 ^ 40 * 2952863 * 2
def baseEnd_2952863 : Nat := 1516238025877385643632537

theorem tailTrace_2952863 : CollatzResearch.WordTrace tailWord_2952863 prefixEnd_2952863 1516238025877385643632537 := by
  unfold tailWord_2952863
  simp only [CollatzResearch.WordTrace]
  refine ⟨107699761501289134695431243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71799841000859423130287495 107699761501289134695431243)
  ·
    refine ⟨161549642251933702043146865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107699761501289134695431243 161549642251933702043146865)
    ·
      refine ⟨121162231688950276532360149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161549642251933702043146865 121162231688950276532360149)
      ·
        refine ⟨2839739805209772106227191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121162231688950276532360149 2839739805209772106227191)
        ·
          refine ⟨4259609707814658159340787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839739805209772106227191 4259609707814658159340787)
          ·
            refine ⟨6389414561721987239011181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259609707814658159340787 6389414561721987239011181)
            ·
              refine ⟨2396030460645745214629193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6389414561721987239011181 2396030460645745214629193)
              ·
                refine ⟨1797022845484308910971895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2396030460645745214629193 1797022845484308910971895)
                ·
                  refine ⟨2695534268226463366457843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797022845484308910971895 2695534268226463366457843)
                  ·
                    refine ⟨4043301402339695049686765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695534268226463366457843 4043301402339695049686765)
                    ·
                      refine ⟨1516238025877385643632537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043301402339695049686765 1516238025877385643632537)
                      ·
                        rfl

theorem cell23_2952863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2952863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952863 prefixEnd_2952863 := by exact prefixLift 2952863
  have htrace : WordTrace (prefixWord ++ tailWord_2952863) baseStart_2952863 baseEnd_2952863 := by
    simpa [prefixWord, tailWord_2952863, baseEnd_2952863] using wordTrace_append hprefix tailTrace_2952863
  have hstable : (prefixWord ++ tailWord_2952863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952863).length < 2 ^ (prefixWord ++ tailWord_2952863).sum := by decide
  have hdescent : baseEnd_2952863 < baseStart_2952863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952869 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 1, 2, 2]
def baseStart_2952869 : Nat := 118140960795 + 2952869 * 2 ^ 59
def prefixEnd_2952869 : Nat := 4983230072969 + 3 ^ 40 * 2952869 * 2
def baseEnd_2952869 : Nat := 1516241106761312620157509

theorem tailTrace_2952869 : CollatzResearch.WordTrace tailWord_2952869 prefixEnd_2952869 1516241106761312620157509 := by
  unfold tailWord_2952869
  simp only [CollatzResearch.WordTrace]
  refine ⟨107699980339267397720149661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71799986892844931813433107 107699980339267397720149661)
  ·
    refine ⟨40387492627225274145056123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107699980339267397720149661 40387492627225274145056123)
    ·
      refine ⟨60581238940837911217584185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40387492627225274145056123 60581238940837911217584185)
      ·
        refine ⟨45435929205628433413188139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60581238940837911217584185 45435929205628433413188139)
        ·
          refine ⟨68153893808442650119782209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45435929205628433413188139 68153893808442650119782209)
          ·
            refine ⟨51115420356331987589836657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68153893808442650119782209 51115420356331987589836657)
            ·
              refine ⟨38336565267248990692377493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51115420356331987589836657 38336565267248990692377493)
              ·
                refine ⟨1797026496902296438705195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38336565267248990692377493 1797026496902296438705195)
                ·
                  refine ⟨2695539745353444658057793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797026496902296438705195 2695539745353444658057793)
                  ·
                    refine ⟨2021654809015083493543345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2695539745353444658057793 2021654809015083493543345)
                    ·
                      refine ⟨1516241106761312620157509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021654809015083493543345 1516241106761312620157509)
                      ·
                        rfl

theorem cell23_2952869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_2952869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952869 prefixEnd_2952869 := by exact prefixLift 2952869
  have htrace : WordTrace (prefixWord ++ tailWord_2952869) baseStart_2952869 baseEnd_2952869 := by
    simpa [prefixWord, tailWord_2952869, baseEnd_2952869] using wordTrace_append hprefix tailTrace_2952869
  have hstable : (prefixWord ++ tailWord_2952869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952869).length < 2 ^ (prefixWord ++ tailWord_2952869).sum := by decide
  have hdescent : baseEnd_2952869 < baseStart_2952869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952886 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2952886 : Nat := 118140960795 + 2952886 * 2 ^ 59
def prefixEnd_2952886 : Nat := 4983230072969 + 3 ^ 40 * 2952886 * 2
def baseEnd_2952886 : Nat := 1516249835932439053644931

theorem tailTrace_2952886 : CollatzResearch.WordTrace tailWord_2952886 prefixEnd_2952886 1516249835932439053644931 := by
  unfold tailWord_2952886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731287523762863101469907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71800400253470539749012341 6731287523762863101469907)
  ·
    refine ⟨10096931285644294652204861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6731287523762863101469907 10096931285644294652204861)
    ·
      refine ⟨3786349232116610494576823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10096931285644294652204861 3786349232116610494576823)
      ·
        refine ⟨5679523848174915741865235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786349232116610494576823 5679523848174915741865235)
        ·
          refine ⟨8519285772262373612797853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679523848174915741865235 8519285772262373612797853)
          ·
            refine ⟨3194732164598390104799195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8519285772262373612797853 3194732164598390104799195)
            ·
              refine ⟨4792098246897585157198793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194732164598390104799195 4792098246897585157198793)
              ·
                refine ⟨3594073685173188867899095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4792098246897585157198793 3594073685173188867899095)
                ·
                  refine ⟨5391110527759783301848643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594073685173188867899095 5391110527759783301848643)
                  ·
                    refine ⟨8086665791639674952772965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391110527759783301848643 8086665791639674952772965)
                    ·
                      refine ⟨1516249835932439053644931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8086665791639674952772965 1516249835932439053644931)
                      ·
                        rfl

theorem cell23_2952886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2952886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952886 prefixEnd_2952886 := by exact prefixLift 2952886
  have htrace : WordTrace (prefixWord ++ tailWord_2952886) baseStart_2952886 baseEnd_2952886 := by
    simpa [prefixWord, tailWord_2952886, baseEnd_2952886] using wordTrace_append hprefix tailTrace_2952886
  have hstable : (prefixWord ++ tailWord_2952886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952886).length < 2 ^ (prefixWord ++ tailWord_2952886).sum := by decide
  have hdescent : baseEnd_2952886 < baseStart_2952886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952928 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2952928 : Nat := 118140960795 + 2952928 * 2 ^ 59
def prefixEnd_2952928 : Nat := 4983230072969 + 3 ^ 40 * 2952928 * 2
def baseEnd_2952928 : Nat := 1516271402119927889319737

theorem tailTrace_2952928 : CollatzResearch.WordTrace tailWord_2952928 prefixEnd_2952928 1516271402119927889319737 := by
  unfold tailWord_2952928
  simp only [CollatzResearch.WordTrace]
  refine ⟨53851066123026825398273719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71801421497369100531031625 53851066123026825398273719)
  ·
    refine ⟨80776599184540238097410579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53851066123026825398273719 80776599184540238097410579)
    ·
      refine ⟨121164898776810357146115869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80776599184540238097410579 121164898776810357146115869)
      ·
        refine ⟨45436837041303883929793451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121164898776810357146115869 45436837041303883929793451)
        ·
          refine ⟨68155255561955825894690177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45436837041303883929793451 68155255561955825894690177)
          ·
            refine ⟨51116441671466869421017633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68155255561955825894690177 51116441671466869421017633)
            ·
              refine ⟨38337331253600152065763225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51116441671466869421017633 38337331253600152065763225)
              ·
                refine ⟨28752998440200114049322419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38337331253600152065763225 28752998440200114049322419)
                ·
                  refine ⟨43129497660300171073983629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28752998440200114049322419 43129497660300171073983629)
                  ·
                    refine ⟨16173561622612564152743861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43129497660300171073983629 16173561622612564152743861)
                    ·
                      refine ⟨1516271402119927889319737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16173561622612564152743861 1516271402119927889319737)
                      ·
                        rfl

theorem cell23_2952928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2952928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2952928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2952928 prefixEnd_2952928 := by exact prefixLift 2952928
  have htrace : WordTrace (prefixWord ++ tailWord_2952928) baseStart_2952928 baseEnd_2952928 := by
    simpa [prefixWord, tailWord_2952928, baseEnd_2952928] using wordTrace_append hprefix tailTrace_2952928
  have hstable : (prefixWord ++ tailWord_2952928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952928).length < 2 ^ (prefixWord ++ tailWord_2952928).sum := by decide
  have hdescent : baseEnd_2952928 < baseStart_2952928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953012 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2953012 : Nat := 118140960795 + 2953012 * 2 ^ 59
def prefixEnd_2953012 : Nat := 4983230072969 + 3 ^ 40 * 2953012 * 2
def baseEnd_2953012 : Nat := 505438178164968520223117

theorem tailTrace_2953012 : CollatzResearch.WordTrace tailWord_2953012 prefixEnd_2953012 505438178164968520223117 := by
  unfold tailWord_2953012
  simp only [CollatzResearch.WordTrace]
  refine ⟨53852597988874666571302645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71803463985166222095070193 53852597988874666571302645)
  ·
    refine ⟨5048681061456999991059623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53852597988874666571302645 5048681061456999991059623)
    ·
      refine ⟨7573021592185499986589435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048681061456999991059623 7573021592185499986589435)
      ·
        refine ⟨11359532388278249979884153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573021592185499986589435 11359532388278249979884153)
        ·
          refine ⟨8519649291208687484913115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11359532388278249979884153 8519649291208687484913115)
          ·
            refine ⟨12779473936813031227369673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8519649291208687484913115 12779473936813031227369673)
            ·
              refine ⟨9584605452609773420527255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12779473936813031227369673 9584605452609773420527255)
              ·
                refine ⟨14376908178914660130790883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584605452609773420527255 14376908178914660130790883)
                ·
                  refine ⟨21565362268371990196186325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14376908178914660130790883 21565362268371990196186325)
                  ·
                    refine ⟨505438178164968520223117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21565362268371990196186325 505438178164968520223117)
                    ·
                      rfl

theorem cell23_2953012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2953012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953012 prefixEnd_2953012 := by exact prefixLift 2953012
  have htrace : WordTrace (prefixWord ++ tailWord_2953012) baseStart_2953012 baseEnd_2953012 := by
    simpa [prefixWord, tailWord_2953012, baseEnd_2953012] using wordTrace_append hprefix tailTrace_2953012
  have hstable : (prefixWord ++ tailWord_2953012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953012).length < 2 ^ (prefixWord ++ tailWord_2953012).sum := by decide
  have hdescent : baseEnd_2953012 < baseStart_2953012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953032 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2953032 : Nat := 118140960795 + 2953032 * 2 ^ 59
def prefixEnd_2953032 : Nat := 4983230072969 + 3 ^ 40 * 2953032 * 2
def baseEnd_2953032 : Nat := 1516324804107995482419259

theorem tailTrace_2953032 : CollatzResearch.WordTrace tailWord_2953032 prefixEnd_2953032 1516324804107995482419259 := by
  unfold tailWord_2953032
  simp only [CollatzResearch.WordTrace]
  refine ⟨53852962718838438279166675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71803950291784584372222233 53852962718838438279166675)
  ·
    refine ⟨80779444078257657418750013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53852962718838438279166675 80779444078257657418750013)
    ·
      refine ⟨30292291529346621532031255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80779444078257657418750013 30292291529346621532031255)
      ·
        refine ⟨45438437294019932298046883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30292291529346621532031255 45438437294019932298046883)
        ·
          refine ⟨68157655941029898447070325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45438437294019932298046883 68157655941029898447070325)
          ·
            refine ⟨6389780244471552979412843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68157655941029898447070325 6389780244471552979412843)
            ·
              refine ⟨9584670366707329469119265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389780244471552979412843 9584670366707329469119265)
              ·
                refine ⟨7188502775030497101839449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584670366707329469119265 7188502775030497101839449)
                ·
                  refine ⟨5391377081272872826379587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188502775030497101839449 5391377081272872826379587)
                  ·
                    refine ⟨8087065621909309239569381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391377081272872826379587 8087065621909309239569381)
                    ·
                      refine ⟨1516324804107995482419259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8087065621909309239569381 1516324804107995482419259)
                      ·
                        rfl

theorem cell23_2953032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2953032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953032 prefixEnd_2953032 := by exact prefixLift 2953032
  have htrace : WordTrace (prefixWord ++ tailWord_2953032) baseStart_2953032 baseEnd_2953032 := by
    simpa [prefixWord, tailWord_2953032, baseEnd_2953032] using wordTrace_append hprefix tailTrace_2953032
  have hstable : (prefixWord ++ tailWord_2953032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953032).length < 2 ^ (prefixWord ++ tailWord_2953032).sum := by decide
  have hdescent : baseEnd_2953032 < baseStart_2953032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953065 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_2953065 : Nat := 118140960795 + 2953065 * 2 ^ 59
def prefixEnd_2953065 : Nat := 4983230072969 + 3 ^ 40 * 2953065 * 2
def baseEnd_2953065 : Nat := 1516341748969593853306607

theorem tailTrace_2953065 : CollatzResearch.WordTrace tailWord_2953065 prefixEnd_2953065 1516341748969593853306607 := by
  unfold tailWord_2953065
  simp only [CollatzResearch.WordTrace]
  refine ⟨107707129046557323194284649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71804752697704882129523099 107707129046557323194284649)
  ·
    refine ⟨80780346784917992395713487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107707129046557323194284649 80780346784917992395713487)
    ·
      refine ⟨121170520177376988593570231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80780346784917992395713487 121170520177376988593570231)
      ·
        refine ⟨181755780266065482890355347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121170520177376988593570231 181755780266065482890355347)
        ·
          refine ⟨272633670399098224335533021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181755780266065482890355347 272633670399098224335533021)
          ·
            refine ⟨102237626399661834125824883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272633670399098224335533021 102237626399661834125824883)
            ·
              refine ⟨153356439599492751188737325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102237626399661834125824883 153356439599492751188737325)
              ·
                refine ⟨57508664849809781695776497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153356439599492751188737325 57508664849809781695776497)
                ·
                  refine ⟨43131498637357336271832373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57508664849809781695776497 43131498637357336271832373)
                  ·
                    refine ⟨4043577997252250275484285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43131498637357336271832373 4043577997252250275484285)
                    ·
                      refine ⟨1516341748969593853306607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043577997252250275484285 1516341748969593853306607)
                      ·
                        rfl

theorem cell23_2953065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_2953065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953065 prefixEnd_2953065 := by exact prefixLift 2953065
  have htrace : WordTrace (prefixWord ++ tailWord_2953065) baseStart_2953065 baseEnd_2953065 := by
    simpa [prefixWord, tailWord_2953065, baseEnd_2953065] using wordTrace_append hprefix tailTrace_2953065
  have hstable : (prefixWord ++ tailWord_2953065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953065).length < 2 ^ (prefixWord ++ tailWord_2953065).sum := by decide
  have hdescent : baseEnd_2953065 < baseStart_2953065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953066 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2953066 : Nat := 118140960795 + 2953066 * 2 ^ 59
def prefixEnd_2953066 : Nat := 4983230072969 + 3 ^ 40 * 2953066 * 2
def baseEnd_2953066 : Nat := 1516342262450248349394103

theorem tailTrace_2953066 : CollatzResearch.WordTrace tailWord_2953066 prefixEnd_2953066 1516342262450248349394103 := by
  unfold tailWord_2953066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926791379888425091267763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71804777013035800243380701 26926791379888425091267763)
  ·
    refine ⟨40390187069832637636901645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26926791379888425091267763 40390187069832637636901645)
    ·
      refine ⟨15146320151187239113838117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40390187069832637636901645 15146320151187239113838117)
      ·
        refine ⟨2839935028347607333844647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15146320151187239113838117 2839935028347607333844647)
        ·
          refine ⟨4259902542521411000766971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839935028347607333844647 4259902542521411000766971)
          ·
            refine ⟨6389853813782116501150457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259902542521411000766971 6389853813782116501150457)
            ·
              refine ⟨4792390360336587375862843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6389853813782116501150457 4792390360336587375862843)
              ·
                refine ⟨7188585540504881063794265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792390360336587375862843 7188585540504881063794265)
                ·
                  refine ⟨5391439155378660797845699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188585540504881063794265 5391439155378660797845699)
                  ·
                    refine ⟨8087158733067991196768549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391439155378660797845699 8087158733067991196768549)
                    ·
                      refine ⟨1516342262450248349394103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8087158733067991196768549 1516342262450248349394103)
                      ·
                        rfl

theorem cell23_2953066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2953066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953066 prefixEnd_2953066 := by exact prefixLift 2953066
  have htrace : WordTrace (prefixWord ++ tailWord_2953066) baseStart_2953066 baseEnd_2953066 := by
    simpa [prefixWord, tailWord_2953066, baseEnd_2953066] using wordTrace_append hprefix tailTrace_2953066
  have hstable : (prefixWord ++ tailWord_2953066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953066).length < 2 ^ (prefixWord ++ tailWord_2953066).sum := by decide
  have hdescent : baseEnd_2953066 < baseStart_2953066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953086 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2953086 : Nat := 118140960795 + 2953086 * 2 ^ 59
def prefixEnd_2953086 : Nat := 4983230072969 + 3 ^ 40 * 2953086 * 2
def baseEnd_2953086 : Nat := 1516352532063338271144011

theorem tailTrace_2953086 : CollatzResearch.WordTrace tailWord_2953086 prefixEnd_2953086 1516352532063338271144011 := by
  unfold tailWord_2953086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463486872435155472599889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71805263319654162520532741 13463486872435155472599889)
  ·
    refine ⟨10097615154326366604449917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13463486872435155472599889 10097615154326366604449917)
    ·
      refine ⟨3786605682872387476668719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10097615154326366604449917 3786605682872387476668719)
      ·
        refine ⟨5679908524308581215003079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786605682872387476668719 5679908524308581215003079)
        ·
          refine ⟨8519862786462871822504619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679908524308581215003079 8519862786462871822504619)
          ·
            refine ⟨12779794179694307733756929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8519862786462871822504619 12779794179694307733756929)
            ·
              refine ⟨9584845634770730800317697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12779794179694307733756929 9584845634770730800317697)
              ·
                refine ⟨7188634226078048100238273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584845634770730800317697 7188634226078048100238273)
                ·
                  refine ⟨5391475669558536075178705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188634226078048100238273 5391475669558536075178705)
                  ·
                    refine ⟨4043606752168902056384029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391475669558536075178705 4043606752168902056384029)
                    ·
                      refine ⟨1516352532063338271144011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043606752168902056384029 1516352532063338271144011)
                      ·
                        rfl

theorem cell23_2953086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2953086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953086 prefixEnd_2953086 := by exact prefixLift 2953086
  have htrace : WordTrace (prefixWord ++ tailWord_2953086) baseStart_2953086 baseEnd_2953086 := by
    simpa [prefixWord, tailWord_2953086, baseEnd_2953086] using wordTrace_append hprefix tailTrace_2953086
  have hstable : (prefixWord ++ tailWord_2953086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953086).length < 2 ^ (prefixWord ++ tailWord_2953086).sum := by decide
  have hdescent : baseEnd_2953086 < baseStart_2953086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953116 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2953116 : Nat := 118140960795 + 2953116 * 2 ^ 59
def prefixEnd_2953116 : Nat := 4983230072969 + 3 ^ 40 * 2953116 * 2
def baseEnd_2953116 : Nat := 1516367936482973153768873

theorem tailTrace_2953116 : CollatzResearch.WordTrace tailWord_2953116 prefixEnd_2953116 1516367936482973153768873 := by
  unfold tailWord_2953116
  simp only [CollatzResearch.WordTrace]
  refine ⟨53854494584686279452195601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71805992779581705936260801 53854494584686279452195601)
  ·
    refine ⟨40390870938514709589146701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53854494584686279452195601 40390870938514709589146701)
    ·
      refine ⟨15146576601943016095930013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40390870938514709589146701 15146576601943016095930013)
      ·
        refine ⟨5679966225728631035973755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15146576601943016095930013 5679966225728631035973755)
        ·
          refine ⟨8519949338592946553960633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679966225728631035973755 8519949338592946553960633)
          ·
            refine ⟨6389962003944709915470475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519949338592946553960633 6389962003944709915470475)
            ·
              refine ⟨9584943005917064873205713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389962003944709915470475 9584943005917064873205713)
              ·
                refine ⟨7188707254437798654904285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584943005917064873205713 7188707254437798654904285)
                ·
                  refine ⟨2695765220414174495589107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7188707254437798654904285 2695765220414174495589107)
                  ·
                    refine ⟨4043647830621261743383661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695765220414174495589107 4043647830621261743383661)
                    ·
                      refine ⟨1516367936482973153768873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043647830621261743383661 1516367936482973153768873)
                      ·
                        rfl

theorem cell23_2953116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2953116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953116 prefixEnd_2953116 := by exact prefixLift 2953116
  have htrace : WordTrace (prefixWord ++ tailWord_2953116) baseStart_2953116 baseEnd_2953116 := by
    simpa [prefixWord, tailWord_2953116, baseEnd_2953116] using wordTrace_append hprefix tailTrace_2953116
  have hstable : (prefixWord ++ tailWord_2953116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953116).length < 2 ^ (prefixWord ++ tailWord_2953116).sum := by decide
  have hdescent : baseEnd_2953116 < baseStart_2953116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953139 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 5, 2, 2]
def baseStart_2953139 : Nat := 118140960795 + 2953139 * 2 ^ 59
def prefixEnd_2953139 : Nat := 4983230072969 + 3 ^ 40 * 2953139 * 2
def baseEnd_2953139 : Nat := 1516379746538026563781267

theorem tailTrace_2953139 : CollatzResearch.WordTrace tailWord_2953139 prefixEnd_2953139 1516379746538026563781267 := by
  unfold tailWord_2953139
  simp only [CollatzResearch.WordTrace]
  refine ⟨107709828048289233832478471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71806552032192822554985647 107709828048289233832478471)
  ·
    refine ⟨161564742072433850748717707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107709828048289233832478471 161564742072433850748717707)
    ·
      refine ⟨242347113108650776123076561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161564742072433850748717707 242347113108650776123076561)
      ·
        refine ⟨181760334831488082092307421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242347113108650776123076561 181760334831488082092307421)
        ·
          refine ⟨68160125561808030784615283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181760334831488082092307421 68160125561808030784615283)
          ·
            refine ⟨102240188342712046176922925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68160125561808030784615283 102240188342712046176922925)
            ·
              refine ⟨38340070628517017316346097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102240188342712046176922925 38340070628517017316346097)
              ·
                refine ⟨28755052971387762987259573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38340070628517017316346097 28755052971387762987259573)
                ·
                  refine ⟨2695786216067602780055585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28755052971387762987259573 2695786216067602780055585)
                  ·
                    refine ⟨2021839662050702085041689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2695786216067602780055585 2021839662050702085041689)
                    ·
                      refine ⟨1516379746538026563781267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021839662050702085041689 1516379746538026563781267)
                      ·
                        rfl

theorem cell23_2953139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2, 2].length) (baseStart_2953139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953139 prefixEnd_2953139 := by exact prefixLift 2953139
  have htrace : WordTrace (prefixWord ++ tailWord_2953139) baseStart_2953139 baseEnd_2953139 := by
    simpa [prefixWord, tailWord_2953139, baseEnd_2953139] using wordTrace_append hprefix tailTrace_2953139
  have hstable : (prefixWord ++ tailWord_2953139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953139).length < 2 ^ (prefixWord ++ tailWord_2953139).sum := by decide
  have hdescent : baseEnd_2953139 < baseStart_2953139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953145 : List Nat := [1, 2, 1, 4, 2, 1, 12]
def baseStart_2953145 : Nat := 118140960795 + 2953145 * 2 ^ 59
def prefixEnd_2953145 : Nat := 4983230072969 + 3 ^ 40 * 2953145 * 2
def baseEnd_2953145 : Nat := 18720775647184611608719

theorem tailTrace_2953145 : CollatzResearch.WordTrace tailWord_2953145 prefixEnd_2953145 18720775647184611608719 := by
  unfold tailWord_2953145
  simp only [CollatzResearch.WordTrace]
  refine ⟨107710046886267496857196889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71806697924178331238131259 107710046886267496857196889)
  ·
    refine ⟨80782535164700622642897667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107710046886267496857196889 80782535164700622642897667)
    ·
      refine ⟨121173802747050933964346501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80782535164700622642897667 121173802747050933964346501)
      ·
        refine ⟨22720088015072050118314969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121173802747050933964346501 22720088015072050118314969)
        ·
          refine ⟨17040066011304037588736227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22720088015072050118314969 17040066011304037588736227)
          ·
            refine ⟨25560099016956056383104341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17040066011304037588736227 25560099016956056383104341)
            ·
              refine ⟨18720775647184611608719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25560099016956056383104341 18720775647184611608719)
              ·
                rfl

theorem cell23_2953145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 12].length) (baseStart_2953145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953145 prefixEnd_2953145 := by exact prefixLift 2953145
  have htrace : WordTrace (prefixWord ++ tailWord_2953145) baseStart_2953145 baseEnd_2953145 := by
    simpa [prefixWord, tailWord_2953145, baseEnd_2953145] using wordTrace_append hprefix tailTrace_2953145
  have hstable : (prefixWord ++ tailWord_2953145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953145).length < 2 ^ (prefixWord ++ tailWord_2953145).sum := by decide
  have hdescent : baseEnd_2953145 < baseStart_2953145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953149 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2953149 : Nat := 118140960795 + 2953149 * 2 ^ 59
def prefixEnd_2953149 : Nat := 4983230072969 + 3 ^ 40 * 2953149 * 2
def baseEnd_2953149 : Nat := 505461627114857174885407

theorem tailTrace_2953149 : CollatzResearch.WordTrace tailWord_2953149 prefixEnd_2953149 505461627114857174885407 := by
  unfold tailWord_2953149
  simp only [CollatzResearch.WordTrace]
  refine ⟨107710192778253005540342501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71806795185502003693561667 107710192778253005540342501)
  ·
    refine ⟨20195661145922438538814219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107710192778253005540342501 20195661145922438538814219)
    ·
      refine ⟨30293491718883657808221329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195661145922438538814219 30293491718883657808221329)
      ·
        refine ⟨22720118789162743356165997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30293491718883657808221329 22720118789162743356165997)
        ·
          refine ⟨8520044545936028758562249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22720118789162743356165997 8520044545936028758562249)
          ·
            refine ⟨6390033409452021568921687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8520044545936028758562249 6390033409452021568921687)
            ·
              refine ⟨9585050114178032353382531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390033409452021568921687 9585050114178032353382531)
              ·
                refine ⟨14377575171267048530073797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585050114178032353382531 14377575171267048530073797)
                ·
                  refine ⟨2695795344612571599388837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14377575171267048530073797 2695795344612571599388837)
                  ·
                    refine ⟨505461627114857174885407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695795344612571599388837 505461627114857174885407)
                    ·
                      rfl

theorem cell23_2953149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2953149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953149 prefixEnd_2953149 := by exact prefixLift 2953149
  have htrace : WordTrace (prefixWord ++ tailWord_2953149) baseStart_2953149 baseEnd_2953149 := by
    simpa [prefixWord, tailWord_2953149, baseEnd_2953149] using wordTrace_append hprefix tailTrace_2953149
  have hstable : (prefixWord ++ tailWord_2953149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953149).length < 2 ^ (prefixWord ++ tailWord_2953149).sum := by decide
  have hdescent : baseEnd_2953149 < baseStart_2953149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953166 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_2953166 : Nat := 118140960795 + 2953166 * 2 ^ 59
def prefixEnd_2953166 : Nat := 4983230072969 + 3 ^ 40 * 2953166 * 2
def baseEnd_2953166 : Nat := 505464536838565986047881

theorem tailTrace_2953166 : CollatzResearch.WordTrace tailWord_2953166 prefixEnd_2953166 505464536838565986047881 := by
  unfold tailWord_2953166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463851602398927180463919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71807208546127611629140901 13463851602398927180463919)
  ·
    refine ⟨20195777403598390770695879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13463851602398927180463919 20195777403598390770695879)
    ·
      refine ⟨30293666105397586156043819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195777403598390770695879 30293666105397586156043819)
      ·
        refine ⟨45440499158096379234065729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30293666105397586156043819 45440499158096379234065729)
        ·
          refine ⟨34080374368572284425549297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45440499158096379234065729 34080374368572284425549297)
          ·
            refine ⟨25560280776429213319161973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34080374368572284425549297 25560280776429213319161973)
            ·
              refine ⟨2396276322790238748671435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25560280776429213319161973 2396276322790238748671435)
              ·
                refine ⟨3594414484185358123007153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396276322790238748671435 3594414484185358123007153)
                ·
                  refine ⟨2695810863139018592255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594414484185358123007153 2695810863139018592255365)
                  ·
                    refine ⟨505464536838565986047881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695810863139018592255365 505464536838565986047881)
                    ·
                      rfl

theorem cell23_2953166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_2953166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953166 prefixEnd_2953166 := by exact prefixLift 2953166
  have htrace : WordTrace (prefixWord ++ tailWord_2953166) baseStart_2953166 baseEnd_2953166 := by
    simpa [prefixWord, tailWord_2953166, baseEnd_2953166] using wordTrace_append hprefix tailTrace_2953166
  have hstable : (prefixWord ++ tailWord_2953166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953166).length < 2 ^ (prefixWord ++ tailWord_2953166).sum := by decide
  have hdescent : baseEnd_2953166 < baseStart_2953166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953195 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_2953195 : Nat := 118140960795 + 2953195 * 2 ^ 59
def prefixEnd_2953195 : Nat := 4983230072969 + 3 ^ 40 * 2953195 * 2
def baseEnd_2953195 : Nat := 1516408501454678344681009

theorem tailTrace_2953195 : CollatzResearch.WordTrace tailWord_2953195 prefixEnd_2953195 1516408501454678344681009 := by
  unfold tailWord_2953195
  simp only [CollatzResearch.WordTrace]
  refine ⟨107711870536086355396517039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71807913690724236931011359 107711870536086355396517039)
  ·
    refine ⟨161567805804129533094775559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107711870536086355396517039 161567805804129533094775559)
    ·
      refine ⟨242351708706194299642163339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161567805804129533094775559 242351708706194299642163339)
      ·
        refine ⟨363527563059291449463245009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242351708706194299642163339 363527563059291449463245009)
        ·
          refine ⟨272645672294468587097433757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363527563059291449463245009 272645672294468587097433757)
          ·
            refine ⟨102242127110425720161537659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272645672294468587097433757 102242127110425720161537659)
            ·
              refine ⟨153363190665638580242306489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102242127110425720161537659 153363190665638580242306489)
              ·
                refine ⟨115022392999228935181729867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153363190665638580242306489 115022392999228935181729867)
                ·
                  refine ⟨172533589498843402772594801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115022392999228935181729867 172533589498843402772594801)
                  ·
                    refine ⟨129400192124132552079446101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172533589498843402772594801 129400192124132552079446101)
                    ·
                      refine ⟨1516408501454678344681009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129400192124132552079446101 1516408501454678344681009)
                      ·
                        rfl

theorem cell23_2953195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_2953195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953195 prefixEnd_2953195 := by exact prefixLift 2953195
  have htrace : WordTrace (prefixWord ++ tailWord_2953195) baseStart_2953195 baseEnd_2953195 := by
    simpa [prefixWord, tailWord_2953195, baseEnd_2953195] using wordTrace_append hprefix tailTrace_2953195
  have hstable : (prefixWord ++ tailWord_2953195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953195).length < 2 ^ (prefixWord ++ tailWord_2953195).sum := by decide
  have hdescent : baseEnd_2953195 < baseStart_2953195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953212 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2953212 : Nat := 118140960795 + 2953212 * 2 ^ 59
def prefixEnd_2953212 : Nat := 4983230072969 + 3 ^ 40 * 2953212 * 2
def baseEnd_2953212 : Nat := 1516417230625804778168431

theorem tailTrace_2953212 : CollatzResearch.WordTrace tailWord_2953212 prefixEnd_2953212 1516417230625804778168431 := by
  unfold tailWord_2953212
  simp only [CollatzResearch.WordTrace]
  refine ⟨53856245288512383649942945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71808327051349844866590593 53856245288512383649942945)
  ·
    refine ⟨40392183966384287737457209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53856245288512383649942945 40392183966384287737457209)
    ·
      refine ⟨30294137974788215803092907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40392183966384287737457209 30294137974788215803092907)
      ·
        refine ⟨45441206962182323704639361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30294137974788215803092907 45441206962182323704639361)
        ·
          refine ⟨34080905221636742778479521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45441206962182323704639361 34080905221636742778479521)
          ·
            refine ⟨25560678916227557083859641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34080905221636742778479521 25560678916227557083859641)
            ·
              refine ⟨19170509187170667812894731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25560678916227557083859641 19170509187170667812894731)
              ·
                refine ⟨28755763780756001719342097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19170509187170667812894731 28755763780756001719342097)
                ·
                  refine ⟨21566822835567001289506573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28755763780756001719342097 21566822835567001289506573)
                  ·
                    refine ⟨8087558563337625483564965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21566822835567001289506573 8087558563337625483564965)
                    ·
                      refine ⟨1516417230625804778168431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8087558563337625483564965 1516417230625804778168431)
                      ·
                        rfl

theorem cell23_2953212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2953212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953212 prefixEnd_2953212 := by exact prefixLift 2953212
  have htrace : WordTrace (prefixWord ++ tailWord_2953212) baseStart_2953212 baseEnd_2953212 := by
    simpa [prefixWord, tailWord_2953212, baseEnd_2953212] using wordTrace_append hprefix tailTrace_2953212
  have hstable : (prefixWord ++ tailWord_2953212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953212).length < 2 ^ (prefixWord ++ tailWord_2953212).sum := by decide
  have hdescent : baseEnd_2953212 < baseStart_2953212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953223 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2953223 : Nat := 118140960795 + 2953223 * 2 ^ 59
def prefixEnd_2953223 : Nat := 4983230072969 + 3 ^ 40 * 2953223 * 2
def baseEnd_2953223 : Nat := 1516422878913004235130881

theorem tailTrace_2953223 : CollatzResearch.WordTrace tailWord_2953223 prefixEnd_2953223 1516422878913004235130881 := by
  unfold tailWord_2953223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107712891779984916178536323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71808594519989944119024215 107712891779984916178536323)
  ·
    refine ⟨161569337669977374267804485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107712891779984916178536323 161569337669977374267804485)
    ·
      refine ⟨30294250813120757675213341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161569337669977374267804485 30294250813120757675213341)
      ·
        refine ⟨11360344054920284128205003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30294250813120757675213341 11360344054920284128205003)
        ·
          refine ⟨17040516082380426192307505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11360344054920284128205003 17040516082380426192307505)
          ·
            refine ⟨12780387061785319644230629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17040516082380426192307505 12780387061785319644230629)
            ·
              refine ⟨2396322574084747433293243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12780387061785319644230629 2396322574084747433293243)
              ·
                refine ⟨3594483861127121149939865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396322574084747433293243 3594483861127121149939865)
                ·
                  refine ⟨2695862895845340862454899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594483861127121149939865 2695862895845340862454899)
                  ·
                    refine ⟨4043794343768011293682349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695862895845340862454899 4043794343768011293682349)
                    ·
                      refine ⟨1516422878913004235130881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043794343768011293682349 1516422878913004235130881)
                      ·
                        rfl

theorem cell23_2953223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2953223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953223 prefixEnd_2953223 := by exact prefixLift 2953223
  have htrace : WordTrace (prefixWord ++ tailWord_2953223) baseStart_2953223 baseEnd_2953223 := by
    simpa [prefixWord, tailWord_2953223, baseEnd_2953223] using wordTrace_append hprefix tailTrace_2953223
  have hstable : (prefixWord ++ tailWord_2953223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953223).length < 2 ^ (prefixWord ++ tailWord_2953223).sum := by decide
  have hdescent : baseEnd_2953223 < baseStart_2953223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953232 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_2953232 : Nat := 118140960795 + 2953232 * 2 ^ 59
def prefixEnd_2953232 : Nat := 4983230072969 + 3 ^ 40 * 2953232 * 2
def baseEnd_2953232 : Nat := 1516427500238894699918339

theorem tailTrace_2953232 : CollatzResearch.WordTrace tailWord_2953232 prefixEnd_2953232 1516427500238894699918339 := by
  unfold tailWord_2953232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53856610018476155357806975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71808813357968207143742633 53856610018476155357806975)
  ·
    refine ⟨80784915027714233036710463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53856610018476155357806975 80784915027714233036710463)
    ·
      refine ⟨121177372541571349555065695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80784915027714233036710463 121177372541571349555065695)
      ·
        refine ⟨181766058812357024332598543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121177372541571349555065695 181766058812357024332598543)
        ·
          refine ⟨272649088218535536498897815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181766058812357024332598543 272649088218535536498897815)
          ·
            refine ⟨408973632327803304748346723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272649088218535536498897815 408973632327803304748346723)
            ·
              refine ⟨613460448491704957122520085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408973632327803304748346723 613460448491704957122520085)
              ·
                refine ⟨28755958523048669865118129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 613460448491704957122520085 28755958523048669865118129)
                ·
                  refine ⟨21566968892286502398838597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28755958523048669865118129 21566968892286502398838597)
                  ·
                    refine ⟨4043806667303719199782237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21566968892286502398838597 4043806667303719199782237)
                    ·
                      refine ⟨1516427500238894699918339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4043806667303719199782237 1516427500238894699918339)
                      ·
                        rfl

theorem cell23_2953232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_2953232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953232 prefixEnd_2953232 := by exact prefixLift 2953232
  have htrace : WordTrace (prefixWord ++ tailWord_2953232) baseStart_2953232 baseEnd_2953232 := by
    simpa [prefixWord, tailWord_2953232, baseEnd_2953232] using wordTrace_append hprefix tailTrace_2953232
  have hstable : (prefixWord ++ tailWord_2953232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953232).length < 2 ^ (prefixWord ++ tailWord_2953232).sum := by decide
  have hdescent : baseEnd_2953232 < baseStart_2953232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953286 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2953286 : Nat := 118140960795 + 2953286 * 2 ^ 59
def prefixEnd_2953286 : Nat := 4983230072969 + 3 ^ 40 * 2953286 * 2
def baseEnd_2953286 : Nat := 168495025354915276515899

theorem tailTrace_2953286 : CollatzResearch.WordTrace tailWord_2953286 prefixEnd_2953286 168495025354915276515899 := by
  unfold tailWord_2953286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366099674336146185564991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71810126385837785292053141 3366099674336146185564991)
  ·
    refine ⟨5049149511504219278347487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3366099674336146185564991 5049149511504219278347487)
    ·
      refine ⟨7573724267256328917521231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5049149511504219278347487 7573724267256328917521231)
      ·
        refine ⟨11360586400884493376281847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573724267256328917521231 11360586400884493376281847)
        ·
          refine ⟨17040879601326740064422771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11360586400884493376281847 17040879601326740064422771)
          ·
            refine ⟨25561319401990110096634157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17040879601326740064422771 25561319401990110096634157)
            ·
              refine ⟨9585494775746291286237809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25561319401990110096634157 9585494775746291286237809)
              ·
                refine ⟨7189121081809718464678357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585494775746291286237809 7189121081809718464678357)
                ·
                  refine ⟨168495025354915276515899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7189121081809718464678357 168495025354915276515899)
                  ·
                    rfl

theorem cell23_2953286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2953286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953286 prefixEnd_2953286 := by exact prefixLift 2953286
  have htrace : WordTrace (prefixWord ++ tailWord_2953286) baseStart_2953286 baseEnd_2953286 := by
    simpa [prefixWord, tailWord_2953286, baseEnd_2953286] using wordTrace_append hprefix tailTrace_2953286
  have hstable : (prefixWord ++ tailWord_2953286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953286).length < 2 ^ (prefixWord ++ tailWord_2953286).sum := by decide
  have hdescent : baseEnd_2953286 < baseStart_2953286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953289 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 5, 2]
def baseStart_2953289 : Nat := 118140960795 + 2953289 * 2 ^ 59
def prefixEnd_2953289 : Nat := 4983230072969 + 3 ^ 40 * 2953289 * 2
def baseEnd_2953289 : Nat := 1516456768636200976905577

theorem tailTrace_2953289 : CollatzResearch.WordTrace tailWord_2953289 prefixEnd_2953289 1516456768636200976905577 := by
  unfold tailWord_2953289
  simp only [CollatzResearch.WordTrace]
  refine ⟨107715298997745809450438921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71810199331830539633625947 107715298997745809450438921)
  ·
    refine ⟨80786474248309357087829191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107715298997745809450438921 80786474248309357087829191)
    ·
      refine ⟨121179711372464035631743787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80786474248309357087829191 121179711372464035631743787)
      ·
        refine ⟨181769567058696053447615681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121179711372464035631743787 181769567058696053447615681)
        ·
          refine ⟨136327175294022040085711761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181769567058696053447615681 136327175294022040085711761)
          ·
            refine ⟨102245381470516530064283821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136327175294022040085711761 102245381470516530064283821)
            ·
              refine ⟨38342018051443698774106433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102245381470516530064283821 38342018051443698774106433)
              ·
                refine ⟨28756513538582774080579825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38342018051443698774106433 28756513538582774080579825)
                ·
                  refine ⟨21567385153937080560434869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28756513538582774080579825 21567385153937080560434869)
                  ·
                    refine ⟨2021942358181601302540769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21567385153937080560434869 2021942358181601302540769)
                    ·
                      refine ⟨1516456768636200976905577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021942358181601302540769 1516456768636200976905577)
                      ·
                        rfl

theorem cell23_2953289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5, 2].length) (baseStart_2953289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953289 prefixEnd_2953289 := by exact prefixLift 2953289
  have htrace : WordTrace (prefixWord ++ tailWord_2953289) baseStart_2953289 baseEnd_2953289 := by
    simpa [prefixWord, tailWord_2953289, baseEnd_2953289] using wordTrace_append hprefix tailTrace_2953289
  have hstable : (prefixWord ++ tailWord_2953289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953289).length < 2 ^ (prefixWord ++ tailWord_2953289).sum := by decide
  have hdescent : baseEnd_2953289 < baseStart_2953289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953292 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2953292 : Nat := 118140960795 + 2953292 * 2 ^ 59
def prefixEnd_2953292 : Nat := 4983230072969 + 3 ^ 40 * 2953292 * 2
def baseEnd_2953292 : Nat := 1516458309078164465168063

theorem tailTrace_2953292 : CollatzResearch.WordTrace tailWord_2953292 prefixEnd_2953292 1516458309078164465168063 := by
  unfold tailWord_2953292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53857704208367470481399065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71810272277823293975198753 53857704208367470481399065)
  ·
    refine ⟨40393278156275602861049299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53857704208367470481399065 40393278156275602861049299)
    ·
      refine ⟨60589917234413404291573949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40393278156275602861049299 60589917234413404291573949)
      ·
        refine ⟨22721218962905026609340231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60589917234413404291573949 22721218962905026609340231)
        ·
          refine ⟨34081828444357539914010347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22721218962905026609340231 34081828444357539914010347)
          ·
            refine ⟨51122742666536309871015521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34081828444357539914010347 51122742666536309871015521)
            ·
              refine ⟨38342056999902232403261641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51122742666536309871015521 38342056999902232403261641)
              ·
                refine ⟨28756542749926674302446231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38342056999902232403261641 28756542749926674302446231)
                ·
                  refine ⟨43134814124890011453669347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28756542749926674302446231 43134814124890011453669347)
                  ·
                    refine ⟨64702221187335017180504021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43134814124890011453669347 64702221187335017180504021)
                    ·
                      refine ⟨1516458309078164465168063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64702221187335017180504021 1516458309078164465168063)
                      ·
                        rfl

theorem cell23_2953292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2953292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953292 prefixEnd_2953292 := by exact prefixLift 2953292
  have htrace : WordTrace (prefixWord ++ tailWord_2953292) baseStart_2953292 baseEnd_2953292 := by
    simpa [prefixWord, tailWord_2953292, baseEnd_2953292] using wordTrace_append hprefix tailTrace_2953292
  have hstable : (prefixWord ++ tailWord_2953292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953292).length < 2 ^ (prefixWord ++ tailWord_2953292).sum := by decide
  have hdescent : baseEnd_2953292 < baseStart_2953292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953314 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2953314 : Nat := 118140960795 + 2953314 * 2 ^ 59
def prefixEnd_2953314 : Nat := 4983230072969 + 3 ^ 40 * 2953314 * 2
def baseEnd_2953314 : Nat := 1516469605652563379092963

theorem tailTrace_2953314 : CollatzResearch.WordTrace tailWord_2953314 prefixEnd_2953314 1516469605652563379092963 := by
  unfold tailWord_2953314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26929052705663809680024749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71810807215103492480065997 26929052705663809680024749)
  ·
    refine ⟨10098394764623928630009281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26929052705663809680024749 10098394764623928630009281)
    ·
      refine ⟨7573796073467946472506961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10098394764623928630009281 7573796073467946472506961)
      ·
        refine ⟨5680347055100959854380221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7573796073467946472506961 5680347055100959854380221)
        ·
          refine ⟨2130130145662859945392583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5680347055100959854380221 2130130145662859945392583)
          ·
            refine ⟨3195195218494289918088875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130130145662859945392583 3195195218494289918088875)
            ·
              refine ⟨4792792827741434877133313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195195218494289918088875 4792792827741434877133313)
              ·
                refine ⟨3594594620806076157849985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4792792827741434877133313 3594594620806076157849985)
                ·
                  refine ⟨2695945965604557118387489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594594620806076157849985 2695945965604557118387489)
                  ·
                    refine ⟨2021959474203417838790617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2695945965604557118387489 2021959474203417838790617)
                    ·
                      refine ⟨1516469605652563379092963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2021959474203417838790617 1516469605652563379092963)
                      ·
                        rfl

theorem cell23_2953314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2953314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953314 prefixEnd_2953314 := by exact prefixLift 2953314
  have htrace : WordTrace (prefixWord ++ tailWord_2953314) baseStart_2953314 baseEnd_2953314 := by
    simpa [prefixWord, tailWord_2953314, baseEnd_2953314] using wordTrace_append hprefix tailTrace_2953314
  have hstable : (prefixWord ++ tailWord_2953314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953314).length < 2 ^ (prefixWord ++ tailWord_2953314).sum := by decide
  have hdescent : baseEnd_2953314 < baseStart_2953314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953319 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2953319 : Nat := 118140960795 + 2953319 * 2 ^ 59
def prefixEnd_2953319 : Nat := 4983230072969 + 3 ^ 40 * 2953319 * 2
def baseEnd_2953319 : Nat := 1516472173055835859530439

theorem tailTrace_2953319 : CollatzResearch.WordTrace tailWord_2953319 prefixEnd_2953319 1516472173055835859530439 := by
  unfold tailWord_2953319
  simp only [CollatzResearch.WordTrace]
  refine ⟨107716393187637124574031011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71810928791758083049354007 107716393187637124574031011)
  ·
    refine ⟨161574589781455686861046517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107716393187637124574031011 161574589781455686861046517)
    ·
      refine ⟨15147617792011470643223111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161574589781455686861046517 15147617792011470643223111)
      ·
        refine ⟨22721426688017205964834667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15147617792011470643223111 22721426688017205964834667)
        ·
          refine ⟨34082140032025808947252001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22721426688017205964834667 34082140032025808947252001)
          ·
            refine ⟨25561605024019356710439001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34082140032025808947252001 25561605024019356710439001)
            ·
              refine ⟨19171203768014517532829251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25561605024019356710439001 19171203768014517532829251)
              ·
                refine ⟨28756805652021776299243877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19171203768014517532829251 28756805652021776299243877)
                ·
                  refine ⟨5391901059754083056108227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28756805652021776299243877 5391901059754083056108227)
                  ·
                    refine ⟨8087851589631124584162341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391901059754083056108227 8087851589631124584162341)
                    ·
                      refine ⟨1516472173055835859530439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8087851589631124584162341 1516472173055835859530439)
                      ·
                        rfl

theorem cell23_2953319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2953319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953319 prefixEnd_2953319 := by exact prefixLift 2953319
  have htrace : WordTrace (prefixWord ++ tailWord_2953319) baseStart_2953319 baseEnd_2953319 := by
    simpa [prefixWord, tailWord_2953319, baseEnd_2953319] using wordTrace_append hprefix tailTrace_2953319
  have hstable : (prefixWord ++ tailWord_2953319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953319).length < 2 ^ (prefixWord ++ tailWord_2953319).sum := by decide
  have hdescent : baseEnd_2953319 < baseStart_2953319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953380 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_2953380 : Nat := 118140960795 + 2953380 * 2 ^ 59
def prefixEnd_2953380 : Nat := 4983230072969 + 3 ^ 40 * 2953380 * 2
def baseEnd_2953380 : Nat := 505501165125253373622553

theorem tailTrace_2953380 : CollatzResearch.WordTrace tailWord_2953380 prefixEnd_2953380 505501165125253373622553 := by
  unfold tailWord_2953380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53859309020208065996000797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71812412026944087994667729 53859309020208065996000797)
  ·
    refine ⟨20197240882578024748500299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53859309020208065996000797 20197240882578024748500299)
    ·
      refine ⟨30295861323867037122750449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20197240882578024748500299 30295861323867037122750449)
      ·
        refine ⟨22721895992900277842062837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30295861323867037122750449 22721895992900277842062837)
        ·
          refine ⟨2130177749334401047693391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22721895992900277842062837 2130177749334401047693391)
          ·
            refine ⟨3195266624001601571540087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130177749334401047693391 3195266624001601571540087)
            ·
              refine ⟨4792899936002402357310131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195266624001601571540087 4792899936002402357310131)
              ·
                refine ⟨7189349904003603535965197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792899936002402357310131 7189349904003603535965197)
                ·
                  refine ⟨2696006214001351325986949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7189349904003603535965197 2696006214001351325986949)
                  ·
                    refine ⟨505501165125253373622553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2696006214001351325986949 505501165125253373622553)
                    ·
                      rfl

theorem cell23_2953380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_2953380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953380 prefixEnd_2953380 := by exact prefixLift 2953380
  have htrace : WordTrace (prefixWord ++ tailWord_2953380) baseStart_2953380 baseEnd_2953380 := by
    simpa [prefixWord, tailWord_2953380, baseEnd_2953380] using wordTrace_append hprefix tailTrace_2953380
  have hstable : (prefixWord ++ tailWord_2953380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953380).length < 2 ^ (prefixWord ++ tailWord_2953380).sum := by decide
  have hdescent : baseEnd_2953380 < baseStart_2953380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953419 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 1, 6]
def baseStart_2953419 : Nat := 118140960795 + 2953419 * 2 ^ 59
def prefixEnd_2953419 : Nat := 4983230072969 + 3 ^ 40 * 2953419 * 2
def baseEnd_2953419 : Nat := 505507840373761822759993

theorem tailTrace_2953419 : CollatzResearch.WordTrace tailWord_2953419 prefixEnd_2953419 505507840373761822759993 := by
  unfold tailWord_2953419
  simp only [CollatzResearch.WordTrace]
  refine ⟨107720040487274841652671311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71813360324849894435114207 107720040487274841652671311)
  ·
    refine ⟨161580060730912262479006967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107720040487274841652671311 161580060730912262479006967)
    ·
      refine ⟨242370091096368393718510451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161580060730912262479006967 242370091096368393718510451)
      ·
        refine ⟨363555136644552590577765677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242370091096368393718510451 363555136644552590577765677)
        ·
          refine ⟨136333176241707221466662129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363555136644552590577765677 136333176241707221466662129)
          ·
            refine ⟨102249882181280416099996597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136333176241707221466662129 102249882181280416099996597)
            ·
              refine ⟨9585926454495039009374681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102249882181280416099996597 9585926454495039009374681)
              ·
                refine ⟨7189444840871279257031011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585926454495039009374681 7189444840871279257031011)
                ·
                  refine ⟨10784167261306918885546517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7189444840871279257031011 10784167261306918885546517)
                  ·
                    refine ⟨505507840373761822759993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10784167261306918885546517 505507840373761822759993)
                    ·
                      rfl

theorem cell23_2953419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 6].length) (baseStart_2953419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953419 prefixEnd_2953419 := by exact prefixLift 2953419
  have htrace : WordTrace (prefixWord ++ tailWord_2953419) baseStart_2953419 baseEnd_2953419 := by
    simpa [prefixWord, tailWord_2953419, baseEnd_2953419] using wordTrace_append hprefix tailTrace_2953419
  have hstable : (prefixWord ++ tailWord_2953419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953419).length < 2 ^ (prefixWord ++ tailWord_2953419).sum := by decide
  have hdescent : baseEnd_2953419 < baseStart_2953419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953437 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2953437 : Nat := 118140960795 + 2953437 * 2 ^ 59
def prefixEnd_2953437 : Nat := 4983230072969 + 3 ^ 40 * 2953437 * 2
def baseEnd_2953437 : Nat := 1516532763773066397854897

theorem tailTrace_2953437 : CollatzResearch.WordTrace tailWord_2953437 prefixEnd_2953437 1516532763773066397854897 := by
  unfold tailWord_2953437
  simp only [CollatzResearch.WordTrace]
  refine ⟨107720697001209630726826565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71813798000806420484551043 107720697001209630726826565)
  ·
    refine ⟨20197630687726805761279981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107720697001209630726826565 20197630687726805761279981)
    ·
      refine ⟨7574111507897552160479993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20197630687726805761279981 7574111507897552160479993)
      ·
        refine ⟨5680583630923164120359995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7574111507897552160479993 5680583630923164120359995)
        ·
          refine ⟨8520875446384746180539993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680583630923164120359995 8520875446384746180539993)
          ·
            refine ⟨6390656584788559635404995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8520875446384746180539993 6390656584788559635404995)
            ·
              refine ⟨9585984877182839453107493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390656584788559635404995 9585984877182839453107493)
              ·
                refine ⟨1797372164471782397457655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9585984877182839453107493 1797372164471782397457655)
                ·
                  refine ⟨2696058246707673596186483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797372164471782397457655 2696058246707673596186483)
                  ·
                    refine ⟨4044087370061510394279725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696058246707673596186483 4044087370061510394279725)
                    ·
                      refine ⟨1516532763773066397854897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4044087370061510394279725 1516532763773066397854897)
                      ·
                        rfl

theorem cell23_2953437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2953437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953437 prefixEnd_2953437 := by exact prefixLift 2953437
  have htrace : WordTrace (prefixWord ++ tailWord_2953437) baseStart_2953437 baseEnd_2953437 := by
    simpa [prefixWord, tailWord_2953437, baseEnd_2953437] using wordTrace_append hprefix tailTrace_2953437
  have hstable : (prefixWord ++ tailWord_2953437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953437).length < 2 ^ (prefixWord ++ tailWord_2953437).sum := by decide
  have hdescent : baseEnd_2953437 < baseStart_2953437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953439 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_2953439 : Nat := 118140960795 + 2953439 * 2 ^ 59
def prefixEnd_2953439 : Nat := 4983230072969 + 3 ^ 40 * 2953439 * 2
def baseEnd_2953439 : Nat := 1516533790734375390029887

theorem tailTrace_2953439 : CollatzResearch.WordTrace tailWord_2953439 prefixEnd_2953439 1516533790734375390029887 := by
  unfold tailWord_2953439
  simp only [CollatzResearch.WordTrace]
  refine ⟨107720769947202385068399371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71813846631468256712266247 107720769947202385068399371)
  ·
    refine ⟨161581154920803577602599057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107720769947202385068399371 161581154920803577602599057)
    ·
      refine ⟨121185866190602683201949293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161581154920803577602599057 121185866190602683201949293)
      ·
        refine ⟨45444699821476006200730985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121185866190602683201949293 45444699821476006200730985)
        ·
          refine ⟨34083524866107004650548239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45444699821476006200730985 34083524866107004650548239)
          ·
            refine ⟨51125287299160506975822359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34083524866107004650548239 51125287299160506975822359)
            ·
              refine ⟨76687930948740760463733539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51125287299160506975822359 76687930948740760463733539)
              ·
                refine ⟨115031896423111140695600309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76687930948740760463733539 115031896423111140695600309)
                ·
                  refine ⟨10784240289666669440212529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115031896423111140695600309 10784240289666669440212529)
                  ·
                    refine ⟨8088180217250002080159397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10784240289666669440212529 8088180217250002080159397)
                    ·
                      refine ⟨1516533790734375390029887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8088180217250002080159397 1516533790734375390029887)
                      ·
                        rfl

theorem cell23_2953439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_2953439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953439 prefixEnd_2953439 := by exact prefixLift 2953439
  have htrace : WordTrace (prefixWord ++ tailWord_2953439) baseStart_2953439 baseEnd_2953439 := by
    simpa [prefixWord, tailWord_2953439, baseEnd_2953439] using wordTrace_append hprefix tailTrace_2953439
  have hstable : (prefixWord ++ tailWord_2953439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953439).length < 2 ^ (prefixWord ++ tailWord_2953439).sum := by decide
  have hdescent : baseEnd_2953439 < baseStart_2953439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953453 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2953453 : Nat := 118140960795 + 2953453 * 2 ^ 59
def prefixEnd_2953453 : Nat := 4983230072969 + 3 ^ 40 * 2953453 * 2
def baseEnd_2953453 : Nat := 505513659821179445084941

theorem tailTrace_2953453 : CollatzResearch.WordTrace tailWord_2953453 prefixEnd_2953453 505513659821179445084941 := by
  unfold tailWord_2953453
  simp only [CollatzResearch.WordTrace]
  refine ⟨107721280569151665459409013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71814187046101110306272675 107721280569151665459409013)
  ·
    refine ⟨10098870053357968636819595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107721280569151665459409013 10098870053357968636819595)
    ·
      refine ⟨15148305080036952955229393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10098870053357968636819595 15148305080036952955229393)
      ·
        refine ⟨11361228810027714716422045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15148305080036952955229393 11361228810027714716422045)
        ·
          refine ⟨4260460803760393018658267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11361228810027714716422045 4260460803760393018658267)
          ·
            refine ⟨6390691205640589527987401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260460803760393018658267 6390691205640589527987401)
            ·
              refine ⟨4793018404230442145990551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6390691205640589527987401 4793018404230442145990551)
              ·
                refine ⟨7189527606345663218985827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4793018404230442145990551 7189527606345663218985827)
                ·
                  refine ⟨10784291409518494828478741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7189527606345663218985827 10784291409518494828478741)
                  ·
                    refine ⟨505513659821179445084941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10784291409518494828478741 505513659821179445084941)
                    ·
                      rfl

theorem cell23_2953453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2953453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953453 prefixEnd_2953453 := by exact prefixLift 2953453
  have htrace : WordTrace (prefixWord ++ tailWord_2953453) baseStart_2953453 baseEnd_2953453 := by
    simpa [prefixWord, tailWord_2953453, baseEnd_2953453] using wordTrace_append hprefix tailTrace_2953453
  have hstable : (prefixWord ++ tailWord_2953453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953453).length < 2 ^ (prefixWord ++ tailWord_2953453).sum := by decide
  have hdescent : baseEnd_2953453 < baseStart_2953453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953466 : List Nat := [3, 1, 1, 1, 1, 6, 3, 7]
def baseStart_2953466 : Nat := 118140960795 + 2953466 * 2 ^ 59
def prefixEnd_2953466 : Nat := 4983230072969 + 3 ^ 40 * 2953466 * 2
def baseEnd_2953466 : Nat := 56168431656001732755269

theorem tailTrace_2953466 : CollatzResearch.WordTrace tailWord_2953466 prefixEnd_2953466 56168431656001732755269 := by
  unfold tailWord_2953466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26930438679526142169908063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71814503145403045786421501 26930438679526142169908063)
  ·
    refine ⟨40395658019289213254862095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26930438679526142169908063 40395658019289213254862095)
    ·
      refine ⟨60593487028933819882293143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40395658019289213254862095 60593487028933819882293143)
      ·
        refine ⟨90890230543400729823439715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60593487028933819882293143 90890230543400729823439715)
        ·
          refine ⟨136335345815101094735159573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90890230543400729823439715 136335345815101094735159573)
          ·
            refine ⟨6390719335082863815710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136335345815101094735159573 6390719335082863815710605)
            ·
              refine ⟨2396519750656073930891477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6390719335082863815710605 2396519750656073930891477)
              ·
                refine ⟨56168431656001732755269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2396519750656073930891477 56168431656001732755269)
                ·
                  rfl

theorem cell23_2953466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_2953466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953466 prefixEnd_2953466 := by exact prefixLift 2953466
  have htrace : WordTrace (prefixWord ++ tailWord_2953466) baseStart_2953466 baseEnd_2953466 := by
    simpa [prefixWord, tailWord_2953466, baseEnd_2953466] using wordTrace_append hprefix tailTrace_2953466
  have hstable : (prefixWord ++ tailWord_2953466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953466).length < 2 ^ (prefixWord ++ tailWord_2953466).sum := by decide
  have hdescent : baseEnd_2953466 < baseStart_2953466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953480 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_2953480 : Nat := 118140960795 + 2953480 * 2 ^ 59
def prefixEnd_2953480 : Nat := 4983230072969 + 3 ^ 40 * 2953480 * 2
def baseEnd_2953480 : Nat := 1516554843441209729617199

theorem tailTrace_2953480 : CollatzResearch.WordTrace tailWord_2953480 prefixEnd_2953480 1516554843441209729617199 := by
  unfold tailWord_2953480
  simp only [CollatzResearch.WordTrace]
  refine ⟨53861132670026924535320947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71814843560035899380427929 53861132670026924535320947)
  ·
    refine ⟨80791699005040386802981421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53861132670026924535320947 80791699005040386802981421)
    ·
      refine ⟨30296887126890145051118033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80791699005040386802981421 30296887126890145051118033)
      ·
        refine ⟨22722665345167608788338525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30296887126890145051118033 22722665345167608788338525)
        ·
          refine ⟨8520999504437853295626947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22722665345167608788338525 8520999504437853295626947)
          ·
            refine ⟨12781499256656779943440421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520999504437853295626947 12781499256656779943440421)
            ·
              refine ⟨2396531110623146239395079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12781499256656779943440421 2396531110623146239395079)
              ·
                refine ⟨3594796665934719359092619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396531110623146239395079 3594796665934719359092619)
                ·
                  refine ⟨5392194998902079038638929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594796665934719359092619 5392194998902079038638929)
                  ·
                    refine ⟨4044146249176559278979197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5392194998902079038638929 4044146249176559278979197)
                    ·
                      refine ⟨1516554843441209729617199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4044146249176559278979197 1516554843441209729617199)
                      ·
                        rfl

theorem cell23_2953480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_2953480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953480 prefixEnd_2953480 := by exact prefixLift 2953480
  have htrace : WordTrace (prefixWord ++ tailWord_2953480) baseStart_2953480 baseEnd_2953480 := by
    simpa [prefixWord, tailWord_2953480, baseEnd_2953480] using wordTrace_append hprefix tailTrace_2953480
  have hstable : (prefixWord ++ tailWord_2953480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953480).length < 2 ^ (prefixWord ++ tailWord_2953480).sum := by decide
  have hdescent : baseEnd_2953480 < baseStart_2953480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953499 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_2953499 : Nat := 118140960795 + 2953499 * 2 ^ 59
def prefixEnd_2953499 : Nat := 4983230072969 + 3 ^ 40 * 2953499 * 2
def baseEnd_2953499 : Nat := 1516564599573645155279611

theorem tailTrace_2953499 : CollatzResearch.WordTrace tailWord_2953499 prefixEnd_2953499 1516564599573645155279611 := by
  unfold tailWord_2953499
  simp only [CollatzResearch.WordTrace]
  refine ⟨107722958326985015315583551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71815305551323343543722367 107722958326985015315583551)
  ·
    refine ⟨161584437490477522973375327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107722958326985015315583551 161584437490477522973375327)
    ·
      refine ⟨242376656235716284460062991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161584437490477522973375327 242376656235716284460062991)
      ·
        refine ⟨363564984353574426690094487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242376656235716284460062991 363564984353574426690094487)
        ·
          refine ⟨545347476530361640035141731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363564984353574426690094487 545347476530361640035141731)
          ·
            refine ⟨818021214795542460052712597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545347476530361640035141731 818021214795542460052712597)
            ·
              refine ⟨38344744443541052814970903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 818021214795542460052712597 38344744443541052814970903)
              ·
                refine ⟨57517116665311579222456355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38344744443541052814970903 57517116665311579222456355)
                ·
                  refine ⟨86275674997967368833684533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57517116665311579222456355 86275674997967368833684533)
                  ·
                    refine ⟨8088344531059440828157925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86275674997967368833684533 8088344531059440828157925)
                    ·
                      refine ⟨1516564599573645155279611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8088344531059440828157925 1516564599573645155279611)
                      ·
                        rfl

theorem cell23_2953499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_2953499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953499 prefixEnd_2953499 := by exact prefixLift 2953499
  have htrace : WordTrace (prefixWord ++ tailWord_2953499) baseStart_2953499 baseEnd_2953499 := by
    simpa [prefixWord, tailWord_2953499, baseEnd_2953499] using wordTrace_append hprefix tailTrace_2953499
  have hstable : (prefixWord ++ tailWord_2953499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953499).length < 2 ^ (prefixWord ++ tailWord_2953499).sum := by decide
  have hdescent : baseEnd_2953499 < baseStart_2953499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953517 : List Nat := [1, 5, 3, 1, 3, 1, 2, 7]
def baseStart_2953517 : Nat := 118140960795 + 2953517 * 2 ^ 59
def prefixEnd_2953517 : Nat := 4983230072969 + 3 ^ 40 * 2953517 * 2
def baseEnd_2953517 : Nat := 56169401563904669809427

theorem tailTrace_2953517 : CollatzResearch.WordTrace tailWord_2953517 prefixEnd_2953517 56169401563904669809427 := by
  unfold tailWord_2953517
  simp only [CollatzResearch.WordTrace]
  refine ⟨107723614840919804389738805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71815743227279869593159203 107723614840919804389738805)
  ·
    refine ⟨10099088891336231661538013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107723614840919804389738805 10099088891336231661538013)
    ·
      refine ⟨3787158334251086873076755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10099088891336231661538013 3787158334251086873076755)
      ·
        refine ⟨5680737501376630309615133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787158334251086873076755 5680737501376630309615133)
        ·
          refine ⟨2130276563016236366105675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5680737501376630309615133 2130276563016236366105675)
          ·
            refine ⟨3195414844524354549158513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130276563016236366105675 3195414844524354549158513)
            ·
              refine ⟨2396561133393265911868885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195414844524354549158513 2396561133393265911868885)
              ·
                refine ⟨56169401563904669809427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2396561133393265911868885 56169401563904669809427)
                ·
                  rfl

theorem cell23_2953517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 7].length) (baseStart_2953517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953517 prefixEnd_2953517 := by exact prefixLift 2953517
  have htrace : WordTrace (prefixWord ++ tailWord_2953517) baseStart_2953517 baseEnd_2953517 := by
    simpa [prefixWord, tailWord_2953517, baseEnd_2953517] using wordTrace_append hprefix tailTrace_2953517
  have hstable : (prefixWord ++ tailWord_2953517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953517).length < 2 ^ (prefixWord ++ tailWord_2953517).sum := by decide
  have hdescent : baseEnd_2953517 < baseStart_2953517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953539 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 9]
def baseStart_2953539 : Nat := 118140960795 + 2953539 * 2 ^ 59
def prefixEnd_2953539 : Nat := 4983230072969 + 3 ^ 40 * 2953539 * 2
def baseEnd_2953539 : Nat := 168509459866647222086603

theorem tailTrace_2953539 : CollatzResearch.WordTrace tailWord_2953539 prefixEnd_2953539 168509459866647222086603 := by
  unfold tailWord_2953539
  simp only [CollatzResearch.WordTrace]
  refine ⟨107724417246840102147039671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71816278164560068098026447 107724417246840102147039671)
  ·
    refine ⟨161586625870260153220559507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107724417246840102147039671 161586625870260153220559507)
    ·
      refine ⟨242379938805390229830839261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161586625870260153220559507 242379938805390229830839261)
      ·
        refine ⟨90892477052021336186564723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242379938805390229830839261 90892477052021336186564723)
        ·
          refine ⟨136338715578032004279847085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90892477052021336186564723 136338715578032004279847085)
          ·
            refine ⟨51127018341762001604942657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136338715578032004279847085 51127018341762001604942657)
            ·
              refine ⟨38345263756321501203706993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51127018341762001604942657 38345263756321501203706993)
              ·
                refine ⟨28758947817241125902780245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38345263756321501203706993 28758947817241125902780245)
                ·
                  refine ⟨168509459866647222086603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28758947817241125902780245 168509459866647222086603)
                  ·
                    rfl

theorem cell23_2953539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 9].length) (baseStart_2953539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953539 prefixEnd_2953539 := by exact prefixLift 2953539
  have htrace : WordTrace (prefixWord ++ tailWord_2953539) baseStart_2953539 baseEnd_2953539 := by
    simpa [prefixWord, tailWord_2953539, baseEnd_2953539] using wordTrace_append hprefix tailTrace_2953539
  have hstable : (prefixWord ++ tailWord_2953539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953539).length < 2 ^ (prefixWord ++ tailWord_2953539).sum := by decide
  have hdescent : baseEnd_2953539 < baseStart_2953539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953567 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 2, 2, 2]
def baseStart_2953567 : Nat := 118140960795 + 2953567 * 2 ^ 59
def prefixEnd_2953567 : Nat := 4983230072969 + 3 ^ 40 * 2953567 * 2
def baseEnd_2953567 : Nat := 1516599516258150889229299

theorem tailTrace_2953567 : CollatzResearch.WordTrace tailWord_2953567 prefixEnd_2953567 1516599516258150889229299 := by
  unfold tailWord_2953567
  simp only [CollatzResearch.WordTrace]
  refine ⟨107725438490738662929058955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71816958993825775286039303 107725438490738662929058955)
  ·
    refine ⟨161588157736107994393588433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107725438490738662929058955 161588157736107994393588433)
    ·
      refine ⟨121191118302080995795191325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161588157736107994393588433 121191118302080995795191325)
      ·
        refine ⟨45446669363280373423196747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121191118302080995795191325 45446669363280373423196747)
        ·
          refine ⟨68170004044920560134795121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45446669363280373423196747 68170004044920560134795121)
          ·
            refine ⟨51127503033690420101096341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68170004044920560134795121 51127503033690420101096341)
            ·
              refine ⟨2396601704704238442238891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51127503033690420101096341 2396601704704238442238891)
              ·
                refine ⟨3594902557056357663358337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396601704704238442238891 3594902557056357663358337)
                ·
                  refine ⟨2696176917792268247518753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594902557056357663358337 2696176917792268247518753)
                  ·
                    refine ⟨2022132688344201185639065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2696176917792268247518753 2022132688344201185639065)
                    ·
                      refine ⟨1516599516258150889229299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022132688344201185639065 1516599516258150889229299)
                      ·
                        rfl

theorem cell23_2953567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_2953567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953567 prefixEnd_2953567 := by exact prefixLift 2953567
  have htrace : WordTrace (prefixWord ++ tailWord_2953567) baseStart_2953567 baseEnd_2953567 := by
    simpa [prefixWord, tailWord_2953567, baseEnd_2953567] using wordTrace_append hprefix tailTrace_2953567
  have hstable : (prefixWord ++ tailWord_2953567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953567).length < 2 ^ (prefixWord ++ tailWord_2953567).sum := by decide
  have hdescent : baseEnd_2953567 < baseStart_2953567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953623 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_2953623 : Nat := 118140960795 + 2953623 * 2 ^ 59
def prefixEnd_2953623 : Nat := 4983230072969 + 3 ^ 40 * 2953623 * 2
def baseEnd_2953623 : Nat := 1516628271174802670129041

theorem tailTrace_2953623 : CollatzResearch.WordTrace tailWord_2953623 prefixEnd_2953623 1516628271174802670129041 := by
  unfold tailWord_2953623
  simp only [CollatzResearch.WordTrace]
  refine ⟨107727480978535784493097523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71818320652357189662065015 107727480978535784493097523)
  ·
    refine ⟨161591221467803676739646285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107727480978535784493097523 161591221467803676739646285)
    ·
      refine ⟨60596708050426378777367357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161591221467803676739646285 60596708050426378777367357)
      ·
        refine ⟨22723765518909892041512759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60596708050426378777367357 22723765518909892041512759)
        ·
          refine ⟨34085648278364838062269139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22723765518909892041512759 34085648278364838062269139)
          ·
            refine ⟨51128472417547257093403709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34085648278364838062269139 51128472417547257093403709)
            ·
              refine ⟨19173177156580221410026391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51128472417547257093403709 19173177156580221410026391)
              ·
                refine ⟨28759765734870332115039587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19173177156580221410026391 28759765734870332115039587)
                ·
                  refine ⟨43139648602305498172559381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28759765734870332115039587 43139648602305498172559381)
                  ·
                    refine ⟨2022171028233070226838721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43139648602305498172559381 2022171028233070226838721)
                    ·
                      refine ⟨1516628271174802670129041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022171028233070226838721 1516628271174802670129041)
                      ·
                        rfl

theorem cell23_2953623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_2953623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953623 prefixEnd_2953623 := by exact prefixLift 2953623
  have htrace : WordTrace (prefixWord ++ tailWord_2953623) baseStart_2953623 baseEnd_2953623 := by
    simpa [prefixWord, tailWord_2953623, baseEnd_2953623] using wordTrace_append hprefix tailTrace_2953623
  have hstable : (prefixWord ++ tailWord_2953623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953623).length < 2 ^ (prefixWord ++ tailWord_2953623).sum := by decide
  have hdescent : baseEnd_2953623 < baseStart_2953623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953640 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2953640 : Nat := 118140960795 + 2953640 * 2 ^ 59
def prefixEnd_2953640 : Nat := 4983230072969 + 3 ^ 40 * 2953640 * 2
def baseEnd_2953640 : Nat := 1516637000345929103616463

theorem tailTrace_2953640 : CollatzResearch.WordTrace tailWord_2953640 prefixEnd_2953640 1516637000345929103616463 := by
  unfold tailWord_2953640
  simp only [CollatzResearch.WordTrace]
  refine ⟨53864050509737098198233187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71818734012982797597644249 53864050509737098198233187)
  ·
    refine ⟨80796075764605647297349781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53864050509737098198233187 80796075764605647297349781)
    ·
      refine ⟨3787316051465889717063271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80796075764605647297349781 3787316051465889717063271)
      ·
        refine ⟨5680974077198834575594907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787316051465889717063271 5680974077198834575594907)
        ·
          refine ⟨8521461115798251863392361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680974077198834575594907 8521461115798251863392361)
          ·
            refine ⟨6391095836848688897544271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8521461115798251863392361 6391095836848688897544271)
            ·
              refine ⟨9586643755273033346316407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391095836848688897544271 9586643755273033346316407)
              ·
                refine ⟨14379965632909550019474611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9586643755273033346316407 14379965632909550019474611)
                ·
                  refine ⟨21569948449364325029211917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14379965632909550019474611 21569948449364325029211917)
                  ·
                    refine ⟨8088730668511621885954469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21569948449364325029211917 8088730668511621885954469)
                    ·
                      refine ⟨1516637000345929103616463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8088730668511621885954469 1516637000345929103616463)
                      ·
                        rfl

theorem cell23_2953640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2953640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953640 prefixEnd_2953640 := by exact prefixLift 2953640
  have htrace : WordTrace (prefixWord ++ tailWord_2953640) baseStart_2953640 baseEnd_2953640 := by
    simpa [prefixWord, tailWord_2953640, baseEnd_2953640] using wordTrace_append hprefix tailTrace_2953640
  have hstable : (prefixWord ++ tailWord_2953640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953640).length < 2 ^ (prefixWord ++ tailWord_2953640).sum := by decide
  have hdescent : baseEnd_2953640 < baseStart_2953640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953690 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_2953690 : Nat := 118140960795 + 2953690 * 2 ^ 59
def prefixEnd_2953690 : Nat := 4983230072969 + 3 ^ 40 * 2953690 * 2
def baseEnd_2953690 : Nat := 1516662674378653907991233

theorem tailTrace_2953690 : CollatzResearch.WordTrace tailWord_2953690 prefixEnd_2953690 1516662674378653907991233 := by
  unfold tailWord_2953690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932481167323263733946631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71819949779528703290524349 26932481167323263733946631)
  ·
    refine ⟨40398721750984895600919947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26932481167323263733946631 40398721750984895600919947)
    ·
      refine ⟨60598082626477343401379921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40398721750984895600919947 60598082626477343401379921)
      ·
        refine ⟨45448561969858007551034941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60598082626477343401379921 45448561969858007551034941)
        ·
          refine ⟨17043210738696752831638103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45448561969858007551034941 17043210738696752831638103)
          ·
            refine ⟨25564816108045129247457155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17043210738696752831638103 25564816108045129247457155)
            ·
              refine ⟨38347224162067693871185733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25564816108045129247457155 38347224162067693871185733)
              ·
                refine ⟨7190104530387692600847325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38347224162067693871185733 7190104530387692600847325)
                ·
                  refine ⟨2696289198895384725317747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7190104530387692600847325 2696289198895384725317747)
                  ·
                    refine ⟨4044433798343077087976621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696289198895384725317747 4044433798343077087976621)
                    ·
                      refine ⟨1516662674378653907991233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4044433798343077087976621 1516662674378653907991233)
                      ·
                        rfl

theorem cell23_2953690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_2953690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953690 prefixEnd_2953690 := by exact prefixLift 2953690
  have htrace : WordTrace (prefixWord ++ tailWord_2953690) baseStart_2953690 baseEnd_2953690 := by
    simpa [prefixWord, tailWord_2953690, baseEnd_2953690] using wordTrace_append hprefix tailTrace_2953690
  have hstable : (prefixWord ++ tailWord_2953690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953690).length < 2 ^ (prefixWord ++ tailWord_2953690).sum := by decide
  have hdescent : baseEnd_2953690 < baseStart_2953690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953701 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_2953701 : Nat := 118140960795 + 2953701 * 2 ^ 59
def prefixEnd_2953701 : Nat := 4983230072969 + 3 ^ 40 * 2953701 * 2
def baseEnd_2953701 : Nat := 505556107555284454984561

theorem tailTrace_2953701 : CollatzResearch.WordTrace tailWord_2953701 prefixEnd_2953701 505556107555284454984561 := by
  unfold tailWord_2953701
  simp only [CollatzResearch.WordTrace]
  refine ⟨107730325872253203814436957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71820217248168802542957971 107730325872253203814436957)
  ·
    refine ⟨40398872202094951430413859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107730325872253203814436957 40398872202094951430413859)
    ·
      refine ⟨60598308303142427145620789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40398872202094951430413859 60598308303142427145620789)
      ·
        refine ⟨5681091403419602544901949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60598308303142427145620789 5681091403419602544901949)
        ·
          refine ⟨2130409276282350954338231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5681091403419602544901949 2130409276282350954338231)
          ·
            refine ⟨3195613914423526431507347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130409276282350954338231 3195613914423526431507347)
            ·
              refine ⟨4793420871635289647261021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195613914423526431507347 4793420871635289647261021)
              ·
                refine ⟨1797532826863233617722883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4793420871635289647261021 1797532826863233617722883)
                ·
                  refine ⟨2696299240294850426584325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797532826863233617722883 2696299240294850426584325)
                  ·
                    refine ⟨505556107555284454984561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2696299240294850426584325 505556107555284454984561)
                    ·
                      rfl

theorem cell23_2953701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_2953701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953701 prefixEnd_2953701 := by exact prefixLift 2953701
  have htrace : WordTrace (prefixWord ++ tailWord_2953701) baseStart_2953701 baseEnd_2953701 := by
    simpa [prefixWord, tailWord_2953701, baseEnd_2953701] using wordTrace_append hprefix tailTrace_2953701
  have hstable : (prefixWord ++ tailWord_2953701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953701).length < 2 ^ (prefixWord ++ tailWord_2953701).sum := by decide
  have hdescent : baseEnd_2953701 < baseStart_2953701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953710 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2953710 : Nat := 118140960795 + 2953710 * 2 ^ 59
def prefixEnd_2953710 : Nat := 4983230072969 + 3 ^ 40 * 2953710 * 2
def baseEnd_2953710 : Nat := 505557647997247943247047

theorem tailTrace_2953710 : CollatzResearch.WordTrace tailWord_2953710 prefixEnd_2953710 505557647997247943247047 := by
  unfold tailWord_2953710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466331766152574793939323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71820436086147065567676389 13466331766152574793939323)
  ·
    refine ⟨20199497649228862190908985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466331766152574793939323 20199497649228862190908985)
    ·
      refine ⟨15149623236921646643181739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20199497649228862190908985 15149623236921646643181739)
      ·
        refine ⟨22724434855382469964772609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149623236921646643181739 22724434855382469964772609)
        ·
          refine ⟨17043326141536852473579457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22724434855382469964772609 17043326141536852473579457)
          ·
            refine ⟨12782494606152639355184593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17043326141536852473579457 12782494606152639355184593)
            ·
              refine ⟨9586870954614479516388445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12782494606152639355184593 9586870954614479516388445)
              ·
                refine ⟨3595076607980429818645667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9586870954614479516388445 3595076607980429818645667)
                ·
                  refine ⟨5392614911970644727968501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595076607980429818645667 5392614911970644727968501)
                  ·
                    refine ⟨505557647997247943247047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5392614911970644727968501 505557647997247943247047)
                    ·
                      rfl

theorem cell23_2953710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2953710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953710 prefixEnd_2953710 := by exact prefixLift 2953710
  have htrace : WordTrace (prefixWord ++ tailWord_2953710) baseStart_2953710 baseEnd_2953710 := by
    simpa [prefixWord, tailWord_2953710, baseEnd_2953710] using wordTrace_append hprefix tailTrace_2953710
  have hstable : (prefixWord ++ tailWord_2953710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953710).length < 2 ^ (prefixWord ++ tailWord_2953710).sum := by decide
  have hdescent : baseEnd_2953710 < baseStart_2953710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953733 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_2953733 : Nat := 118140960795 + 2953733 * 2 ^ 59
def prefixEnd_2953733 : Nat := 4983230072969 + 3 ^ 40 * 2953733 * 2
def baseEnd_2953733 : Nat := 1516684754046797239753535

theorem tailTrace_2953733 : CollatzResearch.WordTrace tailWord_2953733 prefixEnd_2953733 1516684754046797239753535 := by
  unfold tailWord_2953733
  simp only [CollatzResearch.WordTrace]
  refine ⟨107731493008137273279601853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71820995338758182186401235 107731493008137273279601853)
  ·
    refine ⟨40399309878051477479850695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107731493008137273279601853 40399309878051477479850695)
    ·
      refine ⟨60598964817077216219776043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40399309878051477479850695 60598964817077216219776043)
      ·
        refine ⟨90898447225615824329664065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60598964817077216219776043 90898447225615824329664065)
        ·
          refine ⟨68173835419211868247248049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90898447225615824329664065 68173835419211868247248049)
          ·
            refine ⟨51130376564408901185436037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68173835419211868247248049 51130376564408901185436037)
            ·
              refine ⟨9586945605826668972269257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51130376564408901185436037 9586945605826668972269257)
              ·
                refine ⟨7190209204370001729201943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9586945605826668972269257 7190209204370001729201943)
                ·
                  refine ⟨10785313806555002593802915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7190209204370001729201943 10785313806555002593802915)
                  ·
                    refine ⟨16177970709832503890704373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10785313806555002593802915 16177970709832503890704373)
                    ·
                      refine ⟨1516684754046797239753535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16177970709832503890704373 1516684754046797239753535)
                      ·
                        rfl

theorem cell23_2953733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_2953733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953733 prefixEnd_2953733 := by exact prefixLift 2953733
  have htrace : WordTrace (prefixWord ++ tailWord_2953733) baseStart_2953733 baseEnd_2953733 := by
    simpa [prefixWord, tailWord_2953733, baseEnd_2953733] using wordTrace_append hprefix tailTrace_2953733
  have hstable : (prefixWord ++ tailWord_2953733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953733).length < 2 ^ (prefixWord ++ tailWord_2953733).sum := by decide
  have hdescent : baseEnd_2953733 < baseStart_2953733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953774 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2953774 : Nat := 118140960795 + 2953774 * 2 ^ 59
def prefixEnd_2953774 : Nat := 4983230072969 + 3 ^ 40 * 2953774 * 2
def baseEnd_2953774 : Nat := 505568602251210526446949

theorem tailTrace_2953774 : CollatzResearch.WordTrace tailWord_2953774 prefixEnd_2953774 505568602251210526446949 := by
  unfold tailWord_2953774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466623550123592160230547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71821992267325824854562917 13466623550123592160230547)
  ·
    refine ⟨20199935325185388240345821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466623550123592160230547 20199935325185388240345821)
    ·
      refine ⟨7574975746944520590129683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20199935325185388240345821 7574975746944520590129683)
      ·
        refine ⟨11362463620416780885194525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7574975746944520590129683 11362463620416780885194525)
        ·
          refine ⟨4260923857656292831947947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11362463620416780885194525 4260923857656292831947947)
          ·
            refine ⟨6391385786484439247921921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260923857656292831947947 6391385786484439247921921)
            ·
              refine ⟨4793539339863329435941441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6391385786484439247921921 4793539339863329435941441)
              ·
                refine ⟨3595154504897497076956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793539339863329435941441 3595154504897497076956081)
                ·
                  refine ⟨2696365878673122807717061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595154504897497076956081 2696365878673122807717061)
                  ·
                    refine ⟨505568602251210526446949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2696365878673122807717061 505568602251210526446949)
                    ·
                      rfl

theorem cell23_2953774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2953774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953774 prefixEnd_2953774 := by exact prefixLift 2953774
  have htrace : WordTrace (prefixWord ++ tailWord_2953774) baseStart_2953774 baseEnd_2953774 := by
    simpa [prefixWord, tailWord_2953774, baseEnd_2953774] using wordTrace_append hprefix tailTrace_2953774
  have hstable : (prefixWord ++ tailWord_2953774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953774).length < 2 ^ (prefixWord ++ tailWord_2953774).sum := by decide
  have hdescent : baseEnd_2953774 < baseStart_2953774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953797 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_2953797 : Nat := 118140960795 + 2953797 * 2 ^ 59
def prefixEnd_2953797 : Nat := 4983230072969 + 3 ^ 40 * 2953797 * 2
def baseEnd_2953797 : Nat := 1516717616808684989353241

theorem tailTrace_2953797 : CollatzResearch.WordTrace tailWord_2953797 prefixEnd_2953797 1516717616808684989353241 := by
  unfold tailWord_2953797
  simp only [CollatzResearch.WordTrace]
  refine ⟨107733827279905412209931645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71822551519936941473287763 107733827279905412209931645)
  ·
    refine ⟨40400185229964529578724367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107733827279905412209931645 40400185229964529578724367)
    ·
      refine ⟨60600277844946794368086551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40400185229964529578724367 60600277844946794368086551)
      ·
        refine ⟨90900416767420191552129827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60600277844946794368086551 90900416767420191552129827)
        ·
          refine ⟨136350625151130287328194741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90900416767420191552129827 136350625151130287328194741)
          ·
            refine ⟨12782871107918464437018257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136350625151130287328194741 12782871107918464437018257)
            ·
              refine ⟨9587153330938848327763693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12782871107918464437018257 9587153330938848327763693)
              ·
                refine ⟨3595182499102068122911385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9587153330938848327763693 3595182499102068122911385)
                ·
                  refine ⟨2696386874326551092183539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595182499102068122911385 2696386874326551092183539)
                  ·
                    refine ⟨4044580311489826638275309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696386874326551092183539 4044580311489826638275309)
                    ·
                      refine ⟨1516717616808684989353241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4044580311489826638275309 1516717616808684989353241)
                      ·
                        rfl

theorem cell23_2953797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_2953797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953797 prefixEnd_2953797 := by exact prefixLift 2953797
  have htrace : WordTrace (prefixWord ++ tailWord_2953797) baseStart_2953797 baseEnd_2953797 := by
    simpa [prefixWord, tailWord_2953797, baseEnd_2953797] using wordTrace_append hprefix tailTrace_2953797
  have hstable : (prefixWord ++ tailWord_2953797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953797).length < 2 ^ (prefixWord ++ tailWord_2953797).sum := by decide
  have hdescent : baseEnd_2953797 < baseStart_2953797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953823 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_2953823 : Nat := 118140960795 + 2953823 * 2 ^ 59
def prefixEnd_2953823 : Nat := 4983230072969 + 3 ^ 40 * 2953823 * 2
def baseEnd_2953823 : Nat := 1516730967305701887628121

theorem tailTrace_2953823 : CollatzResearch.WordTrace tailWord_2953823 prefixEnd_2953823 1516730967305701887628121 := by
  unfold tailWord_2953823
  simp only [CollatzResearch.WordTrace]
  refine ⟨107734775577811218650378123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71823183718540812433585415 107734775577811218650378123)
  ·
    refine ⟨161602163366716827975567185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107734775577811218650378123 161602163366716827975567185)
    ·
      refine ⟨121201622525037620981675389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161602163366716827975567185 121201622525037620981675389)
      ·
        refine ⟨45450608446889107868128271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121201622525037620981675389 45450608446889107868128271)
        ·
          refine ⟨68175912670333661802192407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45450608446889107868128271 68175912670333661802192407)
          ·
            refine ⟨102263869005500492703288611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68175912670333661802192407 102263869005500492703288611)
            ·
              refine ⟨153395803508250739054932917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102263869005500492703288611 153395803508250739054932917)
              ·
                refine ⟨14380856578898506786399961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153395803508250739054932917 14380856578898506786399961)
                ·
                  refine ⟨10785642434173880089799971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14380856578898506786399961 10785642434173880089799971)
                  ·
                    refine ⟨16178463651260820134699957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10785642434173880089799971 16178463651260820134699957)
                    ·
                      refine ⟨1516730967305701887628121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16178463651260820134699957 1516730967305701887628121)
                      ·
                        rfl

theorem cell23_2953823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_2953823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953823 prefixEnd_2953823 := by exact prefixLift 2953823
  have htrace : WordTrace (prefixWord ++ tailWord_2953823) baseStart_2953823 baseEnd_2953823 := by
    simpa [prefixWord, tailWord_2953823, baseEnd_2953823] using wordTrace_append hprefix tailTrace_2953823
  have hstable : (prefixWord ++ tailWord_2953823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953823).length < 2 ^ (prefixWord ++ tailWord_2953823).sum := by decide
  have hdescent : baseEnd_2953823 < baseStart_2953823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953824 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2]
def baseStart_2953824 : Nat := 118140960795 + 2953824 * 2 ^ 59
def prefixEnd_2953824 : Nat := 4983230072969 + 3 ^ 40 * 2953824 * 2
def baseEnd_2953824 : Nat := 1516731480786356383715617

theorem tailTrace_2953824 : CollatzResearch.WordTrace tailWord_2953824 prefixEnd_2953824 1516731480786356383715617 := by
  unfold tailWord_2953824
  simp only [CollatzResearch.WordTrace]
  refine ⟨53867406025403797910582263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71823208033871730547443017 53867406025403797910582263)
  ·
    refine ⟨80801109038105696865873395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53867406025403797910582263 80801109038105696865873395)
    ·
      refine ⟨121201663557158545298810093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80801109038105696865873395 121201663557158545298810093)
      ·
        refine ⟨45450623833934454487053785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121201663557158545298810093 45450623833934454487053785)
        ·
          refine ⟨34087967875450840865290339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45450623833934454487053785 34087967875450840865290339)
          ·
            refine ⟨51131951813176261297935509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34087967875450840865290339 51131951813176261297935509)
            ·
              refine ⟨2396810241242637248340727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51131951813176261297935509 2396810241242637248340727)
              ·
                refine ⟨3595215361863955872511091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396810241242637248340727 3595215361863955872511091)
                ·
                  refine ⟨5392823042795933808766637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595215361863955872511091 5392823042795933808766637)
                  ·
                    refine ⟨2022308641048475178287489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5392823042795933808766637 2022308641048475178287489)
                    ·
                      refine ⟨1516731480786356383715617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022308641048475178287489 1516731480786356383715617)
                      ·
                        rfl

theorem cell23_2953824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_2953824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953824 prefixEnd_2953824 := by exact prefixLift 2953824
  have htrace : WordTrace (prefixWord ++ tailWord_2953824) baseStart_2953824 baseEnd_2953824 := by
    simpa [prefixWord, tailWord_2953824, baseEnd_2953824] using wordTrace_append hprefix tailTrace_2953824
  have hstable : (prefixWord ++ tailWord_2953824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953824).length < 2 ^ (prefixWord ++ tailWord_2953824).sum := by decide
  have hdescent : baseEnd_2953824 < baseStart_2953824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953860 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 7]
def baseStart_2953860 : Nat := 118140960795 + 2953860 * 2 ^ 59
def prefixEnd_2953860 : Nat := 4983230072969 + 3 ^ 40 * 2953860 * 2
def baseEnd_2953860 : Nat := 168527774009990915873939

theorem tailTrace_2953860 : CollatzResearch.WordTrace tailWord_2953860 prefixEnd_2953860 168527774009990915873939 := by
  unfold tailWord_2953860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53868062539338586984737517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71824083385784782646316689 53868062539338586984737517)
  ·
    refine ⟨20200523452251970119276569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53868062539338586984737517 20200523452251970119276569)
    ·
      refine ⟨15150392589188977589457427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20200523452251970119276569 15150392589188977589457427)
      ·
        refine ⟨22725588883783466384186141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15150392589188977589457427 22725588883783466384186141)
        ·
          refine ⟨8522095831418799894069803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22725588883783466384186141 8522095831418799894069803)
          ·
            refine ⟨12783143747128199841104705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522095831418799894069803 12783143747128199841104705)
            ·
              refine ⟨9587357810346149880828529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12783143747128199841104705 9587357810346149880828529)
              ·
                refine ⟨7190518357759612410621397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9587357810346149880828529 7190518357759612410621397)
                ·
                  refine ⟨168527774009990915873939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7190518357759612410621397 168527774009990915873939)
                  ·
                    rfl

theorem cell23_2953860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_2953860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953860 prefixEnd_2953860 := by exact prefixLift 2953860
  have htrace : WordTrace (prefixWord ++ tailWord_2953860) baseStart_2953860 baseEnd_2953860 := by
    simpa [prefixWord, tailWord_2953860, baseEnd_2953860] using wordTrace_append hprefix tailTrace_2953860
  have hstable : (prefixWord ++ tailWord_2953860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953860).length < 2 ^ (prefixWord ++ tailWord_2953860).sum := by decide
  have hdescent : baseEnd_2953860 < baseStart_2953860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953905 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2953905 : Nat := 118140960795 + 2953905 * 2 ^ 59
def prefixEnd_2953905 : Nat := 4983230072969 + 3 ^ 40 * 2953905 * 2
def baseEnd_2953905 : Nat := 1516773072719370566802745

theorem tailTrace_2953905 : CollatzResearch.WordTrace tailWord_2953905 prefixEnd_2953905 1516773072719370566802745 := by
  unfold tailWord_2953905
  simp only [CollatzResearch.WordTrace]
  refine ⟨107737766363514146654863169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71825177575676097769908779 107737766363514146654863169)
  ·
    refine ⟨80803324772635609991147377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107737766363514146654863169 80803324772635609991147377)
    ·
      refine ⟨60602493579476707493360533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80803324772635609991147377 60602493579476707493360533)
      ·
        refine ⟨2840741886537970663751275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60602493579476707493360533 2840741886537970663751275)
        ·
          refine ⟨4261112829806955995626913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840741886537970663751275 4261112829806955995626913)
          ·
            refine ⟨3195834622355216996720185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261112829806955995626913 3195834622355216996720185)
            ·
              refine ⟨2396875966766412747540139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195834622355216996720185 2396875966766412747540139)
              ·
                refine ⟨3595313950149619121310209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396875966766412747540139 3595313950149619121310209)
                ·
                  refine ⟨2696485462612214340982657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595313950149619121310209 2696485462612214340982657)
                  ·
                    refine ⟨2022364096959160755736993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2696485462612214340982657 2022364096959160755736993)
                    ·
                      refine ⟨1516773072719370566802745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022364096959160755736993 1516773072719370566802745)
                      ·
                        rfl

theorem cell23_2953905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2953905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2953905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2953905 prefixEnd_2953905 := by exact prefixLift 2953905
  have htrace : WordTrace (prefixWord ++ tailWord_2953905) baseStart_2953905 baseEnd_2953905 := by
    simpa [prefixWord, tailWord_2953905, baseEnd_2953905] using wordTrace_append hprefix tailTrace_2953905
  have hstable : (prefixWord ++ tailWord_2953905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953905).length < 2 ^ (prefixWord ++ tailWord_2953905).sum := by decide
  have hdescent : baseEnd_2953905 < baseStart_2953905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954034 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_2954034 : Nat := 118140960795 + 2954034 * 2 ^ 59
def prefixEnd_2954034 : Nat := 4983230072969 + 3 ^ 40 * 2954034 * 2
def baseEnd_2954034 : Nat := 1516839311723800562089651

theorem tailTrace_2954034 : CollatzResearch.WordTrace tailWord_2954034 prefixEnd_2954034 1516839311723800562089651 := by
  unfold tailWord_2954034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935617845011700421577289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71828314253364534457539437 26935617845011700421577289)
  ·
    refine ⟨20201713383758775316182967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26935617845011700421577289 20201713383758775316182967)
    ·
      refine ⟨30302570075638162974274451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20201713383758775316182967 30302570075638162974274451)
      ·
        refine ⟨45453855113457244461411677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30302570075638162974274451 45453855113457244461411677)
        ·
          refine ⟨17045195667546466673029379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45453855113457244461411677 17045195667546466673029379)
          ·
            refine ⟨25567793501319700009544069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17045195667546466673029379 25567793501319700009544069)
            ·
              refine ⟨4793961281497443751789513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25567793501319700009544069 4793961281497443751789513)
              ·
                refine ⟨3595470961123082813842135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793961281497443751789513 3595470961123082813842135)
                ·
                  refine ⟨5393206441684624220763203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595470961123082813842135 5393206441684624220763203)
                  ·
                    refine ⟨8089809662526936331144805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393206441684624220763203 8089809662526936331144805)
                    ·
                      refine ⟨1516839311723800562089651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8089809662526936331144805 1516839311723800562089651)
                      ·
                        rfl

theorem cell23_2954034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_2954034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954034 prefixEnd_2954034 := by exact prefixLift 2954034
  have htrace : WordTrace (prefixWord ++ tailWord_2954034) baseStart_2954034 baseEnd_2954034 := by
    simpa [prefixWord, tailWord_2954034, baseEnd_2954034] using wordTrace_append hprefix tailTrace_2954034
  have hstable : (prefixWord ++ tailWord_2954034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954034).length < 2 ^ (prefixWord ++ tailWord_2954034).sum := by decide
  have hdescent : baseEnd_2954034 < baseStart_2954034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954040 : List Nat := [2, 1, 2, 1, 3, 2, 3, 9]
def baseStart_2954040 : Nat := 118140960795 + 2954040 * 2 ^ 59
def prefixEnd_2954040 : Nat := 4983230072969 + 3 ^ 40 * 2954040 * 2
def baseEnd_2954040 : Nat := 56179347874360279207949

theorem tailTrace_2954040 : CollatzResearch.WordTrace tailWord_2954040 prefixEnd_2954040 56179347874360279207949 := by
  unfold tailWord_2954040
  simp only [CollatzResearch.WordTrace]
  refine ⟨53871345109012532355513787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71828460145350043140685049 53871345109012532355513787)
  ·
    refine ⟨80807017663518798533270681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53871345109012532355513787 80807017663518798533270681)
    ·
      refine ⟨60605263247639098899953011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80807017663518798533270681 60605263247639098899953011)
      ·
        refine ⟨90907894871458648349929517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60605263247639098899953011 90907894871458648349929517)
        ·
          refine ⟨34090460576796993131223569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90907894871458648349929517 34090460576796993131223569)
          ·
            refine ⟨25567845432597744848417677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34090460576796993131223569 25567845432597744848417677)
            ·
              refine ⟨9587942037224154318156629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25567845432597744848417677 9587942037224154318156629)
              ·
                refine ⟨56179347874360279207949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9587942037224154318156629 56179347874360279207949)
                ·
                  rfl

theorem cell23_2954040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 9].length) (baseStart_2954040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954040 prefixEnd_2954040 := by exact prefixLift 2954040
  have htrace : WordTrace (prefixWord ++ tailWord_2954040) baseStart_2954040 baseEnd_2954040 := by
    simpa [prefixWord, tailWord_2954040, baseEnd_2954040] using wordTrace_append hprefix tailTrace_2954040
  have hstable : (prefixWord ++ tailWord_2954040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954040).length < 2 ^ (prefixWord ++ tailWord_2954040).sum := by decide
  have hdescent : baseEnd_2954040 < baseStart_2954040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954045 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2954045 : Nat := 118140960795 + 2954045 * 2 ^ 59
def prefixEnd_2954045 : Nat := 4983230072969 + 3 ^ 40 * 2954045 * 2
def baseEnd_2954045 : Nat := 1516844960011000019052101

theorem tailTrace_2954045 : CollatzResearch.WordTrace tailWord_2954045 prefixEnd_2954045 1516844960011000019052101 := by
  unfold tailWord_2954045
  simp only [CollatzResearch.WordTrace]
  refine ⟨107742872583006950564959589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71828581722004633709973059 107742872583006950564959589)
  ·
    refine ⟨20201788609313803230929923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107742872583006950564959589 20201788609313803230929923)
    ·
      refine ⟨30302682913970704846394885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20201788609313803230929923 30302682913970704846394885)
      ·
        refine ⟨5681753046369507158699041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30302682913970704846394885 5681753046369507158699041)
        ·
          refine ⟨4261314784777130369024281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5681753046369507158699041 4261314784777130369024281)
          ·
            refine ⟨3195986088582847776768211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261314784777130369024281 3195986088582847776768211)
            ·
              refine ⟨4793979132874271665152317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195986088582847776768211 4793979132874271665152317)
              ·
                refine ⟨1797742174827851874432119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4793979132874271665152317 1797742174827851874432119)
                ·
                  refine ⟨2696613262241777811648179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797742174827851874432119 2696613262241777811648179)
                  ·
                    refine ⟨4044919893362666717472269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696613262241777811648179 4044919893362666717472269)
                    ·
                      refine ⟨1516844960011000019052101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4044919893362666717472269 1516844960011000019052101)
                      ·
                        rfl

theorem cell23_2954045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2954045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954045 prefixEnd_2954045 := by exact prefixLift 2954045
  have htrace : WordTrace (prefixWord ++ tailWord_2954045) baseStart_2954045 baseEnd_2954045 := by
    simpa [prefixWord, tailWord_2954045, baseEnd_2954045] using wordTrace_append hprefix tailTrace_2954045
  have hstable : (prefixWord ++ tailWord_2954045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954045).length < 2 ^ (prefixWord ++ tailWord_2954045).sum := by decide
  have hdescent : baseEnd_2954045 < baseStart_2954045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954141 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_2954141 : Nat := 118140960795 + 2954141 * 2 ^ 59
def prefixEnd_2954141 : Nat := 4983230072969 + 3 ^ 40 * 2954141 * 2
def baseEnd_2954141 : Nat := 1516894254153831643451659

theorem tailTrace_2954141 : CollatzResearch.WordTrace tailWord_2954141 prefixEnd_2954141 1516894254153831643451659 := by
  unfold tailWord_2954141
  simp only [CollatzResearch.WordTrace]
  refine ⟨107746373990659158960454277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71830915993772772640302851 107746373990659158960454277)
  ·
    refine ⟨20202445123248592305085177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107746373990659158960454277 20202445123248592305085177)
    ·
      refine ⟨15151833842436444228813883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20202445123248592305085177 15151833842436444228813883)
      ·
        refine ⟨22727750763654666343220825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15151833842436444228813883 22727750763654666343220825)
        ·
          refine ⟨17045813072740999757415619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22727750763654666343220825 17045813072740999757415619)
          ·
            refine ⟨25568719609111499636123429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17045813072740999757415619 25568719609111499636123429)
            ·
              refine ⟨4794134926708406181773143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25568719609111499636123429 4794134926708406181773143)
              ·
                refine ⟨7191202390062609272659715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794134926708406181773143 7191202390062609272659715)
                ·
                  refine ⟨10786803585093913908989573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7191202390062609272659715 10786803585093913908989573)
                  ·
                    refine ⟨2022525672205108857935545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10786803585093913908989573 2022525672205108857935545)
                    ·
                      refine ⟨1516894254153831643451659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022525672205108857935545 1516894254153831643451659)
                      ·
                        rfl

theorem cell23_2954141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_2954141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954141 prefixEnd_2954141 := by exact prefixLift 2954141
  have htrace : WordTrace (prefixWord ++ tailWord_2954141) baseStart_2954141 baseEnd_2954141 := by
    simpa [prefixWord, tailWord_2954141, baseEnd_2954141] using wordTrace_append hprefix tailTrace_2954141
  have hstable : (prefixWord ++ tailWord_2954141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954141).length < 2 ^ (prefixWord ++ tailWord_2954141).sum := by decide
  have hdescent : baseEnd_2954141 < baseStart_2954141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954174 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2954174 : Nat := 118140960795 + 2954174 * 2 ^ 59
def prefixEnd_2954174 : Nat := 4983230072969 + 3 ^ 40 * 2954174 * 2
def baseEnd_2954174 : Nat := 1516911199015430014339007

theorem tailTrace_2954174 : CollatzResearch.WordTrace tailWord_2954174 prefixEnd_2954174 1516911199015430014339007 := by
  unfold tailWord_2954174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468447199942450699550697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71831718399693070397603717 13468447199942450699550697)
  ·
    refine ⟨10101335399956838024663023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13468447199942450699550697 10101335399956838024663023)
    ·
      refine ⟨15152003099935257036994535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101335399956838024663023 15152003099935257036994535)
      ·
        refine ⟨22728004649902885555491803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15152003099935257036994535 22728004649902885555491803)
        ·
          refine ⟨34092006974854328333237705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22728004649902885555491803 34092006974854328333237705)
          ·
            refine ⟨25569005231140746249928279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34092006974854328333237705 25569005231140746249928279)
            ·
              refine ⟨38353507846711119374892419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25569005231140746249928279 38353507846711119374892419)
              ·
                refine ⟨57530261770066679062338629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38353507846711119374892419 57530261770066679062338629)
                ·
                  refine ⟨10786924081887502324188493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57530261770066679062338629 10786924081887502324188493)
                  ·
                    refine ⟨4045096530707813371570685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10786924081887502324188493 4045096530707813371570685)
                    ·
                      refine ⟨1516911199015430014339007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4045096530707813371570685 1516911199015430014339007)
                      ·
                        rfl

theorem cell23_2954174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2954174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954174 prefixEnd_2954174 := by exact prefixLift 2954174
  have htrace : WordTrace (prefixWord ++ tailWord_2954174) baseStart_2954174 baseEnd_2954174 := by
    simpa [prefixWord, tailWord_2954174, baseEnd_2954174] using wordTrace_append hprefix tailTrace_2954174
  have hstable : (prefixWord ++ tailWord_2954174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954174).length < 2 ^ (prefixWord ++ tailWord_2954174).sum := by decide
  have hdescent : baseEnd_2954174 < baseStart_2954174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954194 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2954194 : Nat := 118140960795 + 2954194 * 2 ^ 59
def prefixEnd_2954194 : Nat := 4983230072969 + 3 ^ 40 * 2954194 * 2
def baseEnd_2954194 : Nat := 505640489542839978696305

theorem tailTrace_2954194 : CollatzResearch.WordTrace tailWord_2954194 prefixEnd_2954194 505640489542839978696305 := by
  unfold tailWord_2954194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26937076764866787253033409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71832204706311432674755757 26937076764866787253033409)
  ·
    refine ⟨20202807573650090439775057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26937076764866787253033409 20202807573650090439775057)
    ·
      refine ⟨15152105680237567829831293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20202807573650090439775057 15152105680237567829831293)
      ·
        refine ⟨5682039630089087936186735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15152105680237567829831293 5682039630089087936186735)
        ·
          refine ⟨8523059445133631904280103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682039630089087936186735 8523059445133631904280103)
          ·
            refine ⟨12784589167700447856420155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523059445133631904280103 12784589167700447856420155)
            ·
              refine ⟨19176883751550671784630233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12784589167700447856420155 19176883751550671784630233)
              ·
                refine ⟨14382662813663003838472675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19176883751550671784630233 14382662813663003838472675)
                ·
                  refine ⟨21573994220494505757709013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14382662813663003838472675 21573994220494505757709013)
                  ·
                    refine ⟨505640489542839978696305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21573994220494505757709013 505640489542839978696305)
                    ·
                      rfl

theorem cell23_2954194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2954194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954194 prefixEnd_2954194 := by exact prefixLift 2954194
  have htrace : WordTrace (prefixWord ++ tailWord_2954194) baseStart_2954194 baseEnd_2954194 := by
    simpa [prefixWord, tailWord_2954194, baseEnd_2954194] using wordTrace_append hprefix tailTrace_2954194
  have hstable : (prefixWord ++ tailWord_2954194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954194).length < 2 ^ (prefixWord ++ tailWord_2954194).sum := by decide
  have hdescent : baseEnd_2954194 < baseStart_2954194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954241 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2954241 : Nat := 118140960795 + 2954241 * 2 ^ 59
def prefixEnd_2954241 : Nat := 4983230072969 + 3 ^ 40 * 2954241 * 2
def baseEnd_2954241 : Nat := 505648534073093750733733

theorem tailTrace_2954241 : CollatzResearch.WordTrace tailWord_2954241 prefixEnd_2954241 505648534073093750733733 := by
  unfold tailWord_2954241
  simp only [CollatzResearch.WordTrace]
  refine ⟨107750021290296876039094577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71833347526864584026063051 107750021290296876039094577)
  ·
    refine ⟨80812515967722657029320933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107750021290296876039094577 80812515967722657029320933)
    ·
      refine ⟨15152346743947998192997675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80812515967722657029320933 15152346743947998192997675)
      ·
        refine ⟨22728520115921997289496513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15152346743947998192997675 22728520115921997289496513)
        ·
          refine ⟨17046390086941497967122385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22728520115921997289496513 17046390086941497967122385)
          ·
            refine ⟨12784792565206123475341789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17046390086941497967122385 12784792565206123475341789)
            ·
              refine ⟨4794297211952296303253171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12784792565206123475341789 4794297211952296303253171)
              ·
                refine ⟨7191445817928444454879757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794297211952296303253171 7191445817928444454879757)
                ·
                  refine ⟨2696792181723166670579909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7191445817928444454879757 2696792181723166670579909)
                  ·
                    refine ⟨505648534073093750733733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2696792181723166670579909 505648534073093750733733)
                    ·
                      rfl

theorem cell23_2954241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2954241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954241 prefixEnd_2954241 := by exact prefixLift 2954241
  have htrace : WordTrace (prefixWord ++ tailWord_2954241) baseStart_2954241 baseEnd_2954241 := by
    simpa [prefixWord, tailWord_2954241, baseEnd_2954241] using wordTrace_append hprefix tailTrace_2954241
  have hstable : (prefixWord ++ tailWord_2954241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954241).length < 2 ^ (prefixWord ++ tailWord_2954241).sum := by decide
  have hdescent : baseEnd_2954241 < baseStart_2954241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954257 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2954257 : Nat := 118140960795 + 2954257 * 2 ^ 59
def prefixEnd_2954257 : Nat := 4983230072969 + 3 ^ 40 * 2954257 * 2
def baseEnd_2954257 : Nat := 1516953817909753189601125

theorem tailTrace_2954257 : CollatzResearch.WordTrace tailWord_2954257 prefixEnd_2954257 1516953817909753189601125 := by
  unfold tailWord_2954257
  simp only [CollatzResearch.WordTrace]
  refine ⟨107750604858238910771677025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71833736572159273847784683 107750604858238910771677025)
  ·
    refine ⟨80812953643679183078757769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107750604858238910771677025 80812953643679183078757769)
    ·
      refine ⟨60609715232759387309068327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80812953643679183078757769 60609715232759387309068327)
      ·
        refine ⟨90914572849139080963602491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60609715232759387309068327 90914572849139080963602491)
        ·
          refine ⟨136371859273708621445403737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90914572849139080963602491 136371859273708621445403737)
          ·
            refine ⟨102278894455281466084052803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136371859273708621445403737 102278894455281466084052803)
            ·
              refine ⟨153418341682922199126079205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102278894455281466084052803 153418341682922199126079205)
              ·
                refine ⟨28765939065547912336139851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153418341682922199126079205 28765939065547912336139851)
                ·
                  refine ⟨43148908598321868504209777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28765939065547912336139851 43148908598321868504209777)
                  ·
                    refine ⟨32361681448741401378157333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43148908598321868504209777 32361681448741401378157333)
                    ·
                      refine ⟨1516953817909753189601125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32361681448741401378157333 1516953817909753189601125)
                      ·
                        rfl

theorem cell23_2954257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2954257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954257 prefixEnd_2954257 := by exact prefixLift 2954257
  have htrace : WordTrace (prefixWord ++ tailWord_2954257) baseStart_2954257 baseEnd_2954257 := by
    simpa [prefixWord, tailWord_2954257, baseEnd_2954257] using wordTrace_append hprefix tailTrace_2954257
  have hstable : (prefixWord ++ tailWord_2954257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954257).length < 2 ^ (prefixWord ++ tailWord_2954257).sum := by decide
  have hdescent : baseEnd_2954257 < baseStart_2954257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954268 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2954268 : Nat := 118140960795 + 2954268 * 2 ^ 59
def prefixEnd_2954268 : Nat := 4983230072969 + 3 ^ 40 * 2954268 * 2
def baseEnd_2954268 : Nat := 1516959466196952646563575

theorem tailTrace_2954268 : CollatzResearch.WordTrace tailWord_2954268 prefixEnd_2954268 1516959466196952646563575 := by
  unfold tailWord_2954268
  simp only [CollatzResearch.WordTrace]
  refine ⟨53875503030599529825163729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71834004040799373100218305 53875503030599529825163729)
  ·
    refine ⟨40406627272949647368872797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53875503030599529825163729 40406627272949647368872797)
    ·
      refine ⟨15152485227356117763327299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40406627272949647368872797 15152485227356117763327299)
      ·
        refine ⟨22728727841034176644990949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15152485227356117763327299 22728727841034176644990949)
        ·
          refine ⟨4261636470193908120935803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22728727841034176644990949 4261636470193908120935803)
          ·
            refine ⟨6392454705290862181403705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261636470193908120935803 6392454705290862181403705)
            ·
              refine ⟨4794341028968146636052779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6392454705290862181403705 4794341028968146636052779)
              ·
                refine ⟨7191511543452219954079169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794341028968146636052779 7191511543452219954079169)
                ·
                  refine ⟨5393633657589164965559377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7191511543452219954079169 5393633657589164965559377)
                  ·
                    refine ⟨4045225243191873724169533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393633657589164965559377 4045225243191873724169533)
                    ·
                      refine ⟨1516959466196952646563575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4045225243191873724169533 1516959466196952646563575)
                      ·
                        rfl

theorem cell23_2954268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2954268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954268 prefixEnd_2954268 := by exact prefixLift 2954268
  have htrace : WordTrace (prefixWord ++ tailWord_2954268) baseStart_2954268 baseEnd_2954268 := by
    simpa [prefixWord, tailWord_2954268, baseEnd_2954268] using wordTrace_append hprefix tailTrace_2954268
  have hstable : (prefixWord ++ tailWord_2954268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954268).length < 2 ^ (prefixWord ++ tailWord_2954268).sum := by decide
  have hdescent : baseEnd_2954268 < baseStart_2954268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954292 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2954292 : Nat := 118140960795 + 2954292 * 2 ^ 59
def prefixEnd_2954292 : Nat := 4983230072969 + 3 ^ 40 * 2954292 * 2
def baseEnd_2954292 : Nat := 505657263244220184221155

theorem tailTrace_2954292 : CollatzResearch.WordTrace tailWord_2954292 prefixEnd_2954292 505657263244220184221155 := by
  unfold tailWord_2954292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53875940706556055874600565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71834587608741407832800753 53875940706556055874600565)
  ·
    refine ⟨5050869441239630238243803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53875940706556055874600565 5050869441239630238243803)
    ·
      refine ⟨7576304161859445357365705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050869441239630238243803 7576304161859445357365705)
      ·
        refine ⟨5682228121394584018024279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7576304161859445357365705 5682228121394584018024279)
        ·
          refine ⟨8523342182091876027036419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682228121394584018024279 8523342182091876027036419)
          ·
            refine ⟨12785013273137814040554629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523342182091876027036419 12785013273137814040554629)
            ·
              refine ⟨2397189988713340132603993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12785013273137814040554629 2397189988713340132603993)
              ·
                refine ⟨1797892491535005099452995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397189988713340132603993 1797892491535005099452995)
                ·
                  refine ⟨2696838737302507649179493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797892491535005099452995 2696838737302507649179493)
                  ·
                    refine ⟨505657263244220184221155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2696838737302507649179493 505657263244220184221155)
                    ·
                      rfl

theorem cell23_2954292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2954292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954292 prefixEnd_2954292 := by exact prefixLift 2954292
  have htrace : WordTrace (prefixWord ++ tailWord_2954292) baseStart_2954292 baseEnd_2954292 := by
    simpa [prefixWord, tailWord_2954292, baseEnd_2954292] using wordTrace_append hprefix tailTrace_2954292
  have hstable : (prefixWord ++ tailWord_2954292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954292).length < 2 ^ (prefixWord ++ tailWord_2954292).sum := by decide
  have hdescent : baseEnd_2954292 < baseStart_2954292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954304 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_2954304 : Nat := 118140960795 + 2954304 * 2 ^ 59
def prefixEnd_2954304 : Nat := 4983230072969 + 3 ^ 40 * 2954304 * 2
def baseEnd_2954304 : Nat := 1516977951500514505713409

theorem tailTrace_2954304 : CollatzResearch.WordTrace tailWord_2954304 prefixEnd_2954304 1516977951500514505713409 := by
  unfold tailWord_2954304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53876159544534318899318983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71834879392712425199091977 53876159544534318899318983)
  ·
    refine ⟨80814239316801478348978475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53876159544534318899318983 80814239316801478348978475)
    ·
      refine ⟨121221358975202217523467713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80814239316801478348978475 121221358975202217523467713)
      ·
        refine ⟨90916019231401663142600785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121221358975202217523467713 90916019231401663142600785)
        ·
          refine ⟨68187014423551247356950589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90916019231401663142600785 68187014423551247356950589)
          ·
            refine ⟨25570130408831717758856471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68187014423551247356950589 25570130408831717758856471)
            ·
              refine ⟨38355195613247576638284707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25570130408831717758856471 38355195613247576638284707)
              ·
                refine ⟨57532793419871364957427061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38355195613247576638284707 57532793419871364957427061)
                ·
                  refine ⟨5393699383112940464758787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57532793419871364957427061 5393699383112940464758787)
                  ·
                    refine ⟨8090549074669410697138181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393699383112940464758787 8090549074669410697138181)
                    ·
                      refine ⟨1516977951500514505713409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8090549074669410697138181 1516977951500514505713409)
                      ·
                        rfl

theorem cell23_2954304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_2954304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954304 prefixEnd_2954304 := by exact prefixLift 2954304
  have htrace : WordTrace (prefixWord ++ tailWord_2954304) baseStart_2954304 baseEnd_2954304 := by
    simpa [prefixWord, tailWord_2954304, baseEnd_2954304] using wordTrace_append hprefix tailTrace_2954304
  have hstable : (prefixWord ++ tailWord_2954304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954304).length < 2 ^ (prefixWord ++ tailWord_2954304).sum := by decide
  have hdescent : baseEnd_2954304 < baseStart_2954304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954314 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_2954314 : Nat := 118140960795 + 2954314 * 2 ^ 59
def prefixEnd_2954314 : Nat := 4983230072969 + 3 ^ 40 * 2954314 * 2
def baseEnd_2954314 : Nat := 505661028769019822196121

theorem tailTrace_2954314 : CollatzResearch.WordTrace tailWord_2954314 prefixEnd_2954314 505661028769019822196121 := by
  unfold tailWord_2954314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938170954758102376625499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71835122546021606337667997 26938170954758102376625499)
  ·
    refine ⟨40407256432137153564938249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26938170954758102376625499 40407256432137153564938249)
    ·
      refine ⟨30305442324102865173703687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40407256432137153564938249 30305442324102865173703687)
      ·
        refine ⟨45458163486154297760555531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30305442324102865173703687 45458163486154297760555531)
        ·
          refine ⟨68187245229231446640833297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45458163486154297760555531 68187245229231446640833297)
          ·
            refine ⟨51140433921923584980624973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68187245229231446640833297 51140433921923584980624973)
            ·
              refine ⟨19177662720721344367734365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51140433921923584980624973 19177662720721344367734365)
              ·
                refine ⟨7191623520270504137900387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19177662720721344367734365 7191623520270504137900387)
                ·
                  refine ⟨10787435280405756206850581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7191623520270504137900387 10787435280405756206850581)
                  ·
                    refine ⟨505661028769019822196121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10787435280405756206850581 505661028769019822196121)
                    ·
                      rfl

theorem cell23_2954314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_2954314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954314 prefixEnd_2954314 := by exact prefixLift 2954314
  have htrace : WordTrace (prefixWord ++ tailWord_2954314) baseStart_2954314 baseEnd_2954314 := by
    simpa [prefixWord, tailWord_2954314, baseEnd_2954314] using wordTrace_append hprefix tailTrace_2954314
  have hstable : (prefixWord ++ tailWord_2954314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954314).length < 2 ^ (prefixWord ++ tailWord_2954314).sum := by decide
  have hdescent : baseEnd_2954314 < baseStart_2954314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954432 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2]
def baseStart_2954432 : Nat := 118140960795 + 2954432 * 2 ^ 59
def prefixEnd_2954432 : Nat := 4983230072969 + 3 ^ 40 * 2954432 * 2
def baseEnd_2954432 : Nat := 1517043677024290004912821

theorem tailTrace_2954432 : CollatzResearch.WordTrace tailWord_2954432 prefixEnd_2954432 1517043677024290004912821 := by
  unfold tailWord_2954432
  simp only [CollatzResearch.WordTrace]
  refine ⟨53878493816302457829648775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71837991755069943772865033 53878493816302457829648775)
  ·
    refine ⟨80817740724453686744473163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53878493816302457829648775 80817740724453686744473163)
    ·
      refine ⟨121226611086680530116709745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80817740724453686744473163 121226611086680530116709745)
      ·
        refine ⟨90919958315010397587532309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121226611086680530116709745 90919958315010397587532309)
        ·
          refine ⟨4261873046016112386915577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90919958315010397587532309 4261873046016112386915577)
          ·
            refine ⟨3196404784512084290186683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261873046016112386915577 3196404784512084290186683)
            ·
              refine ⟨4794607176768126435280025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196404784512084290186683 4794607176768126435280025)
              ·
                refine ⟨3595955382576094826460019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4794607176768126435280025 3595955382576094826460019)
                ·
                  refine ⟨5393933073864142239690029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595955382576094826460019 5393933073864142239690029)
                  ·
                    refine ⟨2022724902699053339883761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5393933073864142239690029 2022724902699053339883761)
                    ·
                      refine ⟨1517043677024290004912821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022724902699053339883761 1517043677024290004912821)
                      ·
                        rfl

theorem cell23_2954432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_2954432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954432 prefixEnd_2954432 := by exact prefixLift 2954432
  have htrace : WordTrace (prefixWord ++ tailWord_2954432) baseStart_2954432 baseEnd_2954432 := by
    simpa [prefixWord, tailWord_2954432, baseEnd_2954432] using wordTrace_append hprefix tailTrace_2954432
  have hstable : (prefixWord ++ tailWord_2954432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954432).length < 2 ^ (prefixWord ++ tailWord_2954432).sum := by decide
  have hdescent : baseEnd_2954432 < baseStart_2954432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954501 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_2954501 : Nat := 118140960795 + 2954501 * 2 ^ 59
def prefixEnd_2954501 : Nat := 4983230072969 + 3 ^ 40 * 2954501 * 2
def baseEnd_2954501 : Nat := 1517079107189450234950003

theorem tailTrace_2954501 : CollatzResearch.WordTrace tailWord_2954501 prefixEnd_2954501 1517079107189450234950003 := by
  unfold tailWord_2954501
  simp only [CollatzResearch.WordTrace]
  refine ⟨107759504269354940443559357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71839669512903293629039571 107759504269354940443559357)
  ·
    refine ⟨40409814101008102666334759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107759504269354940443559357 40409814101008102666334759)
    ·
      refine ⟨60614721151512153999502139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40409814101008102666334759 60614721151512153999502139)
      ·
        refine ⟨90922081727268230999253209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60614721151512153999502139 90922081727268230999253209)
        ·
          refine ⟨68191561295451173249439907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90922081727268230999253209 68191561295451173249439907)
          ·
            refine ⟨102287341943176759874159861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68191561295451173249439907 102287341943176759874159861)
            ·
              refine ⟨9589438307172821238202487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102287341943176759874159861 9589438307172821238202487)
              ·
                refine ⟨14384157460759231857303731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589438307172821238202487 14384157460759231857303731)
                ·
                  refine ⟨21576236191138847785955597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14384157460759231857303731 21576236191138847785955597)
                  ·
                    refine ⟨8091088571677067919733349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21576236191138847785955597 8091088571677067919733349)
                    ·
                      refine ⟨1517079107189450234950003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8091088571677067919733349 1517079107189450234950003)
                      ·
                        rfl

theorem cell23_2954501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_2954501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954501 prefixEnd_2954501 := by exact prefixLift 2954501
  have htrace : WordTrace (prefixWord ++ tailWord_2954501) baseStart_2954501 baseEnd_2954501 := by
    simpa [prefixWord, tailWord_2954501, baseEnd_2954501] using wordTrace_append hprefix tailTrace_2954501
  have hstable : (prefixWord ++ tailWord_2954501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954501).length < 2 ^ (prefixWord ++ tailWord_2954501).sum := by decide
  have hdescent : baseEnd_2954501 < baseStart_2954501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954548 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2954548 : Nat := 118140960795 + 2954548 * 2 ^ 59
def prefixEnd_2954548 : Nat := 4983230072969 + 3 ^ 40 * 2954548 * 2
def baseEnd_2954548 : Nat := 1517103240780211551062287

theorem tailTrace_2954548 : CollatzResearch.WordTrace tailWord_2954548 prefixEnd_2954548 1517103240780211551062287 := by
  unfold tailWord_2954548
  simp only [CollatzResearch.WordTrace]
  refine ⟨53880609250092333735260149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71840812333456444980346865 53880609250092333735260149)
  ·
    refine ⟨5051307117196156287680639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53880609250092333735260149 5051307117196156287680639)
    ·
      refine ⟨7576960675794234431520959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5051307117196156287680639 7576960675794234431520959)
      ·
        refine ⟨11365441013691351647281439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576960675794234431520959 11365441013691351647281439)
        ·
          refine ⟨17048161520537027470922159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365441013691351647281439 17048161520537027470922159)
          ·
            refine ⟨25572242280805541206383239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17048161520537027470922159 25572242280805541206383239)
            ·
              refine ⟨38358363421208311809574859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25572242280805541206383239 38358363421208311809574859)
              ·
                refine ⟨57537545131812467714362289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38358363421208311809574859 57537545131812467714362289)
                ·
                  refine ⟨43153158848859350785771717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57537545131812467714362289 43153158848859350785771717)
                  ·
                    refine ⟨8091217284161128272332197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43153158848859350785771717 8091217284161128272332197)
                    ·
                      refine ⟨1517103240780211551062287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8091217284161128272332197 1517103240780211551062287)
                      ·
                        rfl

theorem cell23_2954548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2954548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954548 prefixEnd_2954548 := by exact prefixLift 2954548
  have htrace : WordTrace (prefixWord ++ tailWord_2954548) baseStart_2954548 baseEnd_2954548 := by
    simpa [prefixWord, tailWord_2954548, baseEnd_2954548] using wordTrace_append hprefix tailTrace_2954548
  have hstable : (prefixWord ++ tailWord_2954548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954548).length < 2 ^ (prefixWord ++ tailWord_2954548).sum := by decide
  have hdescent : baseEnd_2954548 < baseStart_2954548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954585 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 3]
def baseStart_2954585 : Nat := 118140960795 + 2954585 * 2 ^ 59
def prefixEnd_2954585 : Nat := 4983230072969 + 3 ^ 40 * 2954585 * 2
def baseEnd_2954585 : Nat := 1517122239564427906299617

theorem tailTrace_2954585 : CollatzResearch.WordTrace tailWord_2954585 prefixEnd_2954585 1517122239564427906299617 := by
  unfold tailWord_2954585
  simp only [CollatzResearch.WordTrace]
  refine ⟨107762568001050622789617209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71841712000700415193078139 107762568001050622789617209)
  ·
    refine ⟨80821926000787967092212907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107762568001050622789617209 80821926000787967092212907)
    ·
      refine ⟨121232889001181950638319361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80821926000787967092212907 121232889001181950638319361)
      ·
        refine ⟨90924666750886462978739521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121232889001181950638319361 90924666750886462978739521)
        ·
          refine ⟨68193500063164847234054641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90924666750886462978739521 68193500063164847234054641)
          ·
            refine ⟨51145125047373635425540981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68193500063164847234054641 51145125047373635425540981)
            ·
              refine ⟨4794855473191278321144467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51145125047373635425540981 4794855473191278321144467)
              ·
                refine ⟨7192283209786917481716701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794855473191278321144467 7192283209786917481716701)
                ·
                  refine ⟨2697106203670094055643763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7192283209786917481716701 2697106203670094055643763)
                  ·
                    refine ⟨4045659305505141083465645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2697106203670094055643763 4045659305505141083465645)
                    ·
                      refine ⟨1517122239564427906299617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4045659305505141083465645 1517122239564427906299617)
                      ·
                        rfl

theorem cell23_2954585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_2954585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954585 prefixEnd_2954585 := by exact prefixLift 2954585
  have htrace : WordTrace (prefixWord ++ tailWord_2954585) baseStart_2954585 baseEnd_2954585 := by
    simpa [prefixWord, tailWord_2954585, baseEnd_2954585] using wordTrace_append hprefix tailTrace_2954585
  have hstable : (prefixWord ++ tailWord_2954585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954585).length < 2 ^ (prefixWord ++ tailWord_2954585).sum := by decide
  have hdescent : baseEnd_2954585 < baseStart_2954585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954591 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_2954591 : Nat := 118140960795 + 2954591 * 2 ^ 59
def prefixEnd_2954591 : Nat := 4983230072969 + 3 ^ 40 * 2954591 * 2
def baseEnd_2954591 : Nat := 1517125320448354882824589

theorem tailTrace_2954591 : CollatzResearch.WordTrace tailWord_2954591 prefixEnd_2954591 1517125320448354882824589 := by
  unfold tailWord_2954591
  simp only [CollatzResearch.WordTrace]
  refine ⟨107762786839028885814335627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71841857892685923876223751 107762786839028885814335627)
  ·
    refine ⟨161644180258543328721503441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107762786839028885814335627 161644180258543328721503441)
    ·
      refine ⟨121233135193907496541127581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161644180258543328721503441 121233135193907496541127581)
      ·
        refine ⟨45462425697715311202922843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121233135193907496541127581 45462425697715311202922843)
        ·
          refine ⟨68193638546572966804384265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45462425697715311202922843 68193638546572966804384265)
          ·
            refine ⟨51145228909929725103288199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68193638546572966804384265 51145228909929725103288199)
            ·
              refine ⟨76717843364894587654932299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51145228909929725103288199 76717843364894587654932299)
              ·
                refine ⟨115076765047341881482398449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76717843364894587654932299 115076765047341881482398449)
                ·
                  refine ⟨86307573785506411111798837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115076765047341881482398449 86307573785506411111798837)
                  ·
                    refine ⟨8091335042391226041731141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86307573785506411111798837 8091335042391226041731141)
                    ·
                      refine ⟨1517125320448354882824589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8091335042391226041731141 1517125320448354882824589)
                      ·
                        rfl

theorem cell23_2954591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_2954591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954591 prefixEnd_2954591 := by exact prefixLift 2954591
  have htrace : WordTrace (prefixWord ++ tailWord_2954591) baseStart_2954591 baseEnd_2954591 := by
    simpa [prefixWord, tailWord_2954591, baseEnd_2954591] using wordTrace_append hprefix tailTrace_2954591
  have hstable : (prefixWord ++ tailWord_2954591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954591).length < 2 ^ (prefixWord ++ tailWord_2954591).sum := by decide
  have hdescent : baseEnd_2954591 < baseStart_2954591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954605 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2954605 : Nat := 118140960795 + 2954605 * 2 ^ 59
def prefixEnd_2954605 : Nat := 4983230072969 + 3 ^ 40 * 2954605 * 2
def baseEnd_2954605 : Nat := 505710836392505942683175

theorem tailTrace_2954605 : CollatzResearch.WordTrace tailWord_2954605 prefixEnd_2954605 505710836392505942683175 := by
  unfold tailWord_2954605
  simp only [CollatzResearch.WordTrace]
  refine ⟨107763297460978166205345269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71842198307318777470230179 107763297460978166205345269)
  ·
    refine ⟨10102809136966703081751119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107763297460978166205345269 10102809136966703081751119)
    ·
      refine ⟨15154213705450054622626679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102809136966703081751119 15154213705450054622626679)
      ·
        refine ⟨22731320558175081933940019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15154213705450054622626679 22731320558175081933940019)
        ·
          refine ⟨34096980837262622900910029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22731320558175081933940019 34096980837262622900910029)
          ·
            refine ⟨12786367813973483587841261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34096980837262622900910029 12786367813973483587841261)
            ·
              refine ⟨4794887930240056345440473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12786367813973483587841261 4794887930240056345440473)
              ·
                refine ⟨3596165947680042259080355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4794887930240056345440473 3596165947680042259080355)
                ·
                  refine ⟨5394248921520063388620533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596165947680042259080355 5394248921520063388620533)
                  ·
                    refine ⟨505710836392505942683175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5394248921520063388620533 505710836392505942683175)
                    ·
                      rfl

theorem cell23_2954605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2954605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954605 prefixEnd_2954605 := by exact prefixLift 2954605
  have htrace : WordTrace (prefixWord ++ tailWord_2954605) baseStart_2954605 baseEnd_2954605 := by
    simpa [prefixWord, tailWord_2954605, baseEnd_2954605] using wordTrace_append hprefix tailTrace_2954605
  have hstable : (prefixWord ++ tailWord_2954605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954605).length < 2 ^ (prefixWord ++ tailWord_2954605).sum := by decide
  have hdescent : baseEnd_2954605 < baseStart_2954605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954608 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_2954608 : Nat := 118140960795 + 2954608 * 2 ^ 59
def prefixEnd_2954608 : Nat := 4983230072969 + 3 ^ 40 * 2954608 * 2
def baseEnd_2954608 : Nat := 1517134049619481316312011

theorem tailTrace_2954608 : CollatzResearch.WordTrace tailWord_2954608 prefixEnd_2954608 1517134049619481316312011 := by
  unfold tailWord_2954608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53881703439983648858852239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71842271253311531811802985 53881703439983648858852239)
  ·
    refine ⟨80822555159975473288278359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53881703439983648858852239 80822555159975473288278359)
    ·
      refine ⟨121233832739963209932417539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80822555159975473288278359 121233832739963209932417539)
      ·
        refine ⟨181850749109944814898626309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121233832739963209932417539 181850749109944814898626309)
        ·
          refine ⟨34097015458114652793492433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181850749109944814898626309 34097015458114652793492433)
          ·
            refine ⟨25572761593585989595119325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34097015458114652793492433 25572761593585989595119325)
            ·
              refine ⟨9589785597594746098169747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25572761593585989595119325 9589785597594746098169747)
              ·
                refine ⟨14384678396392119147254621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589785597594746098169747 14384678396392119147254621)
                ·
                  refine ⟨5394254398647044680220483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14384678396392119147254621 5394254398647044680220483)
                  ·
                    refine ⟨8091381597970567020330725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5394254398647044680220483 8091381597970567020330725)
                    ·
                      refine ⟨1517134049619481316312011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8091381597970567020330725 1517134049619481316312011)
                      ·
                        rfl

theorem cell23_2954608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_2954608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954608 prefixEnd_2954608 := by exact prefixLift 2954608
  have htrace : WordTrace (prefixWord ++ tailWord_2954608) baseStart_2954608 baseEnd_2954608 := by
    simpa [prefixWord, tailWord_2954608, baseEnd_2954608] using wordTrace_append hprefix tailTrace_2954608
  have hstable : (prefixWord ++ tailWord_2954608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954608).length < 2 ^ (prefixWord ++ tailWord_2954608).sum := by decide
  have hdescent : baseEnd_2954608 < baseStart_2954608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954631 : List Nat := [1, 1, 4, 2, 2, 13]
def baseStart_2954631 : Nat := 118140960795 + 2954631 * 2 ^ 59
def prefixEnd_2954631 : Nat := 4983230072969 + 3 ^ 40 * 2954631 * 2
def baseEnd_2954631 : Nat := 6243398599483682001335

theorem tailTrace_2954631 : CollatzResearch.WordTrace tailWord_2954631 prefixEnd_2954631 6243398599483682001335 := by
  unfold tailWord_2954631
  simp only [CollatzResearch.WordTrace]
  refine ⟨107764245758883972645791747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71842830505922648430527831 107764245758883972645791747)
  ·
    refine ⟨161646368638325958968687621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107764245758883972645791747 161646368638325958968687621)
    ·
      refine ⟨30308694119686117306628929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161646368638325958968687621 30308694119686117306628929)
      ·
        refine ⟨22731520589764587979971697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30308694119686117306628929 22731520589764587979971697)
        ·
          refine ⟨17048640442323440984978773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22731520589764587979971697 17048640442323440984978773)
          ·
            refine ⟨6243398599483682001335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 17048640442323440984978773 6243398599483682001335)
            ·
              rfl

theorem cell23_2954631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 13].length) (baseStart_2954631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954631 prefixEnd_2954631 := by exact prefixLift 2954631
  have htrace : WordTrace (prefixWord ++ tailWord_2954631) baseStart_2954631 baseEnd_2954631 := by
    simpa [prefixWord, tailWord_2954631, baseEnd_2954631] using wordTrace_append hprefix tailTrace_2954631
  have hstable : (prefixWord ++ tailWord_2954631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954631).length < 2 ^ (prefixWord ++ tailWord_2954631).sum := by decide
  have hdescent : baseEnd_2954631 < baseStart_2954631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954635 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 2, 4]
def baseStart_2954635 : Nat := 118140960795 + 2954635 * 2 ^ 59
def prefixEnd_2954635 : Nat := 4983230072969 + 3 ^ 40 * 2954635 * 2
def baseEnd_2954635 : Nat := 505715971199050903558129

theorem tailTrace_2954635 : CollatzResearch.WordTrace tailWord_2954635 prefixEnd_2954635 505715971199050903558129 := by
  unfold tailWord_2954635
  simp only [CollatzResearch.WordTrace]
  refine ⟨107764391650869481328937359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71842927767246320885958239 107764391650869481328937359)
  ·
    refine ⟨161646587476304221993406039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107764391650869481328937359 161646587476304221993406039)
    ·
      refine ⟨242469881214456332990109059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161646587476304221993406039 242469881214456332990109059)
      ·
        refine ⟨363704821821684499485163589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242469881214456332990109059 363704821821684499485163589)
        ·
          refine ⟨68194654091565843653468173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363704821821684499485163589 68194654091565843653468173)
          ·
            refine ⟨25572995284337191370050565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68194654091565843653468173 25572995284337191370050565)
            ·
              refine ⟨4794936615813223381884481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25572995284337191370050565 4794936615813223381884481)
              ·
                refine ⟨3596202461859917536413361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4794936615813223381884481 3596202461859917536413361)
                ·
                  refine ⟨2697151846394938152310021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596202461859917536413361 2697151846394938152310021)
                  ·
                    refine ⟨505715971199050903558129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697151846394938152310021 505715971199050903558129)
                    ·
                      rfl

theorem cell23_2954635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 4].length) (baseStart_2954635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954635 prefixEnd_2954635 := by exact prefixLift 2954635
  have htrace : WordTrace (prefixWord ++ tailWord_2954635) baseStart_2954635 baseEnd_2954635 := by
    simpa [prefixWord, tailWord_2954635, baseEnd_2954635] using wordTrace_append hprefix tailTrace_2954635
  have hstable : (prefixWord ++ tailWord_2954635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954635).length < 2 ^ (prefixWord ++ tailWord_2954635).sum := by decide
  have hdescent : baseEnd_2954635 < baseStart_2954635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954652 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2954652 : Nat := 118140960795 + 2954652 * 2 ^ 59
def prefixEnd_2954652 : Nat := 4983230072969 + 3 ^ 40 * 2954652 * 2
def baseEnd_2954652 : Nat := 505718880922759714720603

theorem tailTrace_2954652 : CollatzResearch.WordTrace tailWord_2954652 prefixEnd_2954652 505718880922759714720603 := by
  unfold tailWord_2954652
  simp only [CollatzResearch.WordTrace]
  refine ⟨53882505845903946616153105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71843341127871928821537473 53882505845903946616153105)
  ·
    refine ⟨40411879384427959962114829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53882505845903946616153105 40411879384427959962114829)
    ·
      refine ⟨15154454769160484985793061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40411879384427959962114829 15154454769160484985793061)
      ·
        refine ⟨2841460269217590934836199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15154454769160484985793061 2841460269217590934836199)
        ·
          refine ⟨4262190403826386402254299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841460269217590934836199 4262190403826386402254299)
          ·
            refine ⟨6393285605739579603381449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262190403826386402254299 6393285605739579603381449)
            ·
              refine ⟨4794964204304684702536087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393285605739579603381449 4794964204304684702536087)
              ·
                refine ⟨7192446306457027053804131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794964204304684702536087 7192446306457027053804131)
                ·
                  refine ⟨10788669459685540580706197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192446306457027053804131 10788669459685540580706197)
                  ·
                    refine ⟨505718880922759714720603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10788669459685540580706197 505718880922759714720603)
                    ·
                      rfl

theorem cell23_2954652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2954652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954652 prefixEnd_2954652 := by exact prefixLift 2954652
  have htrace : WordTrace (prefixWord ++ tailWord_2954652) baseStart_2954652 baseEnd_2954652 := by
    simpa [prefixWord, tailWord_2954652, baseEnd_2954652] using wordTrace_append hprefix tailTrace_2954652
  have hstable : (prefixWord ++ tailWord_2954652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954652).length < 2 ^ (prefixWord ++ tailWord_2954652).sum := by decide
  have hdescent : baseEnd_2954652 < baseStart_2954652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954655 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2954655 : Nat := 118140960795 + 2954655 * 2 ^ 59
def prefixEnd_2954655 : Nat := 4983230072969 + 3 ^ 40 * 2954655 * 2
def baseEnd_2954655 : Nat := 1517158183210242632424295

theorem tailTrace_2954655 : CollatzResearch.WordTrace tailWord_2954655 prefixEnd_2954655 1517158183210242632424295 := by
  unfold tailWord_2954655
  simp only [CollatzResearch.WordTrace]
  refine ⟨107765121110797024744665419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71843414073864683163110279 107765121110797024744665419)
  ·
    refine ⟨161647681666195537116998129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107765121110797024744665419 161647681666195537116998129)
    ·
      refine ⟨121235761249646652837748597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161647681666195537116998129 121235761249646652837748597)
      ·
        refine ⟨11365852617154373703538931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121235761249646652837748597 11365852617154373703538931)
        ·
          refine ⟨17048778925731560555308397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365852617154373703538931 17048778925731560555308397)
          ·
            refine ⟨6393292097149335208240649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17048778925731560555308397 6393292097149335208240649)
            ·
              refine ⟨4794969072862001406180487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393292097149335208240649 4794969072862001406180487)
              ·
                refine ⟨7192453609293002109270731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794969072862001406180487 7192453609293002109270731)
                ·
                  refine ⟨10788680413939503163906097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192453609293002109270731 10788680413939503163906097)
                  ·
                    refine ⟨8091510310454627372929573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10788680413939503163906097 8091510310454627372929573)
                    ·
                      refine ⟨1517158183210242632424295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8091510310454627372929573 1517158183210242632424295)
                      ·
                        rfl

theorem cell23_2954655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2954655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954655 prefixEnd_2954655 := by exact prefixLift 2954655
  have htrace : WordTrace (prefixWord ++ tailWord_2954655) baseStart_2954655 baseEnd_2954655 := by
    simpa [prefixWord, tailWord_2954655, baseEnd_2954655] using wordTrace_append hprefix tailTrace_2954655
  have hstable : (prefixWord ++ tailWord_2954655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954655).length < 2 ^ (prefixWord ++ tailWord_2954655).sum := by decide
  have hdescent : baseEnd_2954655 < baseStart_2954655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954709 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2954709 : Nat := 118140960795 + 2954709 * 2 ^ 59
def prefixEnd_2954709 : Nat := 4983230072969 + 3 ^ 40 * 2954709 * 2
def baseEnd_2954709 : Nat := 1517185911165585421149047

theorem tailTrace_2954709 : CollatzResearch.WordTrace tailWord_2954709 prefixEnd_2954709 1517185911165585421149047 := by
  unfold tailWord_2954709
  simp only [CollatzResearch.WordTrace]
  refine ⟨107767090652601391967131181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71844727101734261311420787 107767090652601391967131181)
  ·
    refine ⟨40412658994725521987674193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107767090652601391967131181 40412658994725521987674193)
    ·
      refine ⟨30309494246044141490755645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40412658994725521987674193 30309494246044141490755645)
      ·
        refine ⟨11366060342266553059033367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30309494246044141490755645 11366060342266553059033367)
        ·
          refine ⟨17049090513399829588550051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11366060342266553059033367 17049090513399829588550051)
          ·
            refine ⟨25573635770099744382825077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17049090513399829588550051 25573635770099744382825077)
            ·
              refine ⟨2397528353446851035889851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25573635770099744382825077 2397528353446851035889851)
              ·
                refine ⟨3596292530170276553834777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397528353446851035889851 3596292530170276553834777)
                ·
                  refine ⟨2697219397627707415376083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596292530170276553834777 2697219397627707415376083)
                  ·
                    refine ⟨4045829096441561123064125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2697219397627707415376083 4045829096441561123064125)
                    ·
                      refine ⟨1517185911165585421149047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4045829096441561123064125 1517185911165585421149047)
                      ·
                        rfl

theorem cell23_2954709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2954709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954709 prefixEnd_2954709 := by exact prefixLift 2954709
  have htrace : WordTrace (prefixWord ++ tailWord_2954709) baseStart_2954709 baseEnd_2954709 := by
    simpa [prefixWord, tailWord_2954709, baseEnd_2954709] using wordTrace_append hprefix tailTrace_2954709
  have hstable : (prefixWord ++ tailWord_2954709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954709).length < 2 ^ (prefixWord ++ tailWord_2954709).sum := by decide
  have hdescent : baseEnd_2954709 < baseStart_2954709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954766 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2954766 : Nat := 118140960795 + 2954766 * 2 ^ 59
def prefixEnd_2954766 : Nat := 4983230072969 + 3 ^ 40 * 2954766 * 2
def baseEnd_2954766 : Nat := 1517215179562891698136285

theorem tailTrace_2954766 : CollatzResearch.WordTrace tailWord_2954766 prefixEnd_2954766 1517215179562891698136285 := by
  unfold tailWord_2954766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471146201674361337744519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71846113075596593801304101 13471146201674361337744519)
  ·
    refine ⟨20206719302511542006616779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13471146201674361337744519 20206719302511542006616779)
    ·
      refine ⟨30310078953767313009925169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20206719302511542006616779 30310078953767313009925169)
      ·
        refine ⟨22732559215325484757443877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30310078953767313009925169 22732559215325484757443877)
        ·
          refine ⟨4262354852873528392020727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22732559215325484757443877 4262354852873528392020727)
          ·
            refine ⟨6393532279310292588031091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262354852873528392020727 6393532279310292588031091)
            ·
              refine ⟨9590298418965438882046637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393532279310292588031091 9590298418965438882046637)
              ·
                refine ⟨3596361907112039580767489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9590298418965438882046637 3596361907112039580767489)
                ·
                  refine ⟨2697271430334029685575617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596361907112039580767489 2697271430334029685575617)
                  ·
                    refine ⟨2022953572750522264181713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2697271430334029685575617 2022953572750522264181713)
                    ·
                      refine ⟨1517215179562891698136285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2022953572750522264181713 1517215179562891698136285)
                      ·
                        rfl

theorem cell23_2954766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2954766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954766 prefixEnd_2954766 := by exact prefixLift 2954766
  have htrace : WordTrace (prefixWord ++ tailWord_2954766) baseStart_2954766 baseEnd_2954766 := by
    simpa [prefixWord, tailWord_2954766, baseEnd_2954766] using wordTrace_append hprefix tailTrace_2954766
  have hstable : (prefixWord ++ tailWord_2954766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954766).length < 2 ^ (prefixWord ++ tailWord_2954766).sum := by decide
  have hdescent : baseEnd_2954766 < baseStart_2954766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954778 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2954778 : Nat := 118140960795 + 2954778 * 2 ^ 59
def prefixEnd_2954778 : Nat := 4983230072969 + 3 ^ 40 * 2954778 * 2
def baseEnd_2954778 : Nat := 1517221341330745651186229

theorem tailTrace_2954778 : CollatzResearch.WordTrace tailWord_2954778 prefixEnd_2954778 1517221341330745651186229 := by
  unfold tailWord_2954778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942401822337854187848247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71846404859567611167595325 26942401822337854187848247)
  ·
    refine ⟨40413602733506781281772371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26942401822337854187848247 40413602733506781281772371)
    ·
      refine ⟨60620404100260171922658557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40413602733506781281772371 60620404100260171922658557)
      ·
        refine ⟨22732651537597564470996959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60620404100260171922658557 22732651537597564470996959)
        ·
          refine ⟨34098977306396346706495439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22732651537597564470996959 34098977306396346706495439)
          ·
            refine ⟨51148465959594520059743159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34098977306396346706495439 51148465959594520059743159)
            ·
              refine ⟨76722698939391780089614739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51148465959594520059743159 76722698939391780089614739)
              ·
                refine ⟨115084048409087670134422109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76722698939391780089614739 115084048409087670134422109)
                ·
                  refine ⟨43156518153407876300408291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115084048409087670134422109 43156518153407876300408291)
                  ·
                    refine ⟨64734777230111814450612437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43156518153407876300408291 64734777230111814450612437)
                    ·
                      refine ⟨1517221341330745651186229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64734777230111814450612437 1517221341330745651186229)
                      ·
                        rfl

theorem cell23_2954778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2954778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954778 prefixEnd_2954778 := by exact prefixLift 2954778
  have htrace : WordTrace (prefixWord ++ tailWord_2954778) baseStart_2954778 baseEnd_2954778 := by
    simpa [prefixWord, tailWord_2954778, baseEnd_2954778] using wordTrace_append hprefix tailTrace_2954778
  have hstable : (prefixWord ++ tailWord_2954778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954778).length < 2 ^ (prefixWord ++ tailWord_2954778).sum := by decide
  have hdescent : baseEnd_2954778 < baseStart_2954778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954785 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2954785 : Nat := 118140960795 + 2954785 * 2 ^ 59
def prefixEnd_2954785 : Nat := 4983230072969 + 3 ^ 40 * 2954785 * 2
def baseEnd_2954785 : Nat := 505741645231775707932899

theorem tailTrace_2954785 : CollatzResearch.WordTrace tailWord_2954785 prefixEnd_2954785 505741645231775707932899 := by
  unfold tailWord_2954785
  simp only [CollatzResearch.WordTrace]
  refine ⟨107769862600326056946897809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71846575066884037964598539 107769862600326056946897809)
  ·
    refine ⟨80827396950244542710173357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107769862600326056946897809 80827396950244542710173357)
    ·
      refine ⟨30310273856341703516315009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80827396950244542710173357 30310273856341703516315009)
      ·
        refine ⟨22732705392256277637236257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30310273856341703516315009 22732705392256277637236257)
        ·
          refine ⟨17049529044192208227927193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22732705392256277637236257 17049529044192208227927193)
          ·
            refine ⟨12787146783144156170945395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17049529044192208227927193 12787146783144156170945395)
            ·
              refine ⟨19180720174716234256418093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12787146783144156170945395 19180720174716234256418093)
              ·
                refine ⟨7192770065518587846156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19180720174716234256418093 7192770065518587846156785)
                ·
                  refine ⟨5394577549138940884617589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7192770065518587846156785 5394577549138940884617589)
                  ·
                    refine ⟨505741645231775707932899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5394577549138940884617589 505741645231775707932899)
                    ·
                      rfl

theorem cell23_2954785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2954785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954785 prefixEnd_2954785 := by exact prefixLift 2954785
  have htrace : WordTrace (prefixWord ++ tailWord_2954785) baseStart_2954785 baseEnd_2954785 := by
    simpa [prefixWord, tailWord_2954785, baseEnd_2954785] using wordTrace_append hprefix tailTrace_2954785
  have hstable : (prefixWord ++ tailWord_2954785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954785).length < 2 ^ (prefixWord ++ tailWord_2954785).sum := by decide
  have hdescent : baseEnd_2954785 < baseStart_2954785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954825 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_2954825 : Nat := 118140960795 + 2954825 * 2 ^ 59
def prefixEnd_2954825 : Nat := 4983230072969 + 3 ^ 40 * 2954825 * 2
def baseEnd_2954825 : Nat := 1517245474921506967298513

theorem tailTrace_2954825 : CollatzResearch.WordTrace tailWord_2954825 prefixEnd_2954825 1517245474921506967298513 := by
  unfold tailWord_2954825
  simp only [CollatzResearch.WordTrace]
  refine ⟨107771321520181143778353929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71847547680120762518902619 107771321520181143778353929)
  ·
    refine ⟨80828491140135857833765447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107771321520181143778353929 80828491140135857833765447)
    ·
      refine ⟨121242736710203786750648171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80828491140135857833765447 121242736710203786750648171)
      ·
        refine ⟨181864105065305680125972257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121242736710203786750648171 181864105065305680125972257)
        ·
          refine ⟨136398078798979260094479193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181864105065305680125972257 136398078798979260094479193)
          ·
            refine ⟨102298559099234445070859395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136398078798979260094479193 102298559099234445070859395)
            ·
              refine ⟨153447838648851667606289093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102298559099234445070859395 153447838648851667606289093)
              ·
                refine ⟨28771469746659687676179205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153447838648851667606289093 28771469746659687676179205)
                ·
                  refine ⟨5394650577498691439283601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28771469746659687676179205 5394650577498691439283601)
                  ·
                    refine ⟨4045987933124018579462701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394650577498691439283601 4045987933124018579462701)
                    ·
                      refine ⟨1517245474921506967298513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4045987933124018579462701 1517245474921506967298513)
                      ·
                        rfl

theorem cell23_2954825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_2954825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954825 prefixEnd_2954825 := by exact prefixLift 2954825
  have htrace : WordTrace (prefixWord ++ tailWord_2954825) baseStart_2954825 baseEnd_2954825 := by
    simpa [prefixWord, tailWord_2954825, baseEnd_2954825] using wordTrace_append hprefix tailTrace_2954825
  have hstable : (prefixWord ++ tailWord_2954825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954825).length < 2 ^ (prefixWord ++ tailWord_2954825).sum := by decide
  have hdescent : baseEnd_2954825 < baseStart_2954825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954849 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 1, 4]
def baseStart_2954849 : Nat := 118140960795 + 2954849 * 2 ^ 59
def prefixEnd_2954849 : Nat := 4983230072969 + 3 ^ 40 * 2954849 * 2
def baseEnd_2954849 : Nat := 505752599485738291132801

theorem tailTrace_2954849 : CollatzResearch.WordTrace tailWord_2954849 prefixEnd_2954849 505752599485738291132801 := by
  unfold tailWord_2954849
  simp only [CollatzResearch.WordTrace]
  refine ⟨107772196872094195877227601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71848131248062797251485067 107772196872094195877227601)
  ·
    refine ⟨80829147654070646907920701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107772196872094195877227601 80829147654070646907920701)
    ·
      refine ⟨30310930370276492590470263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80829147654070646907920701 30310930370276492590470263)
      ·
        refine ⟨45466395555414738885705395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30310930370276492590470263 45466395555414738885705395)
        ·
          refine ⟨68199593333122108328558093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45466395555414738885705395 68199593333122108328558093)
          ·
            refine ⟨25574847499920790623209285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68199593333122108328558093 25574847499920790623209285)
            ·
              refine ⟨4795283906235148241851741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25574847499920790623209285 4795283906235148241851741)
              ·
                refine ⟨1798231464838180590694403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4795283906235148241851741 1798231464838180590694403)
                ·
                  refine ⟨2697347197257270886041605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798231464838180590694403 2697347197257270886041605)
                  ·
                    refine ⟨505752599485738291132801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697347197257270886041605 505752599485738291132801)
                    ·
                      rfl

theorem cell23_2954849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_2954849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954849 prefixEnd_2954849 := by exact prefixLift 2954849
  have htrace : WordTrace (prefixWord ++ tailWord_2954849) baseStart_2954849 baseEnd_2954849 := by
    simpa [prefixWord, tailWord_2954849, baseEnd_2954849] using wordTrace_append hprefix tailTrace_2954849
  have hstable : (prefixWord ++ tailWord_2954849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954849).length < 2 ^ (prefixWord ++ tailWord_2954849).sum := by decide
  have hdescent : baseEnd_2954849 < baseStart_2954849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954862 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_2954862 : Nat := 118140960795 + 2954862 * 2 ^ 59
def prefixEnd_2954862 : Nat := 4983230072969 + 3 ^ 40 * 2954862 * 2
def baseEnd_2954862 : Nat := 168584941522858146948427

theorem tailTrace_2954862 : CollatzResearch.WordTrace tailWord_2954862 prefixEnd_2954862 168584941522858146948427 := by
  unfold tailWord_2954862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471583877630887387181355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71848447347364732731633893 13471583877630887387181355)
  ·
    refine ⟨20207375816446331080772033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13471583877630887387181355 20207375816446331080772033)
    ·
      refine ⟨15155531862334748310579025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20207375816446331080772033 15155531862334748310579025)
      ·
        refine ⟨11366648896751061232934269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15155531862334748310579025 11366648896751061232934269)
        ·
          refine ⟨4262493336281647962350351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11366648896751061232934269 4262493336281647962350351)
          ·
            refine ⟨6393740004422471943525527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262493336281647962350351 6393740004422471943525527)
            ·
              refine ⟨9590610006633707915288291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393740004422471943525527 9590610006633707915288291)
              ·
                refine ⟨14385915009950561872932437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9590610006633707915288291 14385915009950561872932437)
                ·
                  refine ⟨168584941522858146948427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14385915009950561872932437 168584941522858146948427)
                  ·
                    rfl

theorem cell23_2954862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_2954862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954862 prefixEnd_2954862 := by exact prefixLift 2954862
  have htrace : WordTrace (prefixWord ++ tailWord_2954862) baseStart_2954862 baseEnd_2954862 := by
    simpa [prefixWord, tailWord_2954862, baseEnd_2954862] using wordTrace_append hprefix tailTrace_2954862
  have hstable : (prefixWord ++ tailWord_2954862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954862).length < 2 ^ (prefixWord ++ tailWord_2954862).sum := by decide
  have hdescent : baseEnd_2954862 < baseStart_2954862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954892 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_2954892 : Nat := 118140960795 + 2954892 * 2 ^ 59
def prefixEnd_2954892 : Nat := 4983230072969 + 3 ^ 40 * 2954892 * 2
def baseEnd_2954892 : Nat := 505759959375119401720235

theorem tailTrace_2954892 : CollatzResearch.WordTrace tailWord_2954892 prefixEnd_2954892 505759959375119401720235 := by
  unfold tailWord_2954892
  simp only [CollatzResearch.WordTrace]
  refine ⟨53886882605469207110521465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71849176807292276147361953 53886882605469207110521465)
  ·
    refine ⟨40415161954101905332891099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53886882605469207110521465 40415161954101905332891099)
    ·
      refine ⟨60622742931152857999336649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40415161954101905332891099 60622742931152857999336649)
      ·
        refine ⟨45467057198364643499502487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60622742931152857999336649 45467057198364643499502487)
        ·
          refine ⟨68200585797546965249253731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45467057198364643499502487 68200585797546965249253731)
          ·
            refine ⟨102300878696320447873880597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68200585797546965249253731 102300878696320447873880597)
            ·
              refine ⟨4795353688890020994088153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102300878696320447873880597 4795353688890020994088153)
              ·
                refine ⟨3596515266667515745566115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795353688890020994088153 3596515266667515745566115)
                ·
                  refine ⟨5394772900001273618349173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596515266667515745566115 5394772900001273618349173)
                  ·
                    refine ⟨505759959375119401720235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5394772900001273618349173 505759959375119401720235)
                    ·
                      rfl

theorem cell23_2954892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_2954892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954892 prefixEnd_2954892 := by exact prefixLift 2954892
  have htrace : WordTrace (prefixWord ++ tailWord_2954892) baseStart_2954892 baseEnd_2954892 := by
    simpa [prefixWord, tailWord_2954892, baseEnd_2954892] using wordTrace_append hprefix tailTrace_2954892
  have hstable : (prefixWord ++ tailWord_2954892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954892).length < 2 ^ (prefixWord ++ tailWord_2954892).sum := by decide
  have hdescent : baseEnd_2954892 < baseStart_2954892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954900 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2954900 : Nat := 118140960795 + 2954900 * 2 ^ 59
def prefixEnd_2954900 : Nat := 4983230072969 + 3 ^ 40 * 2954900 * 2
def baseEnd_2954900 : Nat := 505761328656864724620223

theorem tailTrace_2954900 : CollatzResearch.WordTrace tailWord_2954900 prefixEnd_2954900 505761328656864724620223 := by
  unfold tailWord_2954900
  simp only [CollatzResearch.WordTrace]
  refine ⟨53887028497454715793667077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71849371329939621058222769 53887028497454715793667077)
  ·
    refine ⟨10103817843272759211312577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53887028497454715793667077 10103817843272759211312577)
    ·
      refine ⟨7577863382454569408484433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10103817843272759211312577 7577863382454569408484433)
      ·
        refine ⟨5683397536840927056363325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577863382454569408484433 5683397536840927056363325)
        ·
          refine ⟨2131274076315347646136247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5683397536840927056363325 2131274076315347646136247)
          ·
            refine ⟨3196911114473021469204371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131274076315347646136247 3196911114473021469204371)
            ·
              refine ⟨4795366671709532203806557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196911114473021469204371 4795366671709532203806557)
              ·
                refine ⟨1798262501891074576427459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4795366671709532203806557 1798262501891074576427459)
                ·
                  refine ⟨2697393752836611864641189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798262501891074576427459 2697393752836611864641189)
                  ·
                    refine ⟨505761328656864724620223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697393752836611864641189 505761328656864724620223)
                    ·
                      rfl

theorem cell23_2954900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2954900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954900 prefixEnd_2954900 := by exact prefixLift 2954900
  have htrace : WordTrace (prefixWord ++ tailWord_2954900) baseStart_2954900 baseEnd_2954900 := by
    simpa [prefixWord, tailWord_2954900, baseEnd_2954900] using wordTrace_append hprefix tailTrace_2954900
  have hstable : (prefixWord ++ tailWord_2954900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954900).length < 2 ^ (prefixWord ++ tailWord_2954900).sum := by decide
  have hdescent : baseEnd_2954900 < baseStart_2954900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954935 : List Nat := [1, 1, 3, 1, 5, 1, 1, 10]
def baseStart_2954935 : Nat := 118140960795 + 2954935 * 2 ^ 59
def prefixEnd_2954935 : Nat := 4983230072969 + 3 ^ 40 * 2954935 * 2
def baseEnd_2954935 : Nat := 56196368807166723589741

theorem tailTrace_2954935 : CollatzResearch.WordTrace tailWord_2954935 prefixEnd_2954935 56196368807166723589741 := by
  unfold tailWord_2954935
  simp only [CollatzResearch.WordTrace]
  refine ⟨107775333549782632564858259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71850222366521755043238839 107775333549782632564858259)
  ·
    refine ⟨161663000324673948847287389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107775333549782632564858259 161663000324673948847287389)
    ·
      refine ⟨60623625121752730817732771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161663000324673948847287389 60623625121752730817732771)
      ·
        refine ⟨90935437682629096226599157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60623625121752730817732771 90935437682629096226599157)
        ·
          refine ⟨8525197282746477771243671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90935437682629096226599157 8525197282746477771243671)
          ·
            refine ⟨12787795924119716656865507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8525197282746477771243671 12787795924119716656865507)
            ·
              refine ⟨19181693886179574985298261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12787795924119716656865507 19181693886179574985298261)
              ·
                refine ⟨56196368807166723589741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19181693886179574985298261 56196368807166723589741)
                ·
                  rfl

theorem cell23_2954935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 10].length) (baseStart_2954935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954935 prefixEnd_2954935 := by exact prefixLift 2954935
  have htrace : WordTrace (prefixWord ++ tailWord_2954935) baseStart_2954935 baseEnd_2954935 := by
    simpa [prefixWord, tailWord_2954935, baseEnd_2954935] using wordTrace_append hprefix tailTrace_2954935
  have hstable : (prefixWord ++ tailWord_2954935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954935).length < 2 ^ (prefixWord ++ tailWord_2954935).sum := by decide
  have hdescent : baseEnd_2954935 < baseStart_2954935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954942 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2954942 : Nat := 118140960795 + 2954942 * 2 ^ 59
def prefixEnd_2954942 : Nat := 4983230072969 + 3 ^ 40 * 2954942 * 2
def baseEnd_2954942 : Nat := 1517305552158083009535475

theorem tailTrace_2954942 : CollatzResearch.WordTrace tailWord_2954942 prefixEnd_2954942 1517305552158083009535475 := by
  unfold tailWord_2954942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471948607594659095045385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71850392573838181840242053 13471948607594659095045385)
  ·
    refine ⟨10103961455695994321284039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13471948607594659095045385 10103961455695994321284039)
    ·
      refine ⟨15155942183543991481926059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10103961455695994321284039 15155942183543991481926059)
      ·
        refine ⟨22733913275315987222889089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15155942183543991481926059 22733913275315987222889089)
        ·
          refine ⟨17050434956486990417166817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22733913275315987222889089 17050434956486990417166817)
          ·
            refine ⟨12787826217365242812875113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17050434956486990417166817 12787826217365242812875113)
            ·
              refine ⟨9590869663023932109656335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12787826217365242812875113 9590869663023932109656335)
              ·
                refine ⟨14386304494535898164484503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9590869663023932109656335 14386304494535898164484503)
                ·
                  refine ⟨21579456741803847246726755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14386304494535898164484503 21579456741803847246726755)
                  ·
                    refine ⟨32369185112705770870090133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21579456741803847246726755 32369185112705770870090133)
                    ·
                      refine ⟨1517305552158083009535475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32369185112705770870090133 1517305552158083009535475)
                      ·
                        rfl

theorem cell23_2954942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2954942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954942 prefixEnd_2954942 := by exact prefixLift 2954942
  have htrace : WordTrace (prefixWord ++ tailWord_2954942) baseStart_2954942 baseEnd_2954942 := by
    simpa [prefixWord, tailWord_2954942, baseEnd_2954942] using wordTrace_append hprefix tailTrace_2954942
  have hstable : (prefixWord ++ tailWord_2954942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954942).length < 2 ^ (prefixWord ++ tailWord_2954942).sum := by decide
  have hdescent : baseEnd_2954942 < baseStart_2954942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954950 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2954950 : Nat := 118140960795 + 2954950 * 2 ^ 59
def prefixEnd_2954950 : Nat := 4983230072969 + 3 ^ 40 * 2954950 * 2
def baseEnd_2954950 : Nat := 1517309660003318978235439

theorem tailTrace_2954950 : CollatzResearch.WordTrace tailWord_2954950 prefixEnd_2954950 1517309660003318978235439 := by
  unfold tailWord_2954950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367996270147759066457947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71850587096485526751102869 3367996270147759066457947)
  ·
    refine ⟨5051994405221638599686921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3367996270147759066457947 5051994405221638599686921)
    ·
      refine ⟨3788995803916228949765191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5051994405221638599686921 3788995803916228949765191)
      ·
        refine ⟨5683493705874343424647787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788995803916228949765191 5683493705874343424647787)
        ·
          refine ⟨8525240558811515136971681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683493705874343424647787 8525240558811515136971681)
          ·
            refine ⟨6393930419108636352728761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8525240558811515136971681 6393930419108636352728761)
            ·
              refine ⟨4795447814331477264546571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393930419108636352728761 4795447814331477264546571)
              ·
                refine ⟨7193171721497215896819857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795447814331477264546571 7193171721497215896819857)
                ·
                  refine ⟨5394878791122911922614893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7193171721497215896819857 5394878791122911922614893)
                  ·
                    refine ⟨2023079546671091970980585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5394878791122911922614893 2023079546671091970980585)
                    ·
                      refine ⟨1517309660003318978235439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023079546671091970980585 1517309660003318978235439)
                      ·
                        rfl

theorem cell23_2954950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2954950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954950 prefixEnd_2954950 := by exact prefixLift 2954950
  have htrace : WordTrace (prefixWord ++ tailWord_2954950) baseStart_2954950 baseEnd_2954950 := by
    simpa [prefixWord, tailWord_2954950, baseEnd_2954950] using wordTrace_append hprefix tailTrace_2954950
  have hstable : (prefixWord ++ tailWord_2954950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954950).length < 2 ^ (prefixWord ++ tailWord_2954950).sum := by decide
  have hdescent : baseEnd_2954950 < baseStart_2954950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954973 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2954973 : Nat := 118140960795 + 2954973 * 2 ^ 59
def prefixEnd_2954973 : Nat := 4983230072969 + 3 ^ 40 * 2954973 * 2
def baseEnd_2954973 : Nat := 505773823352790796082611

theorem tailTrace_2954973 : CollatzResearch.WordTrace tailWord_2954973 prefixEnd_2954973 505773823352790796082611 := by
  unfold tailWord_2954973
  simp only [CollatzResearch.WordTrace]
  refine ⟨107776719523644965054741573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71851146349096643369827715 107776719523644965054741573)
  ·
    refine ⟨20208134910683430947764045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107776719523644965054741573 20208134910683430947764045)
    ·
      refine ⟨7578050591506286605411517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20208134910683430947764045 7578050591506286605411517)
      ·
        refine ⟨2841768971814857477029319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7578050591506286605411517 2841768971814857477029319)
        ·
          refine ⟨4262653457722286215543979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841768971814857477029319 4262653457722286215543979)
          ·
            refine ⟨6393980186583429323315969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262653457722286215543979 6393980186583429323315969)
            ·
              refine ⟨4795485139937571992486977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393980186583429323315969 4795485139937571992486977)
              ·
                refine ⟨3596613854953178994365233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795485139937571992486977 3596613854953178994365233)
                ·
                  refine ⟨2697460391214884245773925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596613854953178994365233 2697460391214884245773925)
                  ·
                    refine ⟨505773823352790796082611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697460391214884245773925 505773823352790796082611)
                    ·
                      rfl

theorem cell23_2954973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2954973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954973 prefixEnd_2954973 := by exact prefixLift 2954973
  have htrace : WordTrace (prefixWord ++ tailWord_2954973) baseStart_2954973 baseEnd_2954973 := by
    simpa [prefixWord, tailWord_2954973, baseEnd_2954973] using wordTrace_append hprefix tailTrace_2954973
  have hstable : (prefixWord ++ tailWord_2954973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954973).length < 2 ^ (prefixWord ++ tailWord_2954973).sum := by decide
  have hdescent : baseEnd_2954973 < baseStart_2954973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954995 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 8]
def baseStart_2954995 : Nat := 118140960795 + 2954995 * 2 ^ 59
def prefixEnd_2954995 : Nat := 4983230072969 + 3 ^ 40 * 2954995 * 2
def baseEnd_2954995 : Nat := 505777588877590434057577

theorem tailTrace_2954995 : CollatzResearch.WordTrace tailWord_2954995 prefixEnd_2954995 505777588877590434057577 := by
  unfold tailWord_2954995
  simp only [CollatzResearch.WordTrace]
  refine ⟨107777521929565262812042439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71851681286376841874694959 107777521929565262812042439)
  ·
    refine ⟨161666282894347894218063659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107777521929565262812042439 161666282894347894218063659)
    ·
      refine ⟨242499424341521841327095489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161666282894347894218063659 242499424341521841327095489)
      ·
        refine ⟨181874568256141380995321617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242499424341521841327095489 181874568256141380995321617)
        ·
          refine ⟨136405926192106035746491213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181874568256141380995321617 136405926192106035746491213)
          ·
            refine ⟨51152222322039763404934205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136405926192106035746491213 51152222322039763404934205)
            ·
              refine ⟨19182083370764911276850327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51152222322039763404934205 19182083370764911276850327)
              ·
                refine ⟨28773125056147366915275491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19182083370764911276850327 28773125056147366915275491)
                ·
                  refine ⟨43159687584221050372913237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28773125056147366915275491 43159687584221050372913237)
                  ·
                    refine ⟨505777588877590434057577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43159687584221050372913237 505777588877590434057577)
                    ·
                      rfl

theorem cell23_2954995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_2954995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2954995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2954995 prefixEnd_2954995 := by exact prefixLift 2954995
  have htrace : WordTrace (prefixWord ++ tailWord_2954995) baseStart_2954995 baseEnd_2954995 := by
    simpa [prefixWord, tailWord_2954995, baseEnd_2954995] using wordTrace_append hprefix tailTrace_2954995
  have hstable : (prefixWord ++ tailWord_2954995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954995).length < 2 ^ (prefixWord ++ tailWord_2954995).sum := by decide
  have hdescent : baseEnd_2954995 < baseStart_2954995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955019 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 1, 4, 2]
def baseStart_2955019 : Nat := 118140960795 + 2955019 * 2 ^ 59
def prefixEnd_2955019 : Nat := 4983230072969 + 3 ^ 40 * 2955019 * 2
def baseEnd_2955019 : Nat := 1517345090168479208272621

theorem tailTrace_2955019 : CollatzResearch.WordTrace tailWord_2955019 prefixEnd_2955019 1517345090168479208272621 := by
  unfold tailWord_2955019
  simp only [CollatzResearch.WordTrace]
  refine ⟨107778397281478314910916111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71852264854318876607277407 107778397281478314910916111)
  ·
    refine ⟨161667595922217472366374167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107778397281478314910916111 161667595922217472366374167)
    ·
      refine ⟨242501393883326208549561251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161667595922217472366374167 242501393883326208549561251)
      ·
        refine ⟨363752090824989312824341877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242501393883326208549561251 363752090824989312824341877)
        ·
          refine ⟨34101758514842748077282051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 363752090824989312824341877 34101758514842748077282051)
          ·
            refine ⟨51152637772264122115923077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34101758514842748077282051 51152637772264122115923077)
            ·
              refine ⟨9591119582299522896735577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51152637772264122115923077 9591119582299522896735577)
              ·
                refine ⟨7193339686724642172551683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9591119582299522896735577 7193339686724642172551683)
                ·
                  refine ⟨10790009530086963258827525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7193339686724642172551683 10790009530086963258827525)
                  ·
                    refine ⟨2023126786891305611030161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10790009530086963258827525 2023126786891305611030161)
                    ·
                      refine ⟨1517345090168479208272621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023126786891305611030161 1517345090168479208272621)
                      ·
                        rfl

theorem cell23_2955019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4, 2].length) (baseStart_2955019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955019 prefixEnd_2955019 := by exact prefixLift 2955019
  have htrace : WordTrace (prefixWord ++ tailWord_2955019) baseStart_2955019 baseEnd_2955019 := by
    simpa [prefixWord, tailWord_2955019, baseEnd_2955019] using wordTrace_append hprefix tailTrace_2955019
  have hstable : (prefixWord ++ tailWord_2955019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955019).length < 2 ^ (prefixWord ++ tailWord_2955019).sum := by decide
  have hdescent : baseEnd_2955019 < baseStart_2955019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955022 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2955022 : Nat := 118140960795 + 2955022 * 2 ^ 59
def prefixEnd_2955022 : Nat := 4983230072969 + 3 ^ 40 * 2955022 * 2
def baseEnd_2955022 : Nat := 1517346630610442696535107

theorem tailTrace_2955022 : CollatzResearch.WordTrace tailWord_2955022 prefixEnd_2955022 1517346630610442696535107 := by
  unfold tailWord_2955022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13472313337558430802909415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71852337800311630948850213 13472313337558430802909415)
  ·
    refine ⟨20208470006337646204364123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13472313337558430802909415 20208470006337646204364123)
    ·
      refine ⟨30312705009506469306546185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20208470006337646204364123 30312705009506469306546185)
      ·
        refine ⟨22734528757129851979909639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30312705009506469306546185 22734528757129851979909639)
        ·
          refine ⟨34101793135694777969864459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22734528757129851979909639 34101793135694777969864459)
          ·
            refine ⟨51152689703542166954796689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34101793135694777969864459 51152689703542166954796689)
            ·
              refine ⟨38364517277656625216097517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51152689703542166954796689 38364517277656625216097517)
              ·
                refine ⟨14386693979121234456036569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38364517277656625216097517 14386693979121234456036569)
                ·
                  refine ⟨10790020484340925842027427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14386693979121234456036569 10790020484340925842027427)
                  ·
                    refine ⟨16185030726511388763041141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10790020484340925842027427 16185030726511388763041141)
                    ·
                      refine ⟨1517346630610442696535107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16185030726511388763041141 1517346630610442696535107)
                      ·
                        rfl

theorem cell23_2955022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2955022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955022 prefixEnd_2955022 := by exact prefixLift 2955022
  have htrace : WordTrace (prefixWord ++ tailWord_2955022) baseStart_2955022 baseEnd_2955022 := by
    simpa [prefixWord, tailWord_2955022, baseEnd_2955022] using wordTrace_append hprefix tailTrace_2955022
  have hstable : (prefixWord ++ tailWord_2955022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955022).length < 2 ^ (prefixWord ++ tailWord_2955022).sum := by decide
  have hdescent : baseEnd_2955022 < baseStart_2955022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955025 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 11]
def baseStart_2955025 : Nat := 118140960795 + 2955025 * 2 ^ 59
def prefixEnd_2955025 : Nat := 4983230072969 + 3 ^ 40 * 2955025 * 2
def baseEnd_2955025 : Nat := 168594241228045131644177

theorem tailTrace_2955025 : CollatzResearch.WordTrace tailWord_2955025 prefixEnd_2955025 168594241228045131644177 := by
  unfold tailWord_2955025
  simp only [CollatzResearch.WordTrace]
  refine ⟨107778616119456577935634529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71852410746304385290423019 107778616119456577935634529)
  ·
    refine ⟨80833962089592433451725897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107778616119456577935634529 80833962089592433451725897)
    ·
      refine ⟨60625471567194325088794423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80833962089592433451725897 60625471567194325088794423)
      ·
        refine ⟨90938207350791487633191635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60625471567194325088794423 90938207350791487633191635)
        ·
          refine ⟨136407311026187231449787453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90938207350791487633191635 136407311026187231449787453)
          ·
            refine ⟨51152741634820211793670295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136407311026187231449787453 51152741634820211793670295)
            ·
              refine ⟨76729112452230317690505443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51152741634820211793670295 76729112452230317690505443)
              ·
                refine ⟨115093668678345476535758165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76729112452230317690505443 115093668678345476535758165)
                ·
                  refine ⟨168594241228045131644177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 115093668678345476535758165 168594241228045131644177)
                  ·
                    rfl

theorem cell23_2955025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_2955025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955025 prefixEnd_2955025 := by exact prefixLift 2955025
  have htrace : WordTrace (prefixWord ++ tailWord_2955025) baseStart_2955025 baseEnd_2955025 := by
    simpa [prefixWord, tailWord_2955025, baseEnd_2955025] using wordTrace_append hprefix tailTrace_2955025
  have hstable : (prefixWord ++ tailWord_2955025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955025).length < 2 ^ (prefixWord ++ tailWord_2955025).sum := by decide
  have hdescent : baseEnd_2955025 < baseStart_2955025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955032 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2955032 : Nat := 118140960795 + 2955032 * 2 ^ 59
def prefixEnd_2955032 : Nat := 4983230072969 + 3 ^ 40 * 2955032 * 2
def baseEnd_2955032 : Nat := 1517351765416987657410061

theorem tailTrace_2955032 : CollatzResearch.WordTrace tailWord_2955032 prefixEnd_2955032 1517351765416987657410061 := by
  unfold tailWord_2955032
  simp only [CollatzResearch.WordTrace]
  refine ⟨53889435715215609065569675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71852580953620812087426233 53889435715215609065569675)
  ·
    refine ⟨80834153572823413598354513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53889435715215609065569675 80834153572823413598354513)
    ·
      refine ⟨60625615179617560198765885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80834153572823413598354513 60625615179617560198765885)
      ·
        refine ⟨22734605692356585074537207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60625615179617560198765885 22734605692356585074537207)
        ·
          refine ⟨34101908538534877611805811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22734605692356585074537207 34101908538534877611805811)
          ·
            refine ⟨51152862807802316417708717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34101908538534877611805811 51152862807802316417708717)
            ·
              refine ⟨19182323552925868656640769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51152862807802316417708717 19182323552925868656640769)
              ·
                refine ⟨14386742664694401492480577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19182323552925868656640769 14386742664694401492480577)
                ·
                  refine ⟨10790056998520801119360433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14386742664694401492480577 10790056998520801119360433)
                  ·
                    refine ⟨8092542748890600839520325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10790056998520801119360433 8092542748890600839520325)
                    ·
                      refine ⟨1517351765416987657410061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8092542748890600839520325 1517351765416987657410061)
                      ·
                        rfl

theorem cell23_2955032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2955032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955032 prefixEnd_2955032 := by exact prefixLift 2955032
  have htrace : WordTrace (prefixWord ++ tailWord_2955032) baseStart_2955032 baseEnd_2955032 := by
    simpa [prefixWord, tailWord_2955032, baseEnd_2955032] using wordTrace_append hprefix tailTrace_2955032
  have hstable : (prefixWord ++ tailWord_2955032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955032).length < 2 ^ (prefixWord ++ tailWord_2955032).sum := by decide
  have hdescent : baseEnd_2955032 < baseStart_2955032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_2955035 : Nat := 118140960795 + 2955035 * 2 ^ 59
def prefixEnd_2955035 : Nat := 4983230072969 + 3 ^ 40 * 2955035 * 2
def baseEnd_2955035 : Nat := 1517353305858951145672547

theorem tailTrace_2955035 : CollatzResearch.WordTrace tailWord_2955035 prefixEnd_2955035 1517353305858951145672547 := by
  unfold tailWord_2955035
  simp only [CollatzResearch.WordTrace]
  refine ⟨107778980849420349643498559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71852653899613566428999039 107778980849420349643498559)
  ·
    refine ⟨161668471274130524465247839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107778980849420349643498559 161668471274130524465247839)
    ·
      refine ⟨242502706911195786697871759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161668471274130524465247839 242502706911195786697871759)
      ·
        refine ⟨363754060366793680046807639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242502706911195786697871759 363754060366793680046807639)
        ·
          refine ⟨545631090550190520070211459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363754060366793680046807639 545631090550190520070211459)
          ·
            refine ⟨818446635825285780105317189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545631090550190520070211459 818446635825285780105317189)
            ·
              refine ⟨153458744217241083769746973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 818446635825285780105317189 153458744217241083769746973)
              ·
                refine ⟨57547029081465406413655115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153458744217241083769746973 57547029081465406413655115)
                ·
                  refine ⟨86320543622198109620482673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57547029081465406413655115 86320543622198109620482673)
                  ·
                    refine ⟨64740407716648582215362005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86320543622198109620482673 64740407716648582215362005)
                    ·
                      refine ⟨1517353305858951145672547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64740407716648582215362005 1517353305858951145672547)
                      ·
                        rfl

theorem cell23_2955035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_2955035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955035 prefixEnd_2955035 := by exact prefixLift 2955035
  have htrace : WordTrace (prefixWord ++ tailWord_2955035) baseStart_2955035 baseEnd_2955035 := by
    simpa [prefixWord, tailWord_2955035, baseEnd_2955035] using wordTrace_append hprefix tailTrace_2955035
  have hstable : (prefixWord ++ tailWord_2955035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955035).length < 2 ^ (prefixWord ++ tailWord_2955035).sum := by decide
  have hdescent : baseEnd_2955035 < baseStart_2955035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955036 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2955036 : Nat := 118140960795 + 2955036 * 2 ^ 59
def prefixEnd_2955036 : Nat := 4983230072969 + 3 ^ 40 * 2955036 * 2
def baseEnd_2955036 : Nat := 1517353819339605641760043

theorem tailTrace_2955036 : CollatzResearch.WordTrace tailWord_2955036 prefixEnd_2955036 1517353819339605641760043 := by
  unfold tailWord_2955036
  simp only [CollatzResearch.WordTrace]
  refine ⟨53889508661208363407142481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71852678214944484542856641 53889508661208363407142481)
  ·
    refine ⟨40417131495906272555356861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53889508661208363407142481 40417131495906272555356861)
    ·
      refine ⟨15156424310964852208258823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40417131495906272555356861 15156424310964852208258823)
      ·
        refine ⟨22734636466447278312388235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156424310964852208258823 22734636466447278312388235)
        ·
          refine ⟨34101954699670917468582353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22734636466447278312388235 34101954699670917468582353)
          ·
            refine ⟨25576466024753188101436765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34101954699670917468582353 25576466024753188101436765)
            ·
              refine ⟨9591174759282445538038787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25576466024753188101436765 9591174759282445538038787)
              ·
                refine ⟨14386762138923668307058181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9591174759282445538038787 14386762138923668307058181)
                ·
                  refine ⟨2697517901048187807573409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14386762138923668307058181 2697517901048187807573409)
                  ·
                    refine ⟨2023138425786140855680057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2697517901048187807573409 2023138425786140855680057)
                    ·
                      refine ⟨1517353819339605641760043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023138425786140855680057 1517353819339605641760043)
                      ·
                        rfl

theorem cell23_2955036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2955036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955036 prefixEnd_2955036 := by exact prefixLift 2955036
  have htrace : WordTrace (prefixWord ++ tailWord_2955036) baseStart_2955036 baseEnd_2955036 := by
    simpa [prefixWord, tailWord_2955036, baseEnd_2955036] using wordTrace_append hprefix tailTrace_2955036
  have hstable : (prefixWord ++ tailWord_2955036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955036).length < 2 ^ (prefixWord ++ tailWord_2955036).sum := by decide
  have hdescent : baseEnd_2955036 < baseStart_2955036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955082 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2955082 : Nat := 118140960795 + 2955082 * 2 ^ 59
def prefixEnd_2955082 : Nat := 4983230072969 + 3 ^ 40 * 2955082 * 2
def baseEnd_2955082 : Nat := 1517377439449712461784831

theorem tailTrace_2955082 : CollatzResearch.WordTrace tailWord_2955082 prefixEnd_2955082 1517377439449712461784831 := by
  unfold tailWord_2955082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26945173770062519167614875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71853796720166717780306333 26945173770062519167614875)
  ·
    refine ⟨40417760655093778751422313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26945173770062519167614875 40417760655093778751422313)
    ·
      refine ⟨30313320491320334063566735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40417760655093778751422313 30313320491320334063566735)
      ·
        refine ⟨45469980736980501095350103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30313320491320334063566735 45469980736980501095350103)
        ·
          refine ⟨68204971105470751643025155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45469980736980501095350103 68204971105470751643025155)
          ·
            refine ⟨102307456658206127464537733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68204971105470751643025155 102307456658206127464537733)
            ·
              refine ⟨19182648123413648899600825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102307456658206127464537733 19182648123413648899600825)
              ·
                refine ⟨14386986092560236674700619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19182648123413648899600825 14386986092560236674700619)
                ·
                  refine ⟨21580479138840355012050929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14386986092560236674700619 21580479138840355012050929)
                  ·
                    refine ⟨16185359354130266259038197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21580479138840355012050929 16185359354130266259038197)
                    ·
                      refine ⟨1517377439449712461784831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16185359354130266259038197 1517377439449712461784831)
                      ·
                        rfl

theorem cell23_2955082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2955082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955082 prefixEnd_2955082 := by exact prefixLift 2955082
  have htrace : WordTrace (prefixWord ++ tailWord_2955082) baseStart_2955082 baseEnd_2955082 := by
    simpa [prefixWord, tailWord_2955082, baseEnd_2955082] using wordTrace_append hprefix tailTrace_2955082
  have hstable : (prefixWord ++ tailWord_2955082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955082).length < 2 ^ (prefixWord ++ tailWord_2955082).sum := by decide
  have hdescent : baseEnd_2955082 < baseStart_2955082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955089 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_2955089 : Nat := 118140960795 + 2955089 * 2 ^ 59
def prefixEnd_2955089 : Nat := 4983230072969 + 3 ^ 40 * 2955089 * 2
def baseEnd_2955089 : Nat := 505793677938097978132433

theorem tailTrace_2955089 : CollatzResearch.WordTrace tailWord_2955089 prefixEnd_2955089 505793677938097978132433 := by
  unfold tailWord_2955089
  simp only [CollatzResearch.WordTrace]
  refine ⟨107780950391224716865964321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71853966927483144577309547 107780950391224716865964321)
  ·
    refine ⟨80835712793418537649473241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107780950391224716865964321 80835712793418537649473241)
    ·
      refine ⟨60626784595063903237104931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80835712793418537649473241 60626784595063903237104931)
      ·
        refine ⟨90940176892595854855657397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60626784595063903237104931 90940176892595854855657397)
        ·
          refine ⟨8525641583680861392717881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90940176892595854855657397 8525641583680861392717881)
          ·
            refine ⟨6394231187760646044538411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8525641583680861392717881 6394231187760646044538411)
            ·
              refine ⟨9591346781640969066807617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6394231187760646044538411 9591346781640969066807617)
              ·
                refine ⟨7193510086230726800105713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9591346781640969066807617 7193510086230726800105713)
                ·
                  refine ⟨5395132564673045100079285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7193510086230726800105713 5395132564673045100079285)
                  ·
                    refine ⟨505793677938097978132433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5395132564673045100079285 505793677938097978132433)
                    ·
                      rfl

theorem cell23_2955089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_2955089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955089 prefixEnd_2955089 := by exact prefixLift 2955089
  have htrace : WordTrace (prefixWord ++ tailWord_2955089) baseStart_2955089 baseEnd_2955089 := by
    simpa [prefixWord, tailWord_2955089, baseEnd_2955089] using wordTrace_append hprefix tailTrace_2955089
  have hstable : (prefixWord ++ tailWord_2955089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955089).length < 2 ^ (prefixWord ++ tailWord_2955089).sum := by decide
  have hdescent : baseEnd_2955089 < baseStart_2955089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955109 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_2955109 : Nat := 118140960795 + 2955109 * 2 ^ 59
def prefixEnd_2955109 : Nat := 4983230072969 + 3 ^ 40 * 2955109 * 2
def baseEnd_2955109 : Nat := 1517391303427383856147207

theorem tailTrace_2955109 : CollatzResearch.WordTrace tailWord_2955109 prefixEnd_2955109 1517391303427383856147207 := by
  unfold tailWord_2955109
  simp only [CollatzResearch.WordTrace]
  refine ⟨107781679851152260281692381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71854453234101506854461587 107781679851152260281692381)
  ·
    refine ⟨40418129944182097605634643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107781679851152260281692381 40418129944182097605634643)
    ·
      refine ⟨60627194916273146408451965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40418129944182097605634643 60627194916273146408451965)
      ·
        refine ⟨22735198093602429903169487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60627194916273146408451965 22735198093602429903169487)
        ·
          refine ⟨34102797140403644854754231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22735198093602429903169487 34102797140403644854754231)
          ·
            refine ⟨51154195710605467282131347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34102797140403644854754231 51154195710605467282131347)
            ·
              refine ⟨76731293565908200923197021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51154195710605467282131347 76731293565908200923197021)
              ·
                refine ⟨28774235087215575346198883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76731293565908200923197021 28774235087215575346198883)
                ·
                  refine ⟨43161352630823363019298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28774235087215575346198883 43161352630823363019298325)
                  ·
                    refine ⟨2023188404569845141529609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43161352630823363019298325 2023188404569845141529609)
                    ·
                      refine ⟨1517391303427383856147207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023188404569845141529609 1517391303427383856147207)
                      ·
                        rfl

theorem cell23_2955109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_2955109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955109 prefixEnd_2955109 := by exact prefixLift 2955109
  have htrace : WordTrace (prefixWord ++ tailWord_2955109) baseStart_2955109 baseEnd_2955109 := by
    simpa [prefixWord, tailWord_2955109, baseEnd_2955109] using wordTrace_append hprefix tailTrace_2955109
  have hstable : (prefixWord ++ tailWord_2955109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955109).length < 2 ^ (prefixWord ++ tailWord_2955109).sum := by decide
  have hdescent : baseEnd_2955109 < baseStart_2955109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955122 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2955122 : Nat := 118140960795 + 2955122 * 2 ^ 59
def prefixEnd_2955122 : Nat := 4983230072969 + 3 ^ 40 * 2955122 * 2
def baseEnd_2955122 : Nat := 1517397978675892305284647

theorem tailTrace_2955122 : CollatzResearch.WordTrace tailWord_2955122 prefixEnd_2955122 1517397978675892305284647 := by
  unfold tailWord_2955122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26945538500026290875478905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71854769333403442334610413 26945538500026290875478905)
  ·
    refine ⟨20209153875019718156609179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26945538500026290875478905 20209153875019718156609179)
    ·
      refine ⟨30313730812529577234913769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20209153875019718156609179 30313730812529577234913769)
      ·
        refine ⟨22735298109397182926185327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30313730812529577234913769 22735298109397182926185327)
        ·
          refine ⟨34102947164095774389277991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22735298109397182926185327 34102947164095774389277991)
          ·
            refine ⟨51154420746143661583916987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34102947164095774389277991 51154420746143661583916987)
            ·
              refine ⟨76731631119215492375875481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51154420746143661583916987 76731631119215492375875481)
              ·
                refine ⟨57548723339411619281906611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76731631119215492375875481 57548723339411619281906611)
                ·
                  refine ⟨86323085009117428922859917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57548723339411619281906611 86323085009117428922859917)
                  ·
                    refine ⟨32371156878419035846072469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86323085009117428922859917 32371156878419035846072469)
                    ·
                      refine ⟨1517397978675892305284647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32371156878419035846072469 1517397978675892305284647)
                      ·
                        rfl

theorem cell23_2955122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2955122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955122 prefixEnd_2955122 := by exact prefixLift 2955122
  have htrace : WordTrace (prefixWord ++ tailWord_2955122) baseStart_2955122 baseEnd_2955122 := by
    simpa [prefixWord, tailWord_2955122, baseEnd_2955122] using wordTrace_append hprefix tailTrace_2955122
  have hstable : (prefixWord ++ tailWord_2955122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955122).length < 2 ^ (prefixWord ++ tailWord_2955122).sum := by decide
  have hdescent : baseEnd_2955122 < baseStart_2955122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955136 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 1, 4]
def baseStart_2955136 : Nat := 118140960795 + 2955136 * 2 ^ 59
def prefixEnd_2955136 : Nat := 4983230072969 + 3 ^ 40 * 2955136 * 2
def baseEnd_2955136 : Nat := 505801722468351750169861

theorem tailTrace_2955136 : CollatzResearch.WordTrace tailWord_2955136 prefixEnd_2955136 505801722468351750169861 := by
  unfold tailWord_2955136
  simp only [CollatzResearch.WordTrace]
  refine ⟨53891332311027221946462631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71855109748036295928616841 53891332311027221946462631)
  ·
    refine ⟨80836998466540832919693947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53891332311027221946462631 80836998466540832919693947)
    ·
      refine ⟨121255497699811249379540921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80836998466540832919693947 121255497699811249379540921)
      ·
        refine ⟨90941623274858437034655691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121255497699811249379540921 90941623274858437034655691)
        ·
          refine ⟨136412434912287655551983537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90941623274858437034655691 136412434912287655551983537)
          ·
            refine ⟨102309326184215741663987653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136412434912287655551983537 102309326184215741663987653)
            ·
              refine ⟨19182998659540451561997685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102309326184215741663987653 19182998659540451561997685)
              ·
                refine ⟨1798406124331917333937283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19182998659540451561997685 1798406124331917333937283)
                ·
                  refine ⟨2697609186497876000905925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798406124331917333937283 2697609186497876000905925)
                  ·
                    refine ⟨505801722468351750169861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697609186497876000905925 505801722468351750169861)
                    ·
                      rfl

theorem cell23_2955136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 4].length) (baseStart_2955136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955136 prefixEnd_2955136 := by exact prefixLift 2955136
  have htrace : WordTrace (prefixWord ++ tailWord_2955136) baseStart_2955136 baseEnd_2955136 := by
    simpa [prefixWord, tailWord_2955136, baseEnd_2955136] using wordTrace_append hprefix tailTrace_2955136
  have hstable : (prefixWord ++ tailWord_2955136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955136).length < 2 ^ (prefixWord ++ tailWord_2955136).sum := by decide
  have hdescent : baseEnd_2955136 < baseStart_2955136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955153 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 1, 4]
def baseStart_2955153 : Nat := 118140960795 + 2955153 * 2 ^ 59
def prefixEnd_2955153 : Nat := 4983230072969 + 3 ^ 40 * 2955153 * 2
def baseEnd_2955153 : Nat := 505804632192060561332335

theorem tailTrace_2955153 : CollatzResearch.WordTrace tailWord_2955153 prefixEnd_2955153 505804632192060561332335 := by
  unfold tailWord_2955153
  simp only [CollatzResearch.WordTrace]
  refine ⟨107783284662992855796294113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71855523108661903864196075 107783284662992855796294113)
  ·
    refine ⟨80837463497244641847220585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107783284662992855796294113 80837463497244641847220585)
    ·
      refine ⟨60628097622933481385415439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80837463497244641847220585 60628097622933481385415439)
      ·
        refine ⟨90942146434400222078123159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60628097622933481385415439 90942146434400222078123159)
        ·
          refine ⟨136413219651600333117184739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90942146434400222078123159 136413219651600333117184739)
          ·
            refine ⟨204619829477400499675777109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136413219651600333117184739 204619829477400499675777109)
            ·
              refine ⟨2397888626688287105575513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 204619829477400499675777109 2397888626688287105575513)
              ·
                refine ⟨1798416470016215329181635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397888626688287105575513 1798416470016215329181635)
                ·
                  refine ⟨2697624705024322993772453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798416470016215329181635 2697624705024322993772453)
                  ·
                    refine ⟨505804632192060561332335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697624705024322993772453 505804632192060561332335)
                    ·
                      rfl

theorem cell23_2955153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_2955153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955153 prefixEnd_2955153 := by exact prefixLift 2955153
  have htrace : WordTrace (prefixWord ++ tailWord_2955153) baseStart_2955153 baseEnd_2955153 := by
    simpa [prefixWord, tailWord_2955153, baseEnd_2955153] using wordTrace_append hprefix tailTrace_2955153
  have hstable : (prefixWord ++ tailWord_2955153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955153).length < 2 ^ (prefixWord ++ tailWord_2955153).sum := by decide
  have hdescent : baseEnd_2955153 < baseStart_2955153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955209 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_2955209 : Nat := 118140960795 + 2955209 * 2 ^ 59
def prefixEnd_2955209 : Nat := 4983230072969 + 3 ^ 40 * 2955209 * 2
def baseEnd_2955209 : Nat := 505814217164277821632249

theorem tailTrace_2955209 : CollatzResearch.WordTrace tailWord_2955209 prefixEnd_2955209 505814217164277821632249 := by
  unfold tailWord_2955209
  simp only [CollatzResearch.WordTrace]
  refine ⟨107785327150789977360332681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71856884767193318240221787 107785327150789977360332681)
  ·
    refine ⟨80838995363092483020249511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107785327150789977360332681 80838995363092483020249511)
    ·
      refine ⟨121258493044638724530374267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80838995363092483020249511 121258493044638724530374267)
      ·
        refine ⟨181887739566958086795561401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121258493044638724530374267 181887739566958086795561401)
        ·
          refine ⟨136415804675218565096671051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181887739566958086795561401 136415804675218565096671051)
          ·
            refine ⟨204623707012827847645006577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136415804675218565096671051 204623707012827847645006577)
            ·
              refine ⟨153467780259620885733754933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204623707012827847645006577 153467780259620885733754933)
              ·
                refine ⟨14387604399339458037539525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153467780259620885733754933 14387604399339458037539525)
                ·
                  refine ⟨2697675824876148382038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14387604399339458037539525 2697675824876148382038661)
                  ·
                    refine ⟨505814217164277821632249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697675824876148382038661 505814217164277821632249)
                    ·
                      rfl

theorem cell23_2955209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_2955209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955209 prefixEnd_2955209 := by exact prefixLift 2955209
  have htrace : WordTrace (prefixWord ++ tailWord_2955209) baseStart_2955209 baseEnd_2955209 := by
    simpa [prefixWord, tailWord_2955209, baseEnd_2955209] using wordTrace_append hprefix tailTrace_2955209
  have hstable : (prefixWord ++ tailWord_2955209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955209).length < 2 ^ (prefixWord ++ tailWord_2955209).sum := by decide
  have hdescent : baseEnd_2955209 < baseStart_2955209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955233 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_2955233 : Nat := 118140960795 + 2955233 * 2 ^ 59
def prefixEnd_2955233 : Nat := 4983230072969 + 3 ^ 40 * 2955233 * 2
def baseEnd_2955233 : Nat := 1517454975028541370996637

theorem tailTrace_2955233 : CollatzResearch.WordTrace tailWord_2955233 prefixEnd_2955233 1517454975028541370996637 := by
  unfold tailWord_2955233
  simp only [CollatzResearch.WordTrace]
  refine ⟨107786202502703029459206353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71857468335135352972804235 107786202502703029459206353)
  ·
    refine ⟨80839651877027272094404765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107786202502703029459206353 80839651877027272094404765)
    ·
      refine ⟨30314869453885227035401787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80839651877027272094404765 30314869453885227035401787)
      ·
        refine ⟨45472304180827840553102681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30314869453885227035401787 45472304180827840553102681)
        ·
          refine ⟨34104228135620880414827011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45472304180827840553102681 34104228135620880414827011)
          ·
            refine ⟨51156342203431320622240517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34104228135620880414827011 51156342203431320622240517)
            ·
              refine ⟨9591814163143372616670097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51156342203431320622240517 9591814163143372616670097)
              ·
                refine ⟨7193860622357529462502573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9591814163143372616670097 7193860622357529462502573)
                ·
                  refine ⟨2697697733384073548438465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7193860622357529462502573 2697697733384073548438465)
                  ·
                    refine ⟨2023273300038055161328849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2697697733384073548438465 2023273300038055161328849)
                    ·
                      refine ⟨1517454975028541370996637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023273300038055161328849 1517454975028541370996637)
                      ·
                        rfl

theorem cell23_2955233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_2955233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955233 prefixEnd_2955233 := by exact prefixLift 2955233
  have htrace : WordTrace (prefixWord ++ tailWord_2955233) baseStart_2955233 baseEnd_2955233 := by
    simpa [prefixWord, tailWord_2955233, baseEnd_2955233] using wordTrace_append hprefix tailTrace_2955233
  have hstable : (prefixWord ++ tailWord_2955233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955233).length < 2 ^ (prefixWord ++ tailWord_2955233).sum := by decide
  have hdescent : baseEnd_2955233 < baseStart_2955233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955284 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2955284 : Nat := 118140960795 + 2955284 * 2 ^ 59
def prefixEnd_2955284 : Nat := 4983230072969 + 3 ^ 40 * 2955284 * 2
def baseEnd_2955284 : Nat := 1517481162541920671458903

theorem tailTrace_2955284 : CollatzResearch.WordTrace tailWord_2955284 prefixEnd_2955284 1517481162541920671458903 := by
  unfold tailWord_2955284
  simp only [CollatzResearch.WordTrace]
  refine ⟨53894031312759132584656453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71858708417012176779541937 53894031312759132584656453)
  ·
    refine ⟨10105130871142337359623085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53894031312759132584656453 10105130871142337359623085)
    ·
      refine ⟨3789424076678376509858657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10105130871142337359623085 3789424076678376509858657)
      ·
        refine ⟨2842068057508782382393993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789424076678376509858657 2842068057508782382393993)
        ·
          refine ⟨2131551043131586786795495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2842068057508782382393993 2131551043131586786795495)
          ·
            refine ⟨3197326564697380180193243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131551043131586786795495 3197326564697380180193243)
            ·
              refine ⟨4795989847046070270289865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197326564697380180193243 4795989847046070270289865)
              ·
                refine ⟨3596992385284552702717399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795989847046070270289865 3596992385284552702717399)
                ·
                  refine ⟨5395488577926829054076099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596992385284552702717399 5395488577926829054076099)
                  ·
                    refine ⟨8093232866890243581114149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395488577926829054076099 8093232866890243581114149)
                    ·
                      refine ⟨1517481162541920671458903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8093232866890243581114149 1517481162541920671458903)
                      ·
                        rfl

theorem cell23_2955284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2955284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955284 prefixEnd_2955284 := by exact prefixLift 2955284
  have htrace : WordTrace (prefixWord ++ tailWord_2955284) baseStart_2955284 baseEnd_2955284 := by
    simpa [prefixWord, tailWord_2955284, baseEnd_2955284] using wordTrace_append hprefix tailTrace_2955284
  have hstable : (prefixWord ++ tailWord_2955284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955284).length < 2 ^ (prefixWord ++ tailWord_2955284).sum := by decide
  have hdescent : baseEnd_2955284 < baseStart_2955284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955287 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2955287 : Nat := 118140960795 + 2955287 * 2 ^ 59
def prefixEnd_2955287 : Nat := 4983230072969 + 3 ^ 40 * 2955287 * 2
def baseEnd_2955287 : Nat := 1517482702983884159721389

theorem tailTrace_2955287 : CollatzResearch.WordTrace tailWord_2955287 prefixEnd_2955287 1517482702983884159721389 := by
  unfold tailWord_2955287
  simp only [CollatzResearch.WordTrace]
  refine ⟨107788172044507396681672115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71858781363004931121114743 107788172044507396681672115)
  ·
    refine ⟨161682258066761095022508173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107788172044507396681672115 161682258066761095022508173)
    ·
      refine ⟨60630846775035410633440565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161682258066761095022508173 60630846775035410633440565)
      ·
        refine ⟨5684141885159569746885053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60630846775035410633440565 5684141885159569746885053)
        ·
          refine ⟨2131553206934838655081895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5684141885159569746885053 2131553206934838655081895)
          ·
            refine ⟨3197329810402257982622843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131553206934838655081895 3197329810402257982622843)
            ·
              refine ⟨4795994715603386973934265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197329810402257982622843 4795994715603386973934265)
              ·
                refine ⟨3596996036702540230450699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795994715603386973934265 3596996036702540230450699)
                ·
                  refine ⟨5395494055053810345676049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596996036702540230450699 5395494055053810345676049)
                  ·
                    refine ⟨4046620541290357759257037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395494055053810345676049 4046620541290357759257037)
                    ·
                      refine ⟨1517482702983884159721389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4046620541290357759257037 1517482702983884159721389)
                      ·
                        rfl

theorem cell23_2955287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2955287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955287 prefixEnd_2955287 := by exact prefixLift 2955287
  have htrace : WordTrace (prefixWord ++ tailWord_2955287) baseStart_2955287 baseEnd_2955287 := by
    simpa [prefixWord, tailWord_2955287, baseEnd_2955287] using wordTrace_append hprefix tailTrace_2955287
  have hstable : (prefixWord ++ tailWord_2955287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955287).length < 2 ^ (prefixWord ++ tailWord_2955287).sum := by decide
  have hdescent : baseEnd_2955287 < baseStart_2955287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955340 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_2955340 : Nat := 118140960795 + 2955340 * 2 ^ 59
def prefixEnd_2955340 : Nat := 4983230072969 + 3 ^ 40 * 2955340 * 2
def baseEnd_2955340 : Nat := 1517509917458572452358645

theorem tailTrace_2955340 : CollatzResearch.WordTrace tailWord_2955340 prefixEnd_2955340 1517509917458572452358645 := by
  unfold tailWord_2955340
  simp only [CollatzResearch.WordTrace]
  refine ⟨53895052556657693366675737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71860070075543591155567649 53895052556657693366675737)
  ·
    refine ⟨40421289417493270025006803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53895052556657693366675737 40421289417493270025006803)
    ·
      refine ⟨60631934126239905037510205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40421289417493270025006803 60631934126239905037510205)
      ·
        refine ⟨22736975297339964389066327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60631934126239905037510205 22736975297339964389066327)
        ·
          refine ⟨34105462946009946583599491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22736975297339964389066327 34105462946009946583599491)
          ·
            refine ⟨51158194419014919875399237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34105462946009946583599491 51158194419014919875399237)
            ·
              refine ⟨9592161453565297476637357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51158194419014919875399237 9592161453565297476637357)
              ·
                refine ⟨3597060545086986553739009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9592161453565297476637357 3597060545086986553739009)
                ·
                  refine ⟨2697795408815239915304257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597060545086986553739009 2697795408815239915304257)
                  ·
                    refine ⟨2023346556611429936478193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2697795408815239915304257 2023346556611429936478193)
                    ·
                      refine ⟨1517509917458572452358645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023346556611429936478193 1517509917458572452358645)
                      ·
                        rfl

theorem cell23_2955340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_2955340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955340 prefixEnd_2955340 := by exact prefixLift 2955340
  have htrace : WordTrace (prefixWord ++ tailWord_2955340) baseStart_2955340 baseEnd_2955340 := by
    simpa [prefixWord, tailWord_2955340, baseEnd_2955340] using wordTrace_append hprefix tailTrace_2955340
  have hstable : (prefixWord ++ tailWord_2955340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955340).length < 2 ^ (prefixWord ++ tailWord_2955340).sum := by decide
  have hdescent : baseEnd_2955340 < baseStart_2955340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955396 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2955396 : Nat := 118140960795 + 2955396 * 2 ^ 59
def prefixEnd_2955396 : Nat := 4983230072969 + 3 ^ 40 * 2955396 * 2
def baseEnd_2955396 : Nat := 1517538672375224233258387

theorem tailTrace_2955396 : CollatzResearch.WordTrace tailWord_2955396 prefixEnd_2955396 1517538672375224233258387 := by
  unfold tailWord_2955396
  simp only [CollatzResearch.WordTrace]
  refine ⟨53896073800556254148695021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71861431734075005531593361 53896073800556254148695021)
  ·
    refine ⟨20211027675208595305760633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53896073800556254148695021 20211027675208595305760633)
    ·
      refine ⟨15158270756406446479320475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20211027675208595305760633 15158270756406446479320475)
      ·
        refine ⟨22737406134609669718980713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15158270756406446479320475 22737406134609669718980713)
        ·
          refine ⟨17053054600957252289235535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22737406134609669718980713 17053054600957252289235535)
          ·
            refine ⟨25579581901435878433853303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17053054600957252289235535 25579581901435878433853303)
            ·
              refine ⟨38369372852153817650779955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25579581901435878433853303 38369372852153817650779955)
              ·
                refine ⟨57554059278230726476169933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38369372852153817650779955 57554059278230726476169933)
                ·
                  refine ⟨21582772229336522428563725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57554059278230726476169933 21582772229336522428563725)
                  ·
                    refine ⟨8093539586001195910711397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21582772229336522428563725 8093539586001195910711397)
                    ·
                      refine ⟨1517538672375224233258387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8093539586001195910711397 1517538672375224233258387)
                      ·
                        rfl

theorem cell23_2955396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2955396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955396 prefixEnd_2955396 := by exact prefixLift 2955396
  have htrace : WordTrace (prefixWord ++ tailWord_2955396) baseStart_2955396 baseEnd_2955396 := by
    simpa [prefixWord, tailWord_2955396, baseEnd_2955396] using wordTrace_append hprefix tailTrace_2955396
  have hstable : (prefixWord ++ tailWord_2955396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955396).length < 2 ^ (prefixWord ++ tailWord_2955396).sum := by decide
  have hdescent : baseEnd_2955396 < baseStart_2955396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955419 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 10]
def baseStart_2955419 : Nat := 118140960795 + 2955419 * 2 ^ 59
def prefixEnd_2955419 : Nat := 4983230072969 + 3 ^ 40 * 2955419 * 2
def baseEnd_2955419 : Nat := 168616720270030849252309

theorem tailTrace_2955419 : CollatzResearch.WordTrace tailWord_2955419 prefixEnd_2955419 168616720270030849252309 := by
  unfold tailWord_2955419
  simp only [CollatzResearch.WordTrace]
  refine ⟨107792986480029183225477311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71861990986686122150318207 107792986480029183225477311)
  ·
    refine ⟨161689479720043774838215967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107792986480029183225477311 161689479720043774838215967)
    ·
      refine ⟨242534219580065662257323951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161689479720043774838215967 242534219580065662257323951)
      ·
        refine ⟨363801329370098493385985927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242534219580065662257323951 363801329370098493385985927)
        ·
          refine ⟨545701994055147740078978891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363801329370098493385985927 545701994055147740078978891)
          ·
            refine ⟨818552991082721610118468337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545701994055147740078978891 818552991082721610118468337)
            ·
              refine ⟨613914743312041207588851253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818552991082721610118468337 613914743312041207588851253)
              ·
                refine ⟨57554507185503863211454805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613914743312041207588851253 57554507185503863211454805)
                ·
                  refine ⟨168616720270030849252309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57554507185503863211454805 168616720270030849252309)
                  ·
                    rfl

theorem cell23_2955419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 10].length) (baseStart_2955419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955419 prefixEnd_2955419 := by exact prefixLift 2955419
  have htrace : WordTrace (prefixWord ++ tailWord_2955419) baseStart_2955419 baseEnd_2955419 := by
    simpa [prefixWord, tailWord_2955419, baseEnd_2955419] using wordTrace_append hprefix tailTrace_2955419
  have hstable : (prefixWord ++ tailWord_2955419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955419).length < 2 ^ (prefixWord ++ tailWord_2955419).sum := by decide
  have hdescent : baseEnd_2955419 < baseStart_2955419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955473 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_2955473 : Nat := 118140960795 + 2955473 * 2 ^ 59
def prefixEnd_2955473 : Nat := 4983230072969 + 3 ^ 40 * 2955473 * 2
def baseEnd_2955473 : Nat := 1517578210385620431995533

theorem tailTrace_2955473 : CollatzResearch.WordTrace tailWord_2955473 prefixEnd_2955473 1517578210385620431995533 := by
  unfold tailWord_2955473
  simp only [CollatzResearch.WordTrace]
  refine ⟨107794956021833550447943073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71863304014555700298628715 107794956021833550447943073)
  ·
    refine ⟨80846217016375162835957305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107794956021833550447943073 80846217016375162835957305)
    ·
      refine ⟨60634662762281372126967979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80846217016375162835957305 60634662762281372126967979)
      ·
        refine ⟨90951994143422058190451969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60634662762281372126967979 90951994143422058190451969)
        ·
          refine ⟨68213995607566543642838977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90951994143422058190451969 68213995607566543642838977)
          ·
            refine ⟨51160496705674907732129233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68213995607566543642838977 51160496705674907732129233)
            ·
              refine ⟨38370372529256180799096925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51160496705674907732129233 38370372529256180799096925)
              ·
                refine ⟨14388889698471067799661347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38370372529256180799096925 14388889698471067799661347)
                ·
                  refine ⟨21583334547706601699492021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14388889698471067799661347 21583334547706601699492021)
                  ·
                    refine ⟨2023437613847493909327377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21583334547706601699492021 2023437613847493909327377)
                    ·
                      refine ⟨1517578210385620431995533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023437613847493909327377 1517578210385620431995533)
                      ·
                        rfl

theorem cell23_2955473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_2955473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955473 prefixEnd_2955473 := by exact prefixLift 2955473
  have htrace : WordTrace (prefixWord ++ tailWord_2955473) baseStart_2955473 baseEnd_2955473 := by
    simpa [prefixWord, tailWord_2955473, baseEnd_2955473] using wordTrace_append hprefix tailTrace_2955473
  have hstable : (prefixWord ++ tailWord_2955473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955473).length < 2 ^ (prefixWord ++ tailWord_2955473).sum := by decide
  have hdescent : baseEnd_2955473 < baseStart_2955473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955491 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 1, 4]
def baseStart_2955491 : Nat := 118140960795 + 2955491 * 2 ^ 59
def prefixEnd_2955491 : Nat := 4983230072969 + 3 ^ 40 * 2955491 * 2
def baseEnd_2955491 : Nat := 505862484345800453856817

theorem tailTrace_2955491 : CollatzResearch.WordTrace tailWord_2955491 prefixEnd_2955491 505862484345800453856817 := by
  unfold tailWord_2955491
  simp only [CollatzResearch.WordTrace]
  refine ⟨107795612535768339522098327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71863741690512226348065551 107795612535768339522098327)
  ·
    refine ⟨161693418803652509283147491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107795612535768339522098327 161693418803652509283147491)
    ·
      refine ⟨242540128205478763924721237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161693418803652509283147491 242540128205478763924721237)
      ·
        refine ⟨2842267127407954264742827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 242540128205478763924721237 2842267127407954264742827)
        ·
          refine ⟨4263400691111931397114241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842267127407954264742827 4263400691111931397114241)
          ·
            refine ⟨3197550518333948547835681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263400691111931397114241 3197550518333948547835681)
            ·
              refine ⟨2398162888750461410876761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197550518333948547835681 2398162888750461410876761)
              ·
                refine ⟨1798622166562846058157571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398162888750461410876761 1798622166562846058157571)
                ·
                  refine ⟨2697933249844269087236357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798622166562846058157571 2697933249844269087236357)
                  ·
                    refine ⟨505862484345800453856817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697933249844269087236357 505862484345800453856817)
                    ·
                      rfl

theorem cell23_2955491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 4].length) (baseStart_2955491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955491 prefixEnd_2955491 := by exact prefixLift 2955491
  have htrace : WordTrace (prefixWord ++ tailWord_2955491) baseStart_2955491 baseEnd_2955491 := by
    simpa [prefixWord, tailWord_2955491, baseEnd_2955491] using wordTrace_append hprefix tailTrace_2955491
  have hstable : (prefixWord ++ tailWord_2955491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955491).length < 2 ^ (prefixWord ++ tailWord_2955491).sum := by decide
  have hdescent : baseEnd_2955491 < baseStart_2955491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955503 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_2955503 : Nat := 118140960795 + 2955503 * 2 ^ 59
def prefixEnd_2955503 : Nat := 4983230072969 + 3 ^ 40 * 2955503 * 2
def baseEnd_2955503 : Nat := 1517593614805255314620395

theorem tailTrace_2955503 : CollatzResearch.WordTrace tailWord_2955503 prefixEnd_2955503 1517593614805255314620395 := by
  unfold tailWord_2955503
  simp only [CollatzResearch.WordTrace]
  refine ⟨107796050211724865571535163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71864033474483243714356775 107796050211724865571535163)
  ·
    refine ⟨161694075317587298357302745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107796050211724865571535163 161694075317587298357302745)
    ·
      refine ⟨121270556488190473767977059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161694075317587298357302745 121270556488190473767977059)
      ·
        refine ⟨181905834732285710651965589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121270556488190473767977059 181905834732285710651965589)
        ·
          refine ⟨8526836003075892686810887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181905834732285710651965589 8526836003075892686810887)
          ·
            refine ⟨12790254004613839030216331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526836003075892686810887 12790254004613839030216331)
            ·
              refine ⟨19185381006920758545324497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12790254004613839030216331 19185381006920758545324497)
              ·
                refine ⟨14389035755190568908993373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19185381006920758545324497 14389035755190568908993373)
                ·
                  refine ⟨5395888408196463340872515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14389035755190568908993373 5395888408196463340872515)
                  ·
                    refine ⟨8093832612294695011308773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395888408196463340872515 8093832612294695011308773)
                    ·
                      refine ⟨1517593614805255314620395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8093832612294695011308773 1517593614805255314620395)
                      ·
                        rfl

theorem cell23_2955503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_2955503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955503 prefixEnd_2955503 := by exact prefixLift 2955503
  have htrace : WordTrace (prefixWord ++ tailWord_2955503) baseStart_2955503 baseEnd_2955503 := by
    simpa [prefixWord, tailWord_2955503, baseEnd_2955503] using wordTrace_append hprefix tailTrace_2955503
  have hstable : (prefixWord ++ tailWord_2955503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955503).length < 2 ^ (prefixWord ++ tailWord_2955503).sum := by decide
  have hdescent : baseEnd_2955503 < baseStart_2955503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955520 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2]
def baseStart_2955520 : Nat := 118140960795 + 2955520 * 2 ^ 59
def prefixEnd_2955520 : Nat := 4983230072969 + 3 ^ 40 * 2955520 * 2
def baseEnd_2955520 : Nat := 1517602343976381748107817

theorem tailTrace_2955520 : CollatzResearch.WordTrace tailWord_2955520 prefixEnd_2955520 1517602343976381748107817 := by
  unfold tailWord_2955520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53898335126331638737452007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71864446835108851649936009 53898335126331638737452007)
  ·
    refine ⟨80847502689497458106178011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53898335126331638737452007 80847502689497458106178011)
    ·
      refine ⟨121271254034246187159267017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80847502689497458106178011 121271254034246187159267017)
      ·
        refine ⟨90953440525684640369450263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121271254034246187159267017 90953440525684640369450263)
        ·
          refine ⟨136430160788526960554175395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90953440525684640369450263 136430160788526960554175395)
          ·
            refine ⟨204645241182790440831263093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136430160788526960554175395 204645241182790440831263093)
            ·
              refine ⟨19185491360886603827930915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204645241182790440831263093 19185491360886603827930915)
              ·
                refine ⟨28778237041329905741896373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19185491360886603827930915 28778237041329905741896373)
                ·
                  refine ⟨2697959722624678663302785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28778237041329905741896373 2697959722624678663302785)
                  ·
                    refine ⟨2023469791968508997477089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2697959722624678663302785 2023469791968508997477089)
                    ·
                      refine ⟨1517602343976381748107817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023469791968508997477089 1517602343976381748107817)
                      ·
                        rfl

theorem cell23_2955520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_2955520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955520 prefixEnd_2955520 := by exact prefixLift 2955520
  have htrace : WordTrace (prefixWord ++ tailWord_2955520) baseStart_2955520 baseEnd_2955520 := by
    simpa [prefixWord, tailWord_2955520, baseEnd_2955520] using wordTrace_append hprefix tailTrace_2955520
  have hstable : (prefixWord ++ tailWord_2955520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955520).length < 2 ^ (prefixWord ++ tailWord_2955520).sum := by decide
  have hdescent : baseEnd_2955520 < baseStart_2955520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955523 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3]
def baseStart_2955523 : Nat := 118140960795 + 2955523 * 2 ^ 59
def prefixEnd_2955523 : Nat := 4983230072969 + 3 ^ 40 * 2955523 * 2
def baseEnd_2955523 : Nat := 1517603884418345236370303

theorem tailTrace_2955523 : CollatzResearch.WordTrace tailWord_2955523 prefixEnd_2955523 1517603884418345236370303 := by
  unfold tailWord_2955523
  simp only [CollatzResearch.WordTrace]
  refine ⟨107796779671652408987263223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71864519781101605991508815 107796779671652408987263223)
  ·
    refine ⟨161695169507478613480894835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107796779671652408987263223 161695169507478613480894835)
    ·
      refine ⟨242542754261217920221342253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161695169507478613480894835 242542754261217920221342253)
      ·
        refine ⟨90953532847956720083003345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242542754261217920221342253 90953532847956720083003345)
        ·
          refine ⟨68215149635967540062252509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90953532847956720083003345 68215149635967540062252509)
          ·
            refine ⟨25580681113487827523344691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68215149635967540062252509 25580681113487827523344691)
            ·
              refine ⟨38371021670231741285017037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25580681113487827523344691 38371021670231741285017037)
              ·
                refine ⟨14389133126336902981881389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38371021670231741285017037 14389133126336902981881389)
                ·
                  refine ⟨5395924922376338618205521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14389133126336902981881389 5395924922376338618205521)
                  ·
                    refine ⟨4046943691782253963654141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395924922376338618205521 4046943691782253963654141)
                    ·
                      refine ⟨1517603884418345236370303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4046943691782253963654141 1517603884418345236370303)
                      ·
                        rfl

theorem cell23_2955523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_2955523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955523 prefixEnd_2955523 := by exact prefixLift 2955523
  have htrace : WordTrace (prefixWord ++ tailWord_2955523) baseStart_2955523 baseEnd_2955523 := by
    simpa [prefixWord, tailWord_2955523, baseEnd_2955523] using wordTrace_append hprefix tailTrace_2955523
  have hstable : (prefixWord ++ tailWord_2955523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955523).length < 2 ^ (prefixWord ++ tailWord_2955523).sum := by decide
  have hdescent : baseEnd_2955523 < baseStart_2955523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955524 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2955524 : Nat := 118140960795 + 2955524 * 2 ^ 59
def prefixEnd_2955524 : Nat := 4983230072969 + 3 ^ 40 * 2955524 * 2
def baseEnd_2955524 : Nat := 1517604397898999732457799

theorem tailTrace_2955524 : CollatzResearch.WordTrace tailWord_2955524 prefixEnd_2955524 1517604397898999732457799 := by
  unfold tailWord_2955524
  simp only [CollatzResearch.WordTrace]
  refine ⟨53898408072324393079024813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71864544096432524105366417 53898408072324393079024813)
  ·
    refine ⟨20211903027121647404634305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53898408072324393079024813 20211903027121647404634305)
    ·
      refine ⟨15158927270341235553475729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20211903027121647404634305 15158927270341235553475729)
      ·
        refine ⟨11369195452755926665106797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15158927270341235553475729 11369195452755926665106797)
        ·
          refine ⟨4263448294783472499415049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11369195452755926665106797 4263448294783472499415049)
          ·
            refine ⟨3197586221087604374561287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263448294783472499415049 3197586221087604374561287)
            ·
              refine ⟨4796379331631406561841931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197586221087604374561287 4796379331631406561841931)
              ·
                refine ⟨7194568997447109842762897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796379331631406561841931 7194568997447109842762897)
                ·
                  refine ⟨5395926748085332382072173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7194568997447109842762897 5395926748085332382072173)
                  ·
                    refine ⟨2023472530531999643277065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5395926748085332382072173 2023472530531999643277065)
                    ·
                      refine ⟨1517604397898999732457799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023472530531999643277065 1517604397898999732457799)
                      ·
                        rfl

theorem cell23_2955524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2955524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955524 prefixEnd_2955524 := by exact prefixLift 2955524
  have htrace : WordTrace (prefixWord ++ tailWord_2955524) baseStart_2955524 baseEnd_2955524 := by
    simpa [prefixWord, tailWord_2955524, baseEnd_2955524] using wordTrace_append hprefix tailTrace_2955524
  have hstable : (prefixWord ++ tailWord_2955524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955524).length < 2 ^ (prefixWord ++ tailWord_2955524).sum := by decide
  have hdescent : baseEnd_2955524 < baseStart_2955524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955537 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_2955537 : Nat := 118140960795 + 2955537 * 2 ^ 59
def prefixEnd_2955537 : Nat := 4983230072969 + 3 ^ 40 * 2955537 * 2
def baseEnd_2955537 : Nat := 1517611073147508181595239

theorem tailTrace_2955537 : CollatzResearch.WordTrace tailWord_2955537 prefixEnd_2955537 1517611073147508181595239 := by
  unfold tailWord_2955537
  simp only [CollatzResearch.WordTrace]
  refine ⟨107797290293601689378272865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71864860195734459585515243 107797290293601689378272865)
  ·
    refine ⟨80847967720201267033704649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107797290293601689378272865 80847967720201267033704649)
    ·
      refine ⟨60635975790150950275278487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80847967720201267033704649 60635975790150950275278487)
      ·
        refine ⟨90953963685226425412917731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60635975790150950275278487 90953963685226425412917731)
        ·
          refine ⟨136430945527839638119376597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90953963685226425412917731 136430945527839638119376597)
          ·
            refine ⟨3197600285808741518422889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136430945527839638119376597 3197600285808741518422889)
            ·
              refine ⟨2398200214356556138817167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197600285808741518422889 2398200214356556138817167)
              ·
                refine ⟨3597300321534834208225751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398200214356556138817167 3597300321534834208225751)
                ·
                  refine ⟨5395950482302251312338627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597300321534834208225751 5395950482302251312338627)
                  ·
                    refine ⟨8093925723453376968507941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395950482302251312338627 8093925723453376968507941)
                    ·
                      refine ⟨1517611073147508181595239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8093925723453376968507941 1517611073147508181595239)
                      ·
                        rfl

theorem cell23_2955537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_2955537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955537 prefixEnd_2955537 := by exact prefixLift 2955537
  have htrace : WordTrace (prefixWord ++ tailWord_2955537) baseStart_2955537 baseEnd_2955537 := by
    simpa [prefixWord, tailWord_2955537, baseEnd_2955537] using wordTrace_append hprefix tailTrace_2955537
  have hstable : (prefixWord ++ tailWord_2955537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955537).length < 2 ^ (prefixWord ++ tailWord_2955537).sum := by decide
  have hdescent : baseEnd_2955537 < baseStart_2955537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955553 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2955553 : Nat := 118140960795 + 2955553 * 2 ^ 59
def prefixEnd_2955553 : Nat := 4983230072969 + 3 ^ 40 * 2955553 * 2
def baseEnd_2955553 : Nat := 1517619288837980118995165

theorem tailTrace_2955553 : CollatzResearch.WordTrace tailWord_2955553 prefixEnd_2955553 1517619288837980118995165 := by
  unfold tailWord_2955553
  simp only [CollatzResearch.WordTrace]
  refine ⟨107797873861543724110855313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71865249241029149407236875 107797873861543724110855313)
  ·
    refine ⟨80848405396157793083141485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107797873861543724110855313 80848405396157793083141485)
    ·
      refine ⟨30318152023559172406178057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80848405396157793083141485 30318152023559172406178057)
      ·
        refine ⟨22738614017669379304633543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30318152023559172406178057 22738614017669379304633543)
        ·
          refine ⟨34107921026504068956950315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22738614017669379304633543 34107921026504068956950315)
          ·
            refine ⟨51161881539756103435425473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34107921026504068956950315 51161881539756103435425473)
            ·
              refine ⟨38371411154817077576569105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51161881539756103435425473 38371411154817077576569105)
              ·
                refine ⟨28778558366112808182426829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38371411154817077576569105 28778558366112808182426829)
                ·
                  refine ⟨10791959387292303068410061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28778558366112808182426829 10791959387292303068410061)
                  ·
                    refine ⟨4046984770234613650653773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10791959387292303068410061 4046984770234613650653773)
                    ·
                      refine ⟨1517619288837980118995165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4046984770234613650653773 1517619288837980118995165)
                      ·
                        rfl

theorem cell23_2955553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2955553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955553 prefixEnd_2955553 := by exact prefixLift 2955553
  have htrace : WordTrace (prefixWord ++ tailWord_2955553) baseStart_2955553 baseEnd_2955553 := by
    simpa [prefixWord, tailWord_2955553, baseEnd_2955553] using wordTrace_append hprefix tailTrace_2955553
  have hstable : (prefixWord ++ tailWord_2955553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955553).length < 2 ^ (prefixWord ++ tailWord_2955553).sum := by decide
  have hdescent : baseEnd_2955553 < baseStart_2955553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955554 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_2955554 : Nat := 118140960795 + 2955554 * 2 ^ 59
def prefixEnd_2955554 : Nat := 4983230072969 + 3 ^ 40 * 2955554 * 2
def baseEnd_2955554 : Nat := 1517619802318634615082661

theorem tailTrace_2955554 : CollatzResearch.WordTrace tailWord_2955554 prefixEnd_2955554 1517619802318634615082661 := by
  unfold tailWord_2955554
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949477583635025320410429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71865273556360067521094477 26949477583635025320410429)
  ·
    refine ⟨10106054093863134495153911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26949477583635025320410429 10106054093863134495153911)
    ·
      refine ⟨15159081140794701742730867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10106054093863134495153911 15159081140794701742730867)
      ·
        refine ⟨22738621711192052614096301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159081140794701742730867 22738621711192052614096301)
        ·
          refine ⟨8526983141697019730286113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22738621711192052614096301 8526983141697019730286113)
          ·
            refine ⟨6395237356272764797714585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8526983141697019730286113 6395237356272764797714585)
            ·
              refine ⟨4796428017204573598285939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6395237356272764797714585 4796428017204573598285939)
              ·
                refine ⟨7194642025806860397428909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796428017204573598285939 7194642025806860397428909)
                ·
                  refine ⟨2697990759677572649035841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7194642025806860397428909 2697990759677572649035841)
                  ·
                    refine ⟨2023493069758179486776881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2697990759677572649035841 2023493069758179486776881)
                    ·
                      refine ⟨1517619802318634615082661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023493069758179486776881 1517619802318634615082661)
                      ·
                        rfl

theorem cell23_2955554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_2955554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955554 prefixEnd_2955554 := by exact prefixLift 2955554
  have htrace : WordTrace (prefixWord ++ tailWord_2955554) baseStart_2955554 baseEnd_2955554 := by
    simpa [prefixWord, tailWord_2955554, baseEnd_2955554] using wordTrace_append hprefix tailTrace_2955554
  have hstable : (prefixWord ++ tailWord_2955554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955554).length < 2 ^ (prefixWord ++ tailWord_2955554).sum := by decide
  have hdescent : baseEnd_2955554 < baseStart_2955554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955627 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 2, 2, 2]
def baseStart_2955627 : Nat := 118140960795 + 2955627 * 2 ^ 59
def prefixEnd_2955627 : Nat := 4983230072969 + 3 ^ 40 * 2955627 * 2
def baseEnd_2955627 : Nat := 1517657286406412829469825

theorem tailTrace_2955627 : CollatzResearch.WordTrace tailWord_2955627 prefixEnd_2955627 1517657286406412829469825 := by
  unfold tailWord_2955627
  simp only [CollatzResearch.WordTrace]
  refine ⟨107800572863275634749049135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71867048575517089832699423 107800572863275634749049135)
  ·
    refine ⟨161700859294913452123573703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107800572863275634749049135 161700859294913452123573703)
    ·
      refine ⟨242551288942370178185360555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161700859294913452123573703 242551288942370178185360555)
      ·
        refine ⟨363826933413555267278040833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242551288942370178185360555 363826933413555267278040833)
        ·
          refine ⟨272870200060166450458530625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363826933413555267278040833 272870200060166450458530625)
          ·
            refine ⟨204652650045124837843897969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272870200060166450458530625 204652650045124837843897969)
            ·
              refine ⟨153489487533843628382923477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204652650045124837843897969 153489487533843628382923477)
              ·
                refine ⟨3597409864074460040224769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153489487533843628382923477 3597409864074460040224769)
                ·
                  refine ⟨2698057398055845030168577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597409864074460040224769 2698057398055845030168577)
                  ·
                    refine ⟨2023543048541883772626433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698057398055845030168577 2023543048541883772626433)
                    ·
                      refine ⟨1517657286406412829469825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023543048541883772626433 1517657286406412829469825)
                      ·
                        rfl

theorem cell23_2955627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2, 2].length) (baseStart_2955627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955627 prefixEnd_2955627 := by exact prefixLift 2955627
  have htrace : WordTrace (prefixWord ++ tailWord_2955627) baseStart_2955627 baseEnd_2955627 := by
    simpa [prefixWord, tailWord_2955627, baseEnd_2955627] using wordTrace_append hprefix tailTrace_2955627
  have hstable : (prefixWord ++ tailWord_2955627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955627).length < 2 ^ (prefixWord ++ tailWord_2955627).sum := by decide
  have hdescent : baseEnd_2955627 < baseStart_2955627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955673 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2955673 : Nat := 118140960795 + 2955673 * 2 ^ 59
def prefixEnd_2955673 : Nat := 4983230072969 + 3 ^ 40 * 2955673 * 2
def baseEnd_2955673 : Nat := 1517680906516519649494613

theorem tailTrace_2955673 : CollatzResearch.WordTrace tailWord_2955673 prefixEnd_2955673 1517680906516519649494613 := by
  unfold tailWord_2955673
  simp only [CollatzResearch.WordTrace]
  refine ⟨107802250621108984605223673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71868167080739323070149115 107802250621108984605223673)
  ·
    refine ⟨80851687965831738453917755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107802250621108984605223673 80851687965831738453917755)
    ·
      refine ⟨121277531948747607680876633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80851687965831738453917755 121277531948747607680876633)
      ·
        refine ⟨90958148961560705760657475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121277531948747607680876633 90958148961560705760657475)
        ·
          refine ⟨136437223442341058640986213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90958148961560705760657475 136437223442341058640986213)
          ·
            refine ⟨25581979395438948495184915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136437223442341058640986213 25581979395438948495184915)
            ·
              refine ⟨38372969093158422742777373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25581979395438948495184915 38372969093158422742777373)
              ·
                refine ⟨14389863409934408528541515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38372969093158422742777373 14389863409934408528541515)
                ·
                  refine ⟨21584795114901612792812273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14389863409934408528541515 21584795114901612792812273)
                  ·
                    refine ⟨16188596336176209594609205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21584795114901612792812273 16188596336176209594609205)
                    ·
                      refine ⟨1517680906516519649494613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16188596336176209594609205 1517680906516519649494613)
                      ·
                        rfl

theorem cell23_2955673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2955673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955673 prefixEnd_2955673 := by exact prefixLift 2955673
  have htrace : WordTrace (prefixWord ++ tailWord_2955673) baseStart_2955673 baseEnd_2955673 := by
    simpa [prefixWord, tailWord_2955673, baseEnd_2955673] using wordTrace_append hprefix tailTrace_2955673
  have hstable : (prefixWord ++ tailWord_2955673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955673).length < 2 ^ (prefixWord ++ tailWord_2955673).sum := by decide
  have hdescent : baseEnd_2955673 < baseStart_2955673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955677 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2955677 : Nat := 118140960795 + 2955677 * 2 ^ 59
def prefixEnd_2955677 : Nat := 4983230072969 + 3 ^ 40 * 2955677 * 2
def baseEnd_2955677 : Nat := 1517682960439137633844595

theorem tailTrace_2955677 : CollatzResearch.WordTrace tailWord_2955677 prefixEnd_2955677 1517682960439137633844595 := by
  unfold tailWord_2955677
  simp only [CollatzResearch.WordTrace]
  refine ⟨107802396513094493288369285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71868264342062995525579523 107802396513094493288369285)
  ·
    refine ⟨20212949346205217491569241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107802396513094493288369285 20212949346205217491569241)
    ·
      refine ⟨15159712009653913118676931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20212949346205217491569241 15159712009653913118676931)
      ·
        refine ⟨22739568014480869678015397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159712009653913118676931 22739568014480869678015397)
        ·
          refine ⟨4263669002715163064627887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22739568014480869678015397 4263669002715163064627887)
          ·
            refine ⟨6395503504072744596941831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263669002715163064627887 6395503504072744596941831)
            ·
              refine ⟨9593255256109116895412747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395503504072744596941831 9593255256109116895412747)
              ·
                refine ⟨14389882884163675343119121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9593255256109116895412747 14389882884163675343119121)
                ·
                  refine ⟨10792412163122756507339341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14389882884163675343119121 10792412163122756507339341)
                  ·
                    refine ⟨4047154561171033690252253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10792412163122756507339341 4047154561171033690252253)
                    ·
                      refine ⟨1517682960439137633844595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4047154561171033690252253 1517682960439137633844595)
                      ·
                        rfl

theorem cell23_2955677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2955677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955677 prefixEnd_2955677 := by exact prefixLift 2955677
  have htrace : WordTrace (prefixWord ++ tailWord_2955677) baseStart_2955677 baseEnd_2955677 := by
    simpa [prefixWord, tailWord_2955677, baseEnd_2955677] using wordTrace_append hprefix tailTrace_2955677
  have hstable : (prefixWord ++ tailWord_2955677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955677).length < 2 ^ (prefixWord ++ tailWord_2955677).sum := by decide
  have hdescent : baseEnd_2955677 < baseStart_2955677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955697 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_2955697 : Nat := 118140960795 + 2955697 * 2 ^ 59
def prefixEnd_2955697 : Nat := 4983230072969 + 3 ^ 40 * 2955697 * 2
def baseEnd_2955697 : Nat := 505897743350742518531501

theorem tailTrace_2955697 : CollatzResearch.WordTrace tailWord_2955697 prefixEnd_2955697 505897743350742518531501 := by
  unfold tailWord_2955697
  simp only [CollatzResearch.WordTrace]
  refine ⟨107803125973022036704097345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71868750648681357802731563 107803125973022036704097345)
  ·
    refine ⟨80852344479766527528073009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107803125973022036704097345 80852344479766527528073009)
    ·
      refine ⟨60639258359824895646054757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80852344479766527528073009 60639258359824895646054757)
      ·
        refine ⟨11369860942467167933635267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60639258359824895646054757 11369860942467167933635267)
        ·
          refine ⟨17054791413700751900452901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11369860942467167933635267 17054791413700751900452901)
          ·
            refine ⟨3197773390068890981334919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17054791413700751900452901 3197773390068890981334919)
            ·
              refine ⟨4796660085103336472002379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197773390068890981334919 4796660085103336472002379)
              ·
                refine ⟨7194990127655004708003569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796660085103336472002379 7194990127655004708003569)
                ·
                  refine ⟨5396242595741253531002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7194990127655004708003569 5396242595741253531002677)
                  ·
                    refine ⟨505897743350742518531501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5396242595741253531002677 505897743350742518531501)
                    ·
                      rfl

theorem cell23_2955697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_2955697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955697 prefixEnd_2955697 := by exact prefixLift 2955697
  have htrace : WordTrace (prefixWord ++ tailWord_2955697) baseStart_2955697 baseEnd_2955697 := by
    simpa [prefixWord, tailWord_2955697, baseEnd_2955697] using wordTrace_append hprefix tailTrace_2955697
  have hstable : (prefixWord ++ tailWord_2955697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955697).length < 2 ^ (prefixWord ++ tailWord_2955697).sum := by decide
  have hdescent : baseEnd_2955697 < baseStart_2955697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955734 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_2955734 : Nat := 118140960795 + 2955734 * 2 ^ 59
def prefixEnd_2955734 : Nat := 4983230072969 + 3 ^ 40 * 2955734 * 2
def baseEnd_2955734 : Nat := 1517712228836443910831833

theorem tailTrace_2955734 : CollatzResearch.WordTrace tailWord_2955734 prefixEnd_2955734 1517712228836443910831833 := by
  unfold tailWord_2955734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737779717117999501449641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71869650315925328015462837 6737779717117999501449641)
  ·
    refine ⟨5053334787838499626087231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6737779717117999501449641 5053334787838499626087231)
    ·
      refine ⟨7580002181757749439130847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053334787838499626087231 7580002181757749439130847)
      ·
        refine ⟨11370003272636624158696271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7580002181757749439130847 11370003272636624158696271)
        ·
          refine ⟨17055004908954936238044407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370003272636624158696271 17055004908954936238044407)
          ·
            refine ⟨25582507363432404357066611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17055004908954936238044407 25582507363432404357066611)
            ·
              refine ⟨38373761045148606535599917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25582507363432404357066611 38373761045148606535599917)
              ·
                refine ⟨14390160391930727450849969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38373761045148606535599917 14390160391930727450849969)
                ·
                  refine ⟨10792620293948045588137477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14390160391930727450849969 10792620293948045588137477)
                  ·
                    refine ⟨2023616305115258547775777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10792620293948045588137477 2023616305115258547775777)
                    ·
                      refine ⟨1517712228836443910831833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023616305115258547775777 1517712228836443910831833)
                      ·
                        rfl

theorem cell23_2955734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_2955734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955734 prefixEnd_2955734 := by exact prefixLift 2955734
  have htrace : WordTrace (prefixWord ++ tailWord_2955734) baseStart_2955734 baseEnd_2955734 := by
    simpa [prefixWord, tailWord_2955734, baseEnd_2955734] using wordTrace_append hprefix tailTrace_2955734
  have hstable : (prefixWord ++ tailWord_2955734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955734).length < 2 ^ (prefixWord ++ tailWord_2955734).sum := by decide
  have hdescent : baseEnd_2955734 < baseStart_2955734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955778 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2955778 : Nat := 118140960795 + 2955778 * 2 ^ 59
def prefixEnd_2955778 : Nat := 4983230072969 + 3 ^ 40 * 2955778 * 2
def baseEnd_2955778 : Nat := 505911607328413912893877

theorem tailTrace_2955778 : CollatzResearch.WordTrace tailWord_2955778 prefixEnd_2955778 505911607328413912893877 := by
  unfold tailWord_2955778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951520071432146884448997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71870720190485725025197325 26951520071432146884448997)
  ·
    refine ⟨5053410013393527540834187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26951520071432146884448997 5053410013393527540834187)
    ·
      refine ⟨7580115020090291311251281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053410013393527540834187 7580115020090291311251281)
      ·
        refine ⟨5685086265067718483438461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7580115020090291311251281 5685086265067718483438461)
        ·
          refine ⟨2131907349400394431289423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5685086265067718483438461 2131907349400394431289423)
          ·
            refine ⟨3197861024100591646934135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131907349400394431289423 3197861024100591646934135)
            ·
              refine ⟨4796791536150887470401203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197861024100591646934135 4796791536150887470401203)
              ·
                refine ⟨7195187304226331205601805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796791536150887470401203 7195187304226331205601805)
                ·
                  refine ⟨2698195239084874202100677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7195187304226331205601805 2698195239084874202100677)
                  ·
                    refine ⟨505911607328413912893877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2698195239084874202100677 505911607328413912893877)
                    ·
                      rfl

theorem cell23_2955778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2955778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955778 prefixEnd_2955778 := by exact prefixLift 2955778
  have htrace : WordTrace (prefixWord ++ tailWord_2955778) baseStart_2955778 baseEnd_2955778 := by
    simpa [prefixWord, tailWord_2955778, baseEnd_2955778] using wordTrace_append hprefix tailTrace_2955778
  have hstable : (prefixWord ++ tailWord_2955778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955778).length < 2 ^ (prefixWord ++ tailWord_2955778).sum := by decide
  have hdescent : baseEnd_2955778 < baseStart_2955778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955804 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2955804 : Nat := 118140960795 + 2955804 * 2 ^ 59
def prefixEnd_2955804 : Nat := 4983230072969 + 3 ^ 40 * 2955804 * 2
def baseEnd_2955804 : Nat := 505916057494086212318837

theorem tailTrace_2955804 : CollatzResearch.WordTrace tailWord_2955804 prefixEnd_2955804 505916057494086212318837 := by
  unfold tailWord_2955804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53903514291817196989121233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71871352389089595985494977 53903514291817196989121233)
  ·
    refine ⟨40427635718862897741840925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53903514291817196989121233 40427635718862897741840925)
    ·
      refine ⟨15160363394573586653190347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40427635718862897741840925 15160363394573586653190347)
      ·
        refine ⟨22740545091860379979785521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15160363394573586653190347 22740545091860379979785521)
        ·
          refine ⟨17055408818895284984839141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22740545091860379979785521 17055408818895284984839141)
          ·
            refine ⟨3197889153542865934657339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17055408818895284984839141 3197889153542865934657339)
            ·
              refine ⟨4796833730314298901986009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197889153542865934657339 4796833730314298901986009)
              ·
                refine ⟨3597625297735724176489507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796833730314298901986009 3597625297735724176489507)
                ·
                  refine ⟨5396437946603586264734261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597625297735724176489507 5396437946603586264734261)
                  ·
                    refine ⟨505916057494086212318837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5396437946603586264734261 505916057494086212318837)
                    ·
                      rfl

theorem cell23_2955804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2955804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955804 prefixEnd_2955804 := by exact prefixLift 2955804
  have htrace : WordTrace (prefixWord ++ tailWord_2955804) baseStart_2955804 baseEnd_2955804 := by
    simpa [prefixWord, tailWord_2955804, baseEnd_2955804] using wordTrace_append hprefix tailTrace_2955804
  have hstable : (prefixWord ++ tailWord_2955804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955804).length < 2 ^ (prefixWord ++ tailWord_2955804).sum := by decide
  have hdescent : baseEnd_2955804 < baseStart_2955804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955834 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_2955834 : Nat := 118140960795 + 2955834 * 2 ^ 59
def prefixEnd_2955834 : Nat := 4983230072969 + 3 ^ 40 * 2955834 * 2
def baseEnd_2955834 : Nat := 505921192300631173193791

theorem tailTrace_2955834 : CollatzResearch.WordTrace tailWord_2955834 prefixEnd_2955834 505921192300631173193791 := by
  unfold tailWord_2955834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26952030693381427275458639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71872081849017139401223037 26952030693381427275458639)
  ·
    refine ⟨40428046040072140913187959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26952030693381427275458639 40428046040072140913187959)
    ·
      refine ⟨60642069060108211369781939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40428046040072140913187959 60642069060108211369781939)
      ·
        refine ⟨90963103590162317054672909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60642069060108211369781939 90963103590162317054672909)
        ·
          refine ⟨34111163846310868895502341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90963103590162317054672909 34111163846310868895502341)
          ·
            refine ⟨6395843221183287917906689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34111163846310868895502341 6395843221183287917906689)
            ·
              refine ⟨4796882415887465938430017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6395843221183287917906689 4796882415887465938430017)
              ·
                refine ⟨3597661811915599453822513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796882415887465938430017 3597661811915599453822513)
                ·
                  refine ⟨2698246358936699590366885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597661811915599453822513 2698246358936699590366885)
                  ·
                    refine ⟨505921192300631173193791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2698246358936699590366885 505921192300631173193791)
                    ·
                      rfl

theorem cell23_2955834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_2955834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955834 prefixEnd_2955834 := by exact prefixLift 2955834
  have htrace : WordTrace (prefixWord ++ tailWord_2955834) baseStart_2955834 baseEnd_2955834 := by
    simpa [prefixWord, tailWord_2955834, baseEnd_2955834] using wordTrace_append hprefix tailTrace_2955834
  have hstable : (prefixWord ++ tailWord_2955834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955834).length < 2 ^ (prefixWord ++ tailWord_2955834).sum := by decide
  have hdescent : baseEnd_2955834 < baseStart_2955834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955847 : List Nat := [1, 1, 4, 1, 4, 3, 1, 8]
def baseStart_2955847 : Nat := 118140960795 + 2955847 * 2 ^ 59
def prefixEnd_2955847 : Nat := 4983230072969 + 3 ^ 40 * 2955847 * 2
def baseEnd_2955847 : Nat := 56213713042607480322919

theorem tailTrace_2955847 : CollatzResearch.WordTrace tailWord_2955847 prefixEnd_2955847 56213713042607480322919 := by
  unfold tailWord_2955847
  simp only [CollatzResearch.WordTrace]
  refine ⟨107808596922478612322057795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71872397948319074881371863 107808596922478612322057795)
  ·
    refine ⟨161712895383717918483086693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107808596922478612322057795 161712895383717918483086693)
    ·
      refine ⟨30321167884447109715578755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161712895383717918483086693 30321167884447109715578755)
      ·
        refine ⟨45481751826670664573368133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30321167884447109715578755 45481751826670664573368133)
        ·
          refine ⟨8527828467500749607506525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45481751826670664573368133 8527828467500749607506525)
          ·
            refine ⟨3197935675312781102814947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8527828467500749607506525 3197935675312781102814947)
            ·
              refine ⟨4796903512969171654222421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197935675312781102814947 4796903512969171654222421)
              ·
                refine ⟨56213713042607480322919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4796903512969171654222421 56213713042607480322919)
                ·
                  rfl

theorem cell23_2955847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 8].length) (baseStart_2955847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955847 prefixEnd_2955847 := by exact prefixLift 2955847
  have htrace : WordTrace (prefixWord ++ tailWord_2955847) baseStart_2955847 baseEnd_2955847 := by
    simpa [prefixWord, tailWord_2955847, baseEnd_2955847] using wordTrace_append hprefix tailTrace_2955847
  have hstable : (prefixWord ++ tailWord_2955847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955847).length < 2 ^ (prefixWord ++ tailWord_2955847).sum := by decide
  have hdescent : baseEnd_2955847 < baseStart_2955847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955857 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_2955857 : Nat := 118140960795 + 2955857 * 2 ^ 59
def prefixEnd_2955857 : Nat := 4983230072969 + 3 ^ 40 * 2955857 * 2
def baseEnd_2955857 : Nat := 1517775386956946929593767

theorem tailTrace_2955857 : CollatzResearch.WordTrace tailWord_2955857 prefixEnd_2955857 1517775386956946929593767 := by
  unfold tailWord_2955857
  simp only [CollatzResearch.WordTrace]
  refine ⟨107808961652442384029921825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71872641101628256019947883 107808961652442384029921825)
  ·
    refine ⟨80856721239331788022441369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107808961652442384029921825 80856721239331788022441369)
    ·
      refine ⟨60642540929498841016831027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80856721239331788022441369 60642540929498841016831027)
      ·
        refine ⟨90963811394248261525246541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60642540929498841016831027 90963811394248261525246541)
        ·
          refine ⟨34111429272843098071967453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90963811394248261525246541 34111429272843098071967453)
          ·
            refine ⟨12791785977316161776987795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34111429272843098071967453 12791785977316161776987795)
            ·
              refine ⟨19187678965974242665481693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12791785977316161776987795 19187678965974242665481693)
              ·
                refine ⟨7195379612240340999555635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19187678965974242665481693 7195379612240340999555635)
                ·
                  refine ⟨10793069418360511499333453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7195379612240340999555635 10793069418360511499333453)
                  ·
                    refine ⟨4047401031885191812250045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10793069418360511499333453 4047401031885191812250045)
                    ·
                      refine ⟨1517775386956946929593767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4047401031885191812250045 1517775386956946929593767)
                      ·
                        rfl

theorem cell23_2955857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_2955857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955857 prefixEnd_2955857 := by exact prefixLift 2955857
  have htrace : WordTrace (prefixWord ++ tailWord_2955857) baseStart_2955857 baseEnd_2955857 := by
    simpa [prefixWord, tailWord_2955857, baseEnd_2955857] using wordTrace_append hprefix tailTrace_2955857
  have hstable : (prefixWord ++ tailWord_2955857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955857).length < 2 ^ (prefixWord ++ tailWord_2955857).sum := by decide
  have hdescent : baseEnd_2955857 < baseStart_2955857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955908 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_2955908 : Nat := 118140960795 + 2955908 * 2 ^ 59
def prefixEnd_2955908 : Nat := 4983230072969 + 3 ^ 40 * 2955908 * 2
def baseEnd_2955908 : Nat := 1517801574470326230056033

theorem tailTrace_2955908 : CollatzResearch.WordTrace tailWord_2955908 prefixEnd_2955908 1517801574470326230056033 := by
  unfold tailWord_2955908
  simp only [CollatzResearch.WordTrace]
  refine ⟨53905410887628809870014189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71873881183505079826685585 53905410887628809870014189)
  ·
    refine ⟨20214529082860803701255321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53905410887628809870014189 20214529082860803701255321)
    ·
      refine ⟨15160896812145602775941491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20214529082860803701255321 15160896812145602775941491)
      ·
        refine ⟨22741345218218404163912237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15160896812145602775941491 22741345218218404163912237)
        ·
          refine ⟨8528004456831901561467089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22741345218218404163912237 8528004456831901561467089)
          ·
            refine ⟨6396003342623926171100317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528004456831901561467089 6396003342623926171100317)
            ·
              refine ⟨2398501253483972314162619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6396003342623926171100317 2398501253483972314162619)
              ·
                refine ⟨3597751880225958471243929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398501253483972314162619 3597751880225958471243929)
                ·
                  refine ⟨2698313910169468853432947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597751880225958471243929 2698313910169468853432947)
                  ·
                    refine ⟨4047470865254203280149421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2698313910169468853432947 4047470865254203280149421)
                    ·
                      refine ⟨1517801574470326230056033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4047470865254203280149421 1517801574470326230056033)
                      ·
                        rfl

theorem cell23_2955908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_2955908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955908 prefixEnd_2955908 := by exact prefixLift 2955908
  have htrace : WordTrace (prefixWord ++ tailWord_2955908) baseStart_2955908 baseEnd_2955908 := by
    simpa [prefixWord, tailWord_2955908, baseEnd_2955908] using wordTrace_append hprefix tailTrace_2955908
  have hstable : (prefixWord ++ tailWord_2955908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955908).length < 2 ^ (prefixWord ++ tailWord_2955908).sum := by decide
  have hdescent : baseEnd_2955908 < baseStart_2955908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955934 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2955934 : Nat := 118140960795 + 2955934 * 2 ^ 59
def prefixEnd_2955934 : Nat := 4983230072969 + 3 ^ 40 * 2955934 * 2
def baseEnd_2955934 : Nat := 1517814924967343128330913

theorem tailTrace_2955934 : CollatzResearch.WordTrace tailWord_2955934 prefixEnd_2955934 1517814924967343128330913 := by
  unfold tailWord_2955934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13476471259145428272559357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71874513382108950786983237 13476471259145428272559357)
  ·
    refine ⟨5053676722179535602209759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13476471259145428272559357 5053676722179535602209759)
    ·
      refine ⟨7580515083269303403314639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053676722179535602209759 7580515083269303403314639)
      ·
        refine ⟨11370772624903955104971959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7580515083269303403314639 11370772624903955104971959)
        ·
          refine ⟨17056158937355932657457939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370772624903955104971959 17056158937355932657457939)
          ·
            refine ⟨25584238406033898986186909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17056158937355932657457939 25584238406033898986186909)
            ·
              refine ⟨9594089402262712119820091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25584238406033898986186909 9594089402262712119820091)
              ·
                refine ⟨14391134103394068179730137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9594089402262712119820091 14391134103394068179730137)
                ·
                  refine ⟨10793350577545551134797603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14391134103394068179730137 10793350577545551134797603)
                  ·
                    refine ⟨16190025866318326702196405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10793350577545551134797603 16190025866318326702196405)
                    ·
                      refine ⟨1517814924967343128330913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16190025866318326702196405 1517814924967343128330913)
                      ·
                        rfl

theorem cell23_2955934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2955934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955934 prefixEnd_2955934 := by exact prefixLift 2955934
  have htrace : WordTrace (prefixWord ++ tailWord_2955934) baseStart_2955934 baseEnd_2955934 := by
    simpa [prefixWord, tailWord_2955934, baseEnd_2955934] using wordTrace_append hprefix tailTrace_2955934
  have hstable : (prefixWord ++ tailWord_2955934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955934).length < 2 ^ (prefixWord ++ tailWord_2955934).sum := by decide
  have hdescent : baseEnd_2955934 < baseStart_2955934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955965 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2955965 : Nat := 118140960795 + 2955965 * 2 ^ 59
def prefixEnd_2955965 : Nat := 4983230072969 + 3 ^ 40 * 2955965 * 2
def baseEnd_2955965 : Nat := 1517830842867632507043271

theorem tailTrace_2955965 : CollatzResearch.WordTrace tailWord_2955965 prefixEnd_2955965 1517830842867632507043271 := by
  unfold tailWord_2955965
  simp only [CollatzResearch.WordTrace]
  refine ⟨107812900736051118474853349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71875267157367412316568899 107812900736051118474853349)
  ·
    refine ⟨20214918888009584714035003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107812900736051118474853349 20214918888009584714035003)
    ·
      refine ⟨30322378332014377071052505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20214918888009584714035003 30322378332014377071052505)
      ·
        refine ⟨22741783749010782803289379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30322378332014377071052505 22741783749010782803289379)
        ·
          refine ⟨34112675623516174204934069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22741783749010782803289379 34112675623516174204934069)
          ·
            refine ⟨3198063339704641331712569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34112675623516174204934069 3198063339704641331712569)
            ·
              refine ⟨2398547504778480998784427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3198063339704641331712569 2398547504778480998784427)
              ·
                refine ⟨3597821257167721498176641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398547504778480998784427 3597821257167721498176641)
                ·
                  refine ⟨2698365942875791123632481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597821257167721498176641 2698365942875791123632481)
                  ·
                    refine ⟨2023774457156843342724361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698365942875791123632481 2023774457156843342724361)
                    ·
                      refine ⟨1517830842867632507043271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023774457156843342724361 1517830842867632507043271)
                      ·
                        rfl

theorem cell23_2955965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2955965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2955965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2955965 prefixEnd_2955965 := by exact prefixLift 2955965
  have htrace : WordTrace (prefixWord ++ tailWord_2955965) baseStart_2955965 baseEnd_2955965 := by
    simpa [prefixWord, tailWord_2955965, baseEnd_2955965] using wordTrace_append hprefix tailTrace_2955965
  have hstable : (prefixWord ++ tailWord_2955965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955965).length < 2 ^ (prefixWord ++ tailWord_2955965).sum := by decide
  have hdescent : baseEnd_2955965 < baseStart_2955965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956004 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2956004 : Nat := 118140960795 + 2956004 * 2 ^ 59
def prefixEnd_2956004 : Nat := 4983230072969 + 3 ^ 40 * 2956004 * 2
def baseEnd_2956004 : Nat := 1517850868613157854455591

theorem tailTrace_2956004 : CollatzResearch.WordTrace tailWord_2956004 prefixEnd_2956004 1517850868613157854455591 := by
  unfold tailWord_2956004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53907161591454914067761533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71876215455273218757015377 53907161591454914067761533)
  ·
    refine ⟨20215185596795592775410575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53907161591454914067761533 20215185596795592775410575)
    ·
      refine ⟨30322778395193389163115863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20215185596795592775410575 30322778395193389163115863)
      ·
        refine ⟨45484167592790083744673795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30322778395193389163115863 45484167592790083744673795)
        ·
          refine ⟨68226251389185125617010693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45484167592790083744673795 68226251389185125617010693)
          ·
            refine ⟨12792422135472211053189505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68226251389185125617010693 12792422135472211053189505)
            ·
              refine ⟨9594316601604158289892129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12792422135472211053189505 9594316601604158289892129)
              ·
                refine ⟨7195737451203118717419097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594316601604158289892129 7195737451203118717419097)
                ·
                  refine ⟨5396803088402339038064323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7195737451203118717419097 5396803088402339038064323)
                  ·
                    refine ⟨8095204632603508557096485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5396803088402339038064323 8095204632603508557096485)
                    ·
                      refine ⟨1517850868613157854455591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8095204632603508557096485 1517850868613157854455591)
                      ·
                        rfl

theorem cell23_2956004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2956004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956004 prefixEnd_2956004 := by exact prefixLift 2956004
  have htrace : WordTrace (prefixWord ++ tailWord_2956004) baseStart_2956004 baseEnd_2956004 := by
    simpa [prefixWord, tailWord_2956004, baseEnd_2956004] using wordTrace_append hprefix tailTrace_2956004
  have hstable : (prefixWord ++ tailWord_2956004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956004).length < 2 ^ (prefixWord ++ tailWord_2956004).sum := by decide
  have hdescent : baseEnd_2956004 < baseStart_2956004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956057 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_2956057 : Nat := 118140960795 + 2956057 * 2 ^ 59
def prefixEnd_2956057 : Nat := 4983230072969 + 3 ^ 40 * 2956057 * 2
def baseEnd_2956057 : Nat := 505959361029282049030949

theorem tailTrace_2956057 : CollatzResearch.WordTrace tailWord_2956057 prefixEnd_2956057 505959361029282049030949 := by
  unfold tailWord_2956057
  simp only [CollatzResearch.WordTrace]
  refine ⟨107816256251717818187202425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71877504167811878791468283 107816256251717818187202425)
  ·
    refine ⟨80862192188788363640401819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107816256251717818187202425 80862192188788363640401819)
    ·
      refine ⟨121293288283182545460602729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80862192188788363640401819 121293288283182545460602729)
      ·
        refine ⟨90969966212386909095452047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121293288283182545460602729 90969966212386909095452047)
        ·
          refine ⟨136454949318580363643178071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90969966212386909095452047 136454949318580363643178071)
          ·
            refine ⟨204682423977870545464767107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136454949318580363643178071 204682423977870545464767107)
            ·
              refine ⟨307023635966805818197150661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204682423977870545464767107 307023635966805818197150661)
              ·
                refine ⟨57566931743776090911965749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307023635966805818197150661 57566931743776090911965749)
                ·
                  refine ⟨5396899850979008522996789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57566931743776090911965749 5396899850979008522996789)
                  ·
                    refine ⟨505959361029282049030949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5396899850979008522996789 505959361029282049030949)
                    ·
                      rfl

theorem cell23_2956057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_2956057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956057 prefixEnd_2956057 := by exact prefixLift 2956057
  have htrace : WordTrace (prefixWord ++ tailWord_2956057) baseStart_2956057 baseEnd_2956057 := by
    simpa [prefixWord, tailWord_2956057, baseEnd_2956057] using wordTrace_append hprefix tailTrace_2956057
  have hstable : (prefixWord ++ tailWord_2956057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956057).length < 2 ^ (prefixWord ++ tailWord_2956057).sum := by decide
  have hdescent : baseEnd_2956057 < baseStart_2956057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956061 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 8]
def baseStart_2956061 : Nat := 118140960795 + 2956061 * 2 ^ 59
def prefixEnd_2956061 : Nat := 4983230072969 + 3 ^ 40 * 2956061 * 2
def baseEnd_2956061 : Nat := 168653348556718236826981

theorem tailTrace_2956061 : CollatzResearch.WordTrace tailWord_2956061 prefixEnd_2956061 168653348556718236826981 := by
  unfold tailWord_2956061
  simp only [CollatzResearch.WordTrace]
  refine ⟨107816402143703326870348037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71877601429135551246898691 107816402143703326870348037)
  ·
    refine ⟨20215575401944373788190257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107816402143703326870348037 20215575401944373788190257)
    ·
      refine ⟨15161681551458280341142693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215575401944373788190257 15161681551458280341142693)
      ·
        refine ⟨2842815290898427563964255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15161681551458280341142693 2842815290898427563964255)
        ·
          refine ⟨4264222936347641345946383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842815290898427563964255 4264222936347641345946383)
          ·
            refine ⟨6396334404521462018919575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264222936347641345946383 6396334404521462018919575)
            ·
              refine ⟨9594501606782193028379363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396334404521462018919575 9594501606782193028379363)
              ·
                refine ⟨14391752410173289542569045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9594501606782193028379363 14391752410173289542569045)
                ·
                  refine ⟨168653348556718236826981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14391752410173289542569045 168653348556718236826981)
                  ·
                    rfl

theorem cell23_2956061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_2956061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956061 prefixEnd_2956061 := by exact prefixLift 2956061
  have htrace : WordTrace (prefixWord ++ tailWord_2956061) baseStart_2956061 baseEnd_2956061 := by
    simpa [prefixWord, tailWord_2956061, baseEnd_2956061] using wordTrace_append hprefix tailTrace_2956061
  have hstable : (prefixWord ++ tailWord_2956061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956061).length < 2 ^ (prefixWord ++ tailWord_2956061).sum := by decide
  have hdescent : baseEnd_2956061 < baseStart_2956061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956078 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_2956078 : Nat := 118140960795 + 2956078 * 2 ^ 59
def prefixEnd_2956078 : Nat := 4983230072969 + 3 ^ 40 * 2956078 * 2
def baseEnd_2956078 : Nat := 168654318464621173881139

theorem tailTrace_2956078 : CollatzResearch.WordTrace tailWord_2956078 prefixEnd_2956078 168654318464621173881139 := by
  unfold tailWord_2956078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477127773080217346714611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71878014789761159182477925 13477127773080217346714611)
  ·
    refine ⟨20215691659620326020071917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13477127773080217346714611 20215691659620326020071917)
    ·
      refine ⟨7580884372357622257526969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20215691659620326020071917 7580884372357622257526969)
      ·
        refine ⟨5685663279268216693145227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7580884372357622257526969 5685663279268216693145227)
        ·
          refine ⟨8528494918902325039717841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685663279268216693145227 8528494918902325039717841)
          ·
            refine ⟨6396371189176743779788381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528494918902325039717841 6396371189176743779788381)
            ·
              refine ⟨2398639195941278917420643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6396371189176743779788381 2398639195941278917420643)
              ·
                refine ⟨3597958793911918376130965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398639195941278917420643 3597958793911918376130965)
                ·
                  refine ⟨168654318464621173881139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3597958793911918376130965 168654318464621173881139)
                  ·
                    rfl

theorem cell23_2956078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_2956078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956078 prefixEnd_2956078 := by exact prefixLift 2956078
  have htrace : WordTrace (prefixWord ++ tailWord_2956078) baseStart_2956078 baseEnd_2956078 := by
    simpa [prefixWord, tailWord_2956078, baseEnd_2956078] using wordTrace_append hprefix tailTrace_2956078
  have hstable : (prefixWord ++ tailWord_2956078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956078).length < 2 ^ (prefixWord ++ tailWord_2956078).sum := by decide
  have hdescent : baseEnd_2956078 < baseStart_2956078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956104 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_2956104 : Nat := 118140960795 + 2956104 * 2 ^ 59
def prefixEnd_2956104 : Nat := 4983230072969 + 3 ^ 40 * 2956104 * 2
def baseEnd_2956104 : Nat := 505967405559535821068377

theorem tailTrace_2956104 : CollatzResearch.WordTrace tailWord_2956104 prefixEnd_2956104 505967405559535821068377 := by
  unfold tailWord_2956104
  simp only [CollatzResearch.WordTrace]
  refine ⟨53908985241273772607081683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71878646988365030142775577 53908985241273772607081683)
  ·
    refine ⟨80863477861910658910622525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53908985241273772607081683 80863477861910658910622525)
    ·
      refine ⟨30323804198216497091483447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80863477861910658910622525 30323804198216497091483447)
      ·
        refine ⟨45485706297324745637225171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30323804198216497091483447 45485706297324745637225171)
        ·
          refine ⟨68228559445987118455837757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45485706297324745637225171 68228559445987118455837757)
          ·
            refine ⟨25585709792245169420939159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68228559445987118455837757 25585709792245169420939159)
            ·
              refine ⟨38378564688367754131408739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25585709792245169420939159 38378564688367754131408739)
              ·
                refine ⟨57567847032551631197113109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38378564688367754131408739 57567847032551631197113109)
                ·
                  refine ⟨2698492829650857712364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57567847032551631197113109 2698492829650857712364677)
                  ·
                    refine ⟨505967405559535821068377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2698492829650857712364677 505967405559535821068377)
                    ·
                      rfl

theorem cell23_2956104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_2956104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956104 prefixEnd_2956104 := by exact prefixLift 2956104
  have htrace : WordTrace (prefixWord ++ tailWord_2956104) baseStart_2956104 baseEnd_2956104 := by
    simpa [prefixWord, tailWord_2956104, baseEnd_2956104] using wordTrace_append hprefix tailTrace_2956104
  have hstable : (prefixWord ++ tailWord_2956104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956104).length < 2 ^ (prefixWord ++ tailWord_2956104).sum := by decide
  have hdescent : baseEnd_2956104 < baseStart_2956104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956105 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 1, 1, 3]
def baseStart_2956105 : Nat := 118140960795 + 2956105 * 2 ^ 59
def prefixEnd_2956105 : Nat := 4983230072969 + 3 ^ 40 * 2956105 * 2
def baseEnd_2956105 : Nat := 1517902730159261959292627

theorem tailTrace_2956105 : CollatzResearch.WordTrace tailWord_2956105 prefixEnd_2956105 1517902730159261959292627 := by
  unfold tailWord_2956105
  simp only [CollatzResearch.WordTrace]
  refine ⟨107818006955543922384949769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71878671303695948256633179 107818006955543922384949769)
  ·
    refine ⟨80863505216657941788712327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107818006955543922384949769 80863505216657941788712327)
    ·
      refine ⟨121295257824986912683068491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80863505216657941788712327 121295257824986912683068491)
      ·
        refine ⟨181942886737480369024602737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121295257824986912683068491 181942886737480369024602737)
        ·
          refine ⟨136457165053110276768452053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181942886737480369024602737 136457165053110276768452053)
          ·
            refine ⟨3198214805932272111760595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136457165053110276768452053 3198214805932272111760595)
            ·
              refine ⟨4797322208898408167640893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198214805932272111760595 4797322208898408167640893)
              ·
                refine ⟨1798995828336903062865335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4797322208898408167640893 1798995828336903062865335)
                ·
                  refine ⟨2698493742505354594298003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798995828336903062865335 2698493742505354594298003)
                  ·
                    refine ⟨4047740613758031891447005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2698493742505354594298003 4047740613758031891447005)
                    ·
                      refine ⟨1517902730159261959292627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4047740613758031891447005 1517902730159261959292627)
                      ·
                        rfl

theorem cell23_2956105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 1, 3].length) (baseStart_2956105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956105 prefixEnd_2956105 := by exact prefixLift 2956105
  have htrace : WordTrace (prefixWord ++ tailWord_2956105) baseStart_2956105 baseEnd_2956105 := by
    simpa [prefixWord, tailWord_2956105, baseEnd_2956105] using wordTrace_append hprefix tailTrace_2956105
  have hstable : (prefixWord ++ tailWord_2956105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956105).length < 2 ^ (prefixWord ++ tailWord_2956105).sum := by decide
  have hdescent : baseEnd_2956105 < baseStart_2956105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956218 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_2956218 : Nat := 118140960795 + 2956218 * 2 ^ 59
def prefixEnd_2956218 : Nat := 4983230072969 + 3 ^ 40 * 2956218 * 2
def baseEnd_2956218 : Nat := 1517960753473220017179607

theorem tailTrace_2956218 : CollatzResearch.WordTrace tailWord_2956218 prefixEnd_2956218 1517960753473220017179607 := by
  unfold tailWord_2956218
  simp only [CollatzResearch.WordTrace]
  refine ⟨26955532101033635670953327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71881418936089695122542205 26955532101033635670953327)
  ·
    refine ⟨40433298151550453506429991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26955532101033635670953327 40433298151550453506429991)
    ·
      refine ⟨60649947227325680259644987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40433298151550453506429991 60649947227325680259644987)
      ·
        refine ⟨90974920840988520389467481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60649947227325680259644987 90974920840988520389467481)
        ·
          refine ⟨68231190630741390292100611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90974920840988520389467481 68231190630741390292100611)
          ·
            refine ⟨102346785946112085438150917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68231190630741390292100611 102346785946112085438150917)
            ·
              refine ⟨19190022364896016019653297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102346785946112085438150917 19190022364896016019653297)
              ·
                refine ⟨14392516773672012014739973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19190022364896016019653297 14392516773672012014739973)
                ·
                  refine ⟨2698596895063502252763745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14392516773672012014739973 2698596895063502252763745)
                  ·
                    refine ⟨2023947671297626689572809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698596895063502252763745 2023947671297626689572809)
                    ·
                      refine ⟨1517960753473220017179607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023947671297626689572809 1517960753473220017179607)
                      ·
                        rfl

theorem cell23_2956218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_2956218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956218 prefixEnd_2956218 := by exact prefixLift 2956218
  have htrace : WordTrace (prefixWord ++ tailWord_2956218) baseStart_2956218 baseEnd_2956218 := by
    simpa [prefixWord, tailWord_2956218, baseEnd_2956218] using wordTrace_append hprefix tailTrace_2956218
  have hstable : (prefixWord ++ tailWord_2956218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956218).length < 2 ^ (prefixWord ++ tailWord_2956218).sum := by decide
  have hdescent : baseEnd_2956218 < baseStart_2956218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956235 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 2, 2, 2]
def baseStart_2956235 : Nat := 118140960795 + 2956235 * 2 ^ 59
def prefixEnd_2956235 : Nat := 4983230072969 + 3 ^ 40 * 2956235 * 2
def baseEnd_2956235 : Nat := 1517969482644346450667029

theorem tailTrace_2956235 : CollatzResearch.WordTrace tailWord_2956235 prefixEnd_2956235 1517969482644346450667029 := by
  unfold tailWord_2956235
  simp only [CollatzResearch.WordTrace]
  refine ⟨107822748445072954587182159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71881832296715303058121439 107822748445072954587182159)
  ·
    refine ⟨161734122667609431880773239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107822748445072954587182159 161734122667609431880773239)
    ·
      refine ⟨242601184001414147821159859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161734122667609431880773239 242601184001414147821159859)
      ·
        refine ⟨363901776002121221731739789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242601184001414147821159859 363901776002121221731739789)
        ·
          refine ⟨136463166000795458149402421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363901776002121221731739789 136463166000795458149402421)
          ·
            refine ⟨12793421812574574201506477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136463166000795458149402421 12793421812574574201506477)
            ·
              refine ⟨4797533179715465325564929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12793421812574574201506477 4797533179715465325564929)
              ·
                refine ⟨3598149884786598994173697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797533179715465325564929 3598149884786598994173697)
                ·
                  refine ⟨2698612413589949245630273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598149884786598994173697 2698612413589949245630273)
                  ·
                    refine ⟨2023959310192461934222705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698612413589949245630273 2023959310192461934222705)
                    ·
                      refine ⟨1517969482644346450667029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2023959310192461934222705 1517969482644346450667029)
                      ·
                        rfl

theorem cell23_2956235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2, 2].length) (baseStart_2956235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956235 prefixEnd_2956235 := by exact prefixLift 2956235
  have htrace : WordTrace (prefixWord ++ tailWord_2956235) baseStart_2956235 baseEnd_2956235 := by
    simpa [prefixWord, tailWord_2956235, baseEnd_2956235] using wordTrace_append hprefix tailTrace_2956235
  have hstable : (prefixWord ++ tailWord_2956235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956235).length < 2 ^ (prefixWord ++ tailWord_2956235).sum := by decide
  have hdescent : baseEnd_2956235 < baseStart_2956235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956241 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 5]
def baseStart_2956241 : Nat := 118140960795 + 2956241 * 2 ^ 59
def prefixEnd_2956241 : Nat := 4983230072969 + 3 ^ 40 * 2956241 * 2
def baseEnd_2956241 : Nat := 168663618169808158576889

theorem tailTrace_2956241 : CollatzResearch.WordTrace tailWord_2956241 prefixEnd_2956241 168663618169808158576889 := by
  unfold tailWord_2956241
  simp only [CollatzResearch.WordTrace]
  refine ⟨107822967283051217611900577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71881978188700811741267051 107822967283051217611900577)
  ·
    refine ⟨80867225462288413208925433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107822967283051217611900577 80867225462288413208925433)
    ·
      refine ⟨60650419096716309906694075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80867225462288413208925433 60650419096716309906694075)
      ·
        refine ⟨90975628645074464860041113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60650419096716309906694075 90975628645074464860041113)
        ·
          refine ⟨68231721483805848645030835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90975628645074464860041113 68231721483805848645030835)
          ·
            refine ⟨102347582225708772967546253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68231721483805848645030835 102347582225708772967546253)
            ·
              refine ⟨38380343334640789862829845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102347582225708772967546253 38380343334640789862829845)
              ·
                refine ⟨1799078593811287024820149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38380343334640789862829845 1799078593811287024820149)
                ·
                  refine ⟨168663618169808158576889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799078593811287024820149 168663618169808158576889)
                  ·
                    rfl

theorem cell23_2956241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 5].length) (baseStart_2956241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956241 prefixEnd_2956241 := by exact prefixLift 2956241
  have htrace : WordTrace (prefixWord ++ tailWord_2956241) baseStart_2956241 baseEnd_2956241 := by
    simpa [prefixWord, tailWord_2956241, baseEnd_2956241] using wordTrace_append hprefix tailTrace_2956241
  have hstable : (prefixWord ++ tailWord_2956241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956241).length < 2 ^ (prefixWord ++ tailWord_2956241).sum := by decide
  have hdescent : baseEnd_2956241 < baseStart_2956241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956258 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_2956258 : Nat := 118140960795 + 2956258 * 2 ^ 59
def prefixEnd_2956258 : Nat := 4983230072969 + 3 ^ 40 * 2956258 * 2
def baseEnd_2956258 : Nat := 168664588077711095631047

theorem tailTrace_2956258 : CollatzResearch.WordTrace tailWord_2956258 prefixEnd_2956258 168664588077711095631047 := by
  unfold tailWord_2956258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26955896830997407378817357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71882391549326419676846285 26955896830997407378817357)
  ·
    refine ⟨10108461311624027767056509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26955896830997407378817357 10108461311624027767056509)
    ·
      refine ⟨3790672991859010412646191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10108461311624027767056509 3790672991859010412646191)
      ·
        refine ⟨5686009487788515618969287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3790672991859010412646191 5686009487788515618969287)
        ·
          refine ⟨8529014231682773428453931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686009487788515618969287 8529014231682773428453931)
          ·
            refine ⟨12793521347524160142680897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529014231682773428453931 12793521347524160142680897)
            ·
              refine ⟨9595141010643120107010673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12793521347524160142680897 9595141010643120107010673)
              ·
                refine ⟨7196355757982340080258005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9595141010643120107010673 7196355757982340080258005)
                ·
                  refine ⟨168664588077711095631047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7196355757982340080258005 168664588077711095631047)
                  ·
                    rfl

theorem cell23_2956258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_2956258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956258 prefixEnd_2956258 := by exact prefixLift 2956258
  have htrace : WordTrace (prefixWord ++ tailWord_2956258) baseStart_2956258 baseEnd_2956258 := by
    simpa [prefixWord, tailWord_2956258, baseEnd_2956258] using wordTrace_append hprefix tailTrace_2956258
  have hstable : (prefixWord ++ tailWord_2956258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956258).length < 2 ^ (prefixWord ++ tailWord_2956258).sum := by decide
  have hdescent : baseEnd_2956258 < baseStart_2956258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956348 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 6]
def baseStart_2956348 : Nat := 118140960795 + 2956348 * 2 ^ 59
def prefixEnd_2956348 : Nat := 4983230072969 + 3 ^ 40 * 2956348 * 2
def baseEnd_2956348 : Nat := 168669722884256056506001

theorem tailTrace_2956348 : CollatzResearch.WordTrace tailWord_2956348 prefixEnd_2956348 168669722884256056506001 := by
  unfold tailWord_2956348
  simp only [CollatzResearch.WordTrace]
  refine ⟨53913434946831787443022849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71884579929109049924030465 53913434946831787443022849)
  ·
    refine ⟨40435076210123840582267137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53913434946831787443022849 40435076210123840582267137)
    ·
      refine ⟨30326307157592880436700353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40435076210123840582267137 30326307157592880436700353)
      ·
        refine ⟨22744730368194660327525265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30326307157592880436700353 22744730368194660327525265)
        ·
          refine ⟨17058547776145995245643949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22744730368194660327525265 17058547776145995245643949)
          ·
            refine ⟨6396955416054748217116481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17058547776145995245643949 6396955416054748217116481)
            ·
              refine ⟨4797716562041061162837361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6396955416054748217116481 4797716562041061162837361)
              ·
                refine ⟨3598287421530795872128021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797716562041061162837361 3598287421530795872128021)
                ·
                  refine ⟨168669722884256056506001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3598287421530795872128021 168669722884256056506001)
                  ·
                    rfl

theorem cell23_2956348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_2956348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956348 prefixEnd_2956348 := by exact prefixLift 2956348
  have htrace : WordTrace (prefixWord ++ tailWord_2956348) baseStart_2956348 baseEnd_2956348 := by
    simpa [prefixWord, tailWord_2956348, baseEnd_2956348] using wordTrace_append hprefix tailTrace_2956348
  have hstable : (prefixWord ++ tailWord_2956348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956348).length < 2 ^ (prefixWord ++ tailWord_2956348).sum := by decide
  have hdescent : baseEnd_2956348 < baseStart_2956348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956368 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2]
def baseStart_2956368 : Nat := 118140960795 + 2956368 * 2 ^ 59
def prefixEnd_2956368 : Nat := 4983230072969 + 3 ^ 40 * 2956368 * 2
def baseEnd_2956368 : Nat := 1518037775571394430303917

theorem tailTrace_2956368 : CollatzResearch.WordTrace tailWord_2956368 prefixEnd_2956368 1518037775571394430303917 := by
  unfold tailWord_2956368
  simp only [CollatzResearch.WordTrace]
  refine ⟨53913799676795559150886879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71885066235727412201182505 53913799676795559150886879)
  ·
    refine ⟨80870699515193338726330319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53913799676795559150886879 80870699515193338726330319)
    ·
      refine ⟨121306049272790008089495479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80870699515193338726330319 121306049272790008089495479)
      ·
        refine ⟨181959073909185012134243219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121306049272790008089495479 181959073909185012134243219)
        ·
          refine ⟨272938610863777518201364829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181959073909185012134243219 272938610863777518201364829)
          ·
            refine ⟨102351979073916569325511811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272938610863777518201364829 102351979073916569325511811)
            ·
              refine ⟨153527968610874853988267717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102351979073916569325511811 153527968610874853988267717)
              ·
                refine ⟨28786494114539035122800197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153527968610874853988267717 28786494114539035122800197)
                ·
                  refine ⟨5397467646476069085525037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28786494114539035122800197 5397467646476069085525037)
                  ·
                    refine ⟨2024050367428525907071889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5397467646476069085525037 2024050367428525907071889)
                    ·
                      refine ⟨1518037775571394430303917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024050367428525907071889 1518037775571394430303917)
                      ·
                        rfl

theorem cell23_2956368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2].length) (baseStart_2956368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956368 prefixEnd_2956368 := by exact prefixLift 2956368
  have htrace : WordTrace (prefixWord ++ tailWord_2956368) baseStart_2956368 baseEnd_2956368 := by
    simpa [prefixWord, tailWord_2956368, baseEnd_2956368] using wordTrace_append hprefix tailTrace_2956368
  have hstable : (prefixWord ++ tailWord_2956368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956368).length < 2 ^ (prefixWord ++ tailWord_2956368).sum := by decide
  have hdescent : baseEnd_2956368 < baseStart_2956368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956385 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2956385 : Nat := 118140960795 + 2956385 * 2 ^ 59
def prefixEnd_2956385 : Nat := 4983230072969 + 3 ^ 40 * 2956385 * 2
def baseEnd_2956385 : Nat := 1518046504742520863791339

theorem tailTrace_2956385 : CollatzResearch.WordTrace tailWord_2956385 prefixEnd_2956385 1518046504742520863791339 := by
  unfold tailWord_2956385
  simp only [CollatzResearch.WordTrace]
  refine ⟨107828219394529530205142609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71885479596353020136761739 107828219394529530205142609)
  ·
    refine ⟨80871164545897147653856957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107828219394529530205142609 80871164545897147653856957)
    ·
      refine ⟨30326686704711430370196359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80871164545897147653856957 30326686704711430370196359)
      ·
        refine ⟨45490030057067145555294539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30326686704711430370196359 45490030057067145555294539)
        ·
          refine ⟨68235045085600718332941809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45490030057067145555294539 68235045085600718332941809)
          ·
            refine ⟨51176283814200538749706357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68235045085600718332941809 51176283814200538749706357)
            ·
              refine ⟨4797776607581300507784971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51176283814200538749706357 4797776607581300507784971)
              ·
                refine ⟨7196664911371950761677457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797776607581300507784971 7196664911371950761677457)
                ·
                  refine ⟨5397498683528963071258093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7196664911371950761677457 5397498683528963071258093)
                  ·
                    refine ⟨2024062006323361151721785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5397498683528963071258093 2024062006323361151721785)
                    ·
                      refine ⟨1518046504742520863791339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024062006323361151721785 1518046504742520863791339)
                      ·
                        rfl

theorem cell23_2956385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2956385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956385 prefixEnd_2956385 := by exact prefixLift 2956385
  have htrace : WordTrace (prefixWord ++ tailWord_2956385) baseStart_2956385 baseEnd_2956385 := by
    simpa [prefixWord, tailWord_2956385, baseEnd_2956385] using wordTrace_append hprefix tailTrace_2956385
  have hstable : (prefixWord ++ tailWord_2956385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956385).length < 2 ^ (prefixWord ++ tailWord_2956385).sum := by decide
  have hdescent : baseEnd_2956385 < baseStart_2956385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956411 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_2956411 : Nat := 118140960795 + 2956411 * 2 ^ 59
def prefixEnd_2956411 : Nat := 4983230072969 + 3 ^ 40 * 2956411 * 2
def baseEnd_2956411 : Nat := 1518059855239537762066219

theorem tailTrace_2956411 : CollatzResearch.WordTrace tailWord_2956411 prefixEnd_2956411 1518059855239537762066219 := by
  unfold tailWord_2956411
  simp only [CollatzResearch.WordTrace]
  refine ⟨107829167692435336645589087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71886111794956891097059391 107829167692435336645589087)
  ·
    refine ⟨161743751538653004968383631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107829167692435336645589087 161743751538653004968383631)
    ·
      refine ⟨242615627307979507452575447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161743751538653004968383631 242615627307979507452575447)
      ·
        refine ⟨363923440961969261178863171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242615627307979507452575447 363923440961969261178863171)
        ·
          refine ⟨545885161442953891768294757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363923440961969261178863171 545885161442953891768294757)
          ·
            refine ⟨102353467770553854706555267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 545885161442953891768294757 102353467770553854706555267)
            ·
              refine ⟨153530201655830782059832901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102353467770553854706555267 153530201655830782059832901)
              ·
                refine ⟨28786912810468271636218669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153530201655830782059832901 28786912810468271636218669)
                ·
                  refine ⟨10795092303925601863582001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28786912810468271636218669 10795092303925601863582001)
                  ·
                    refine ⟨8096319227944201397686501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10795092303925601863582001 8096319227944201397686501)
                    ·
                      refine ⟨1518059855239537762066219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8096319227944201397686501 1518059855239537762066219)
                      ·
                        rfl

theorem cell23_2956411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_2956411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956411 prefixEnd_2956411 := by exact prefixLift 2956411
  have htrace : WordTrace (prefixWord ++ tailWord_2956411) baseStart_2956411 baseEnd_2956411 := by
    simpa [prefixWord, tailWord_2956411, baseEnd_2956411] using wordTrace_append hprefix tailTrace_2956411
  have hstable : (prefixWord ++ tailWord_2956411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956411).length < 2 ^ (prefixWord ++ tailWord_2956411).sum := by decide
  have hdescent : baseEnd_2956411 < baseStart_2956411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956448 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_2956448 : Nat := 118140960795 + 2956448 * 2 ^ 59
def prefixEnd_2956448 : Nat := 4983230072969 + 3 ^ 40 * 2956448 * 2
def baseEnd_2956448 : Nat := 1518078854023754117303549

theorem tailTrace_2956448 : CollatzResearch.WordTrace tailWord_2956448 prefixEnd_2956448 1518078854023754117303549 := by
  unfold tailWord_2956448
  simp only [CollatzResearch.WordTrace]
  refine ⟨53915258596650645982342999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71887011462200861309790665 53915258596650645982342999)
  ·
    refine ⟨80872887894975968973514499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53915258596650645982342999 80872887894975968973514499)
    ·
      refine ⟨121309331842463953460271749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80872887894975968973514499 121309331842463953460271749)
      ·
        refine ⟨22745499720461991273800953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121309331842463953460271749 22745499720461991273800953)
        ·
          refine ⟨17059124790346493455350715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22745499720461991273800953 17059124790346493455350715)
          ·
            refine ⟨25588687185519740183026073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17059124790346493455350715 25588687185519740183026073)
            ·
              refine ⟨19191515389139805137269555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25588687185519740183026073 19191515389139805137269555)
              ·
                refine ⟨28787273083709707705904333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19191515389139805137269555 28787273083709707705904333)
                ·
                  refine ⟨10795227406391140389714125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28787273083709707705904333 10795227406391140389714125)
                  ·
                    refine ⟨4048210277396677646142797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10795227406391140389714125 4048210277396677646142797)
                    ·
                      refine ⟨1518078854023754117303549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048210277396677646142797 1518078854023754117303549)
                      ·
                        rfl

theorem cell23_2956448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_2956448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956448 prefixEnd_2956448 := by exact prefixLift 2956448
  have htrace : WordTrace (prefixWord ++ tailWord_2956448) baseStart_2956448 baseEnd_2956448 := by
    simpa [prefixWord, tailWord_2956448, baseEnd_2956448] using wordTrace_append hprefix tailTrace_2956448
  have hstable : (prefixWord ++ tailWord_2956448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956448).length < 2 ^ (prefixWord ++ tailWord_2956448).sum := by decide
  have hdescent : baseEnd_2956448 < baseStart_2956448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956466 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_2956466 : Nat := 118140960795 + 2956466 * 2 ^ 59
def prefixEnd_2956466 : Nat := 4983230072969 + 3 ^ 40 * 2956466 * 2
def baseEnd_2956466 : Nat := 1518088096675535046878467

theorem tailTrace_2956466 : CollatzResearch.WordTrace tailWord_2956466 prefixEnd_2956466 1518088096675535046878467 := by
  unfold tailWord_2956466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957793426809020259710313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71887449138157387359227501 26957793426809020259710313)
  ·
    refine ⟨20218345070106765194782735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26957793426809020259710313 20218345070106765194782735)
    ·
      refine ⟨30327517605160147792174103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20218345070106765194782735 30327517605160147792174103)
      ·
        refine ⟨45491276407740221688261155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30327517605160147792174103 45491276407740221688261155)
        ·
          refine ⟨68236914611610332532391733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45491276407740221688261155 68236914611610332532391733)
          ·
            refine ⟨6397210744838468674911725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68236914611610332532391733 6397210744838468674911725)
            ·
              refine ⟨2398954029314425753091897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6397210744838468674911725 2398954029314425753091897)
              ·
                refine ⟨1799215521985819314818923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398954029314425753091897 1799215521985819314818923)
                ·
                  refine ⟨2698823282978728972228385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799215521985819314818923 2698823282978728972228385)
                  ·
                    refine ⟨2024117462234046729171289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698823282978728972228385 2024117462234046729171289)
                    ·
                      refine ⟨1518088096675535046878467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024117462234046729171289 1518088096675535046878467)
                      ·
                        rfl

theorem cell23_2956466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_2956466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956466 prefixEnd_2956466 := by exact prefixLift 2956466
  have htrace : WordTrace (prefixWord ++ tailWord_2956466) baseStart_2956466 baseEnd_2956466 := by
    simpa [prefixWord, tailWord_2956466, baseEnd_2956466] using wordTrace_append hprefix tailTrace_2956466
  have hstable : (prefixWord ++ tailWord_2956466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956466).length < 2 ^ (prefixWord ++ tailWord_2956466).sum := by decide
  have hdescent : baseEnd_2956466 < baseStart_2956466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956486 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2956486 : Nat := 118140960795 + 2956486 * 2 ^ 59
def prefixEnd_2956486 : Nat := 4983230072969 + 3 ^ 40 * 2956486 * 2
def baseEnd_2956486 : Nat := 1518098366288624968628375

theorem tailTrace_2956486 : CollatzResearch.WordTrace tailWord_2956486 prefixEnd_2956486 1518098366288624968628375 := by
  unfold tailWord_2956486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369746973973863264205291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71887935444775749636379541 3369746973973863264205291)
  ·
    refine ⟨5054620460960794896307937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369746973973863264205291 5054620460960794896307937)
    ·
      refine ⟨3790965345720596172230953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5054620460960794896307937 3790965345720596172230953)
      ·
        refine ⟨2843224009290447129173215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790965345720596172230953 2843224009290447129173215)
        ·
          refine ⟨4264836013935670693759823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843224009290447129173215 4264836013935670693759823)
          ·
            refine ⟨6397254020903506040639735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264836013935670693759823 6397254020903506040639735)
            ·
              refine ⟨9595881031355259060959603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397254020903506040639735 9595881031355259060959603)
              ·
                refine ⟨14393821547032888591439405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9595881031355259060959603 14393821547032888591439405)
                ·
                  refine ⟨5397683080137333221789777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14393821547032888591439405 5397683080137333221789777)
                  ·
                    refine ⟨4048262310102999916342333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397683080137333221789777 4048262310102999916342333)
                    ·
                      refine ⟨1518098366288624968628375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048262310102999916342333 1518098366288624968628375)
                      ·
                        rfl

theorem cell23_2956486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2956486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956486 prefixEnd_2956486 := by exact prefixLift 2956486
  have htrace : WordTrace (prefixWord ++ tailWord_2956486) baseStart_2956486 baseEnd_2956486 := by
    simpa [prefixWord, tailWord_2956486, baseEnd_2956486] using wordTrace_append hprefix tailTrace_2956486
  have hstable : (prefixWord ++ tailWord_2956486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956486).length < 2 ^ (prefixWord ++ tailWord_2956486).sum := by decide
  have hdescent : baseEnd_2956486 < baseStart_2956486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956525 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2956525 : Nat := 118140960795 + 2956525 * 2 ^ 59
def prefixEnd_2956525 : Nat := 4983230072969 + 3 ^ 40 * 2956525 * 2
def baseEnd_2956525 : Nat := 1518118392034150316040695

theorem tailTrace_2956525 : CollatzResearch.WordTrace tailWord_2956525 prefixEnd_2956525 1518118392034150316040695 := by
  unfold tailWord_2956525
  simp only [CollatzResearch.WordTrace]
  refine ⟨107833325614022334115239029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71888883742681556076826019 107833325614022334115239029)
  ·
    refine ⟨10109374276314593823303659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107833325614022334115239029 10109374276314593823303659)
    ·
      refine ⟨15164061414471890734955489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10109374276314593823303659 15164061414471890734955489)
      ·
        refine ⟨11373046060853918051216617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15164061414471890734955489 11373046060853918051216617)
        ·
          refine ⟨8529784545640438538412463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11373046060853918051216617 8529784545640438538412463)
          ·
            refine ⟨12794676818460657807618695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529784545640438538412463 12794676818460657807618695)
            ·
              refine ⟨19192015227690986711428043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12794676818460657807618695 19192015227690986711428043)
              ·
                refine ⟨28788022841536480067142065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19192015227690986711428043 28788022841536480067142065)
                ·
                  refine ⟨21591017131152360050356549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28788022841536480067142065 21591017131152360050356549)
                  ·
                    refine ⟨4048315712091067509441853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21591017131152360050356549 4048315712091067509441853)
                    ·
                      refine ⟨1518118392034150316040695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048315712091067509441853 1518118392034150316040695)
                      ·
                        rfl

theorem cell23_2956525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2956525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956525 prefixEnd_2956525 := by exact prefixLift 2956525
  have htrace : WordTrace (prefixWord ++ tailWord_2956525) baseStart_2956525 baseEnd_2956525 := by
    simpa [prefixWord, tailWord_2956525, baseEnd_2956525] using wordTrace_append hprefix tailTrace_2956525
  have hstable : (prefixWord ++ tailWord_2956525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956525).length < 2 ^ (prefixWord ++ tailWord_2956525).sum := by decide
  have hdescent : baseEnd_2956525 < baseStart_2956525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956608 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_2956608 : Nat := 118140960795 + 2956608 * 2 ^ 59
def prefixEnd_2956608 : Nat := 4983230072969 + 3 ^ 40 * 2956608 * 2
def baseEnd_2956608 : Nat := 1518161010928473491302813

theorem tailTrace_2956608 : CollatzResearch.WordTrace tailWord_2956608 prefixEnd_2956608 1518161010928473491302813 := by
  unfold tailWord_2956608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53918176436360819645255239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71890901915147759527006985 53918176436360819645255239)
  ·
    refine ⟨80877264654541229467882859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53918176436360819645255239 80877264654541229467882859)
    ·
      refine ⟨121315896981811844201824289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80877264654541229467882859 121315896981811844201824289)
      ·
        refine ⟨90986922736358883151368217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121315896981811844201824289 90986922736358883151368217)
        ·
          refine ⟨68240192052269162363526163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90986922736358883151368217 68240192052269162363526163)
          ·
            refine ⟨102360288078403743545289245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68240192052269162363526163 102360288078403743545289245)
            ·
              refine ⟨38385108029401403829483467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102360288078403743545289245 38385108029401403829483467)
              ·
                refine ⟨57577662044102105744225201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38385108029401403829483467 57577662044102105744225201)
                ·
                  refine ⟨43183246533076579308168901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57577662044102105744225201 43183246533076579308168901)
                  ·
                    refine ⟨8096858724951858620281669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43183246533076579308168901 8096858724951858620281669)
                    ·
                      refine ⟨1518161010928473491302813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8096858724951858620281669 1518161010928473491302813)
                      ·
                        rfl

theorem cell23_2956608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_2956608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956608 prefixEnd_2956608 := by exact prefixLift 2956608
  have htrace : WordTrace (prefixWord ++ tailWord_2956608) baseStart_2956608 baseEnd_2956608 := by
    simpa [prefixWord, tailWord_2956608, baseEnd_2956608] using wordTrace_append hprefix tailTrace_2956608
  have hstable : (prefixWord ++ tailWord_2956608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956608).length < 2 ^ (prefixWord ++ tailWord_2956608).sum := by decide
  have hdescent : baseEnd_2956608 < baseStart_2956608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956612 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2956612 : Nat := 118140960795 + 2956612 * 2 ^ 59
def prefixEnd_2956612 : Nat := 4983230072969 + 3 ^ 40 * 2956612 * 2
def baseEnd_2956612 : Nat := 1518163064851091475652795

theorem tailTrace_2956612 : CollatzResearch.WordTrace tailWord_2956612 prefixEnd_2956612 1518163064851091475652795 := by
  unfold tailWord_2956612
  simp only [CollatzResearch.WordTrace]
  refine ⟨53918249382353573986828045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71890999176471431982437393 53918249382353573986828045)
  ·
    refine ⟨20219343518382590245060517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53918249382353573986828045 20219343518382590245060517)
    ·
      refine ⟨3791126909696735670948847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20219343518382590245060517 3791126909696735670948847)
      ·
        refine ⟨5686690364545103506423271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791126909696735670948847 5686690364545103506423271)
        ·
          refine ⟨8530035546817655259634907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686690364545103506423271 8530035546817655259634907)
          ·
            refine ⟨12795053320226482889452361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530035546817655259634907 12795053320226482889452361)
            ·
              refine ⟨9596289990169862167089271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12795053320226482889452361 9596289990169862167089271)
              ·
                refine ⟨14394434985254793250633907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596289990169862167089271 14394434985254793250633907)
                ·
                  refine ⟨21591652477882189875950861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14394434985254793250633907 21591652477882189875950861)
                  ·
                    refine ⟨8096869679205821203481573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21591652477882189875950861 8096869679205821203481573)
                    ·
                      refine ⟨1518163064851091475652795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8096869679205821203481573 1518163064851091475652795)
                      ·
                        rfl

theorem cell23_2956612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2956612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956612 prefixEnd_2956612 := by exact prefixLift 2956612
  have htrace : WordTrace (prefixWord ++ tailWord_2956612) baseStart_2956612 baseEnd_2956612 := by
    simpa [prefixWord, tailWord_2956612, baseEnd_2956612] using wordTrace_append hprefix tailTrace_2956612
  have hstable : (prefixWord ++ tailWord_2956612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956612).length < 2 ^ (prefixWord ++ tailWord_2956612).sum := by decide
  have hdescent : baseEnd_2956612 < baseStart_2956612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956615 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_2956615 : Nat := 118140960795 + 2956615 * 2 ^ 59
def prefixEnd_2956615 : Nat := 4983230072969 + 3 ^ 40 * 2956615 * 2
def baseEnd_2956615 : Nat := 1518164605293054963915281

theorem tailTrace_2956615 : CollatzResearch.WordTrace tailWord_2956615 prefixEnd_2956615 1518164605293054963915281 := by
  unfold tailWord_2956615
  simp only [CollatzResearch.WordTrace]
  refine ⟨107836608183696279486015299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71891072122464186324010199 107836608183696279486015299)
  ·
    refine ⟨161754912275544419229022949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107836608183696279486015299 161754912275544419229022949)
    ·
      refine ⟨30329046051664578605441803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161754912275544419229022949 30329046051664578605441803)
      ·
        refine ⟨45493569077496867908162705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30329046051664578605441803 45493569077496867908162705)
        ·
          refine ⟨34120176808122650931122029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45493569077496867908162705 34120176808122650931122029)
          ·
            refine ⟨12795066303045994099170761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34120176808122650931122029 12795066303045994099170761)
            ·
              refine ⟨9596299727284495574378071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12795066303045994099170761 9596299727284495574378071)
              ·
                refine ⟨14394449590926743361567107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596299727284495574378071 14394449590926743361567107)
                ·
                  refine ⟨21591674386390115042350661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14394449590926743361567107 21591674386390115042350661)
                  ·
                    refine ⟨4048438947448146570440749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21591674386390115042350661 4048438947448146570440749)
                    ·
                      refine ⟨1518164605293054963915281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048438947448146570440749 1518164605293054963915281)
                      ·
                        rfl

theorem cell23_2956615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_2956615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956615 prefixEnd_2956615 := by exact prefixLift 2956615
  have htrace : WordTrace (prefixWord ++ tailWord_2956615) baseStart_2956615 baseEnd_2956615 := by
    simpa [prefixWord, tailWord_2956615, baseEnd_2956615] using wordTrace_append hprefix tailTrace_2956615
  have hstable : (prefixWord ++ tailWord_2956615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956615).length < 2 ^ (prefixWord ++ tailWord_2956615).sum := by decide
  have hdescent : baseEnd_2956615 < baseStart_2956615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956630 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2956630 : Nat := 118140960795 + 2956630 * 2 ^ 59
def prefixEnd_2956630 : Nat := 4983230072969 + 3 ^ 40 * 2956630 * 2
def baseEnd_2956630 : Nat := 168685811944763600580857

theorem tailTrace_2956630 : CollatzResearch.WordTrace tailWord_2956630 prefixEnd_2956630 168685811944763600580857 := by
  unfold tailWord_2956630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739822204915121065488209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71891436852427958031874229 6739822204915121065488209)
  ·
    refine ⟨5054866653686340799116157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6739822204915121065488209 5054866653686340799116157)
    ·
      refine ⟨1895574995132377799668559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5054866653686340799116157 1895574995132377799668559)
      ·
        refine ⟨2843362492698566699502839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895574995132377799668559 2843362492698566699502839)
        ·
          refine ⟨4265043739047850049254259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843362492698566699502839 4265043739047850049254259)
          ·
            refine ⟨6397565608571775073881389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265043739047850049254259 6397565608571775073881389)
            ·
              refine ⟨2399087103214415652705521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6397565608571775073881389 2399087103214415652705521)
              ·
                refine ⟨1799315327410811739529141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399087103214415652705521 1799315327410811739529141)
                ·
                  refine ⟨168685811944763600580857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799315327410811739529141 168685811944763600580857)
                  ·
                    rfl

theorem cell23_2956630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2956630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956630 prefixEnd_2956630 := by exact prefixLift 2956630
  have htrace : WordTrace (prefixWord ++ tailWord_2956630) baseStart_2956630 baseEnd_2956630 := by
    simpa [prefixWord, tailWord_2956630, baseEnd_2956630] using wordTrace_append hprefix tailTrace_2956630
  have hstable : (prefixWord ++ tailWord_2956630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956630).length < 2 ^ (prefixWord ++ tailWord_2956630).sum := by decide
  have hdescent : baseEnd_2956630 < baseStart_2956630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956652 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 6]
def baseStart_2956652 : Nat := 118140960795 + 2956652 * 2 ^ 59
def prefixEnd_2956652 : Nat := 4983230072969 + 3 ^ 40 * 2956652 * 2
def baseEnd_2956652 : Nat := 168687067119696813239179

theorem tailTrace_2956652 : CollatzResearch.WordTrace tailWord_2956652 prefixEnd_2956652 168687067119696813239179 := by
  unfold tailWord_2956652
  simp only [CollatzResearch.WordTrace]
  refine ⟨53918978842281117402556105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71891971789708156536741473 53918978842281117402556105)
  ·
    refine ⟨40439234131710838051917079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53918978842281117402556105 40439234131710838051917079)
    ·
      refine ⟨60658851197566257077875619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40439234131710838051917079 60658851197566257077875619)
      ·
        refine ⟨90988276796349385616813429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60658851197566257077875619 90988276796349385616813429)
        ·
          refine ⟨8530150949657754901576259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90988276796349385616813429 8530150949657754901576259)
          ·
            refine ⟨12795226424486632352364389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530150949657754901576259 12795226424486632352364389)
            ·
              refine ⟨2399104954591243566068323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12795226424486632352364389 2399104954591243566068323)
              ·
                refine ⟨3598657431886865349102485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399104954591243566068323 3598657431886865349102485)
                ·
                  refine ⟨168687067119696813239179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3598657431886865349102485 168687067119696813239179)
                  ·
                    rfl

theorem cell23_2956652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_2956652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956652 prefixEnd_2956652 := by exact prefixLift 2956652
  have htrace : WordTrace (prefixWord ++ tailWord_2956652) baseStart_2956652 baseEnd_2956652 := by
    simpa [prefixWord, tailWord_2956652, baseEnd_2956652] using wordTrace_append hprefix tailTrace_2956652
  have hstable : (prefixWord ++ tailWord_2956652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956652).length < 2 ^ (prefixWord ++ tailWord_2956652).sum := by decide
  have hdescent : baseEnd_2956652 < baseStart_2956652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956690 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2956690 : Nat := 118140960795 + 2956690 * 2 ^ 59
def prefixEnd_2956690 : Nat := 4983230072969 + 3 ^ 40 * 2956690 * 2
def baseEnd_2956690 : Nat := 506067705447380723492479

theorem tailTrace_2956690 : CollatzResearch.WordTrace tailWord_2956690 prefixEnd_2956690 506067705447380723492479 := by
  unfold tailWord_2956690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26959835914606141823748881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71892895772283044863330349 26959835914606141823748881)
  ·
    refine ⟨20219876935954606367811661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26959835914606141823748881 20219876935954606367811661)
    ·
      refine ⟨7582453850982977387929373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20219876935954606367811661 7582453850982977387929373)
      ·
        refine ⟨2843420194118616520473515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7582453850982977387929373 2843420194118616520473515)
        ·
          refine ⟨4265130291177924780710273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843420194118616520473515 4265130291177924780710273)
          ·
            refine ⟨3198847718383443585532705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4265130291177924780710273 3198847718383443585532705)
            ·
              refine ⟨2399135788787582689149529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3198847718383443585532705 2399135788787582689149529)
              ·
                refine ⟨1799351841590687016862147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399135788787582689149529 1799351841590687016862147)
                ·
                  refine ⟨2699027762386030525293221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799351841590687016862147 2699027762386030525293221)
                  ·
                    refine ⟨506067705447380723492479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2699027762386030525293221 506067705447380723492479)
                    ·
                      rfl

theorem cell23_2956690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2956690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956690 prefixEnd_2956690 := by exact prefixLift 2956690
  have htrace : WordTrace (prefixWord ++ tailWord_2956690) baseStart_2956690 baseEnd_2956690 := by
    simpa [prefixWord, tailWord_2956690, baseEnd_2956690] using wordTrace_append hprefix tailTrace_2956690
  have hstable : (prefixWord ++ tailWord_2956690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956690).length < 2 ^ (prefixWord ++ tailWord_2956690).sum := by decide
  have hdescent : baseEnd_2956690 < baseStart_2956690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956736 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 1, 2, 2]
def baseStart_2956736 : Nat := 118140960795 + 2956736 * 2 ^ 59
def prefixEnd_2956736 : Nat := 4983230072969 + 3 ^ 40 * 2956736 * 2
def baseEnd_2956736 : Nat := 1518226736452248990502225

theorem tailTrace_2956736 : CollatzResearch.WordTrace tailWord_2956736 prefixEnd_2956736 1518226736452248990502225 := by
  unfold tailWord_2956736
  simp only [CollatzResearch.WordTrace]
  refine ⟨53920510708128958575585031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71894014277505278100780041 53920510708128958575585031)
  ·
    refine ⟨80880766062193437863377547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53920510708128958575585031 80880766062193437863377547)
    ·
      refine ⟨121321149093290156795066321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80880766062193437863377547 121321149093290156795066321)
      ·
        refine ⟨90990861819967617596299741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121321149093290156795066321 90990861819967617596299741)
        ·
          refine ⟨34121573182487856598612403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90990861819967617596299741 34121573182487856598612403)
          ·
            refine ⟨51182359773731784897918605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34121573182487856598612403 51182359773731784897918605)
            ·
              refine ⟨19193384915149419336719477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51182359773731784897918605 19193384915149419336719477)
              ·
                refine ⟨1799379835795258062817451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19193384915149419336719477 1799379835795258062817451)
                ·
                  refine ⟨2699069753692887094226177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799379835795258062817451 2699069753692887094226177)
                  ·
                    refine ⟨2024302315269665320669633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2699069753692887094226177 2024302315269665320669633)
                    ·
                      refine ⟨1518226736452248990502225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024302315269665320669633 1518226736452248990502225)
                      ·
                        rfl

theorem cell23_2956736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_2956736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956736 prefixEnd_2956736 := by exact prefixLift 2956736
  have htrace : WordTrace (prefixWord ++ tailWord_2956736) baseStart_2956736 baseEnd_2956736 := by
    simpa [prefixWord, tailWord_2956736, baseEnd_2956736] using wordTrace_append hprefix tailTrace_2956736
  have hstable : (prefixWord ++ tailWord_2956736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956736).length < 2 ^ (prefixWord ++ tailWord_2956736).sum := by decide
  have hdescent : baseEnd_2956736 < baseStart_2956736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956739 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 1, 2, 3]
def baseStart_2956739 : Nat := 118140960795 + 2956739 * 2 ^ 59
def prefixEnd_2956739 : Nat := 4983230072969 + 3 ^ 40 * 2956739 * 2
def baseEnd_2956739 : Nat := 1518228276894212478764711

theorem tailTrace_2956739 : CollatzResearch.WordTrace tailWord_2956739 prefixEnd_2956739 1518228276894212478764711 := by
  unfold tailWord_2956739
  simp only [CollatzResearch.WordTrace]
  refine ⟨107841130835247048663529271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71894087223498032442352847 107841130835247048663529271)
  ·
    refine ⟨161761696252870572995293907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107841130835247048663529271 161761696252870572995293907)
    ·
      refine ⟨242642544379305859492940861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161761696252870572995293907 242642544379305859492940861)
      ·
        refine ⟨90990954142239697309852823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242642544379305859492940861 90990954142239697309852823)
        ·
          refine ⟨136486431213359545964779235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90990954142239697309852823 136486431213359545964779235)
          ·
            refine ⟨204729646820039318947168853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136486431213359545964779235 204729646820039318947168853)
            ·
              refine ⟨2399175548672335768912135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 204729646820039318947168853 2399175548672335768912135)
              ·
                refine ⟨3598763323008503653368203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399175548672335768912135 3598763323008503653368203)
                ·
                  refine ⟨5398144984512755480052305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598763323008503653368203 5398144984512755480052305)
                  ·
                    refine ⟨4048608738384566610039229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398144984512755480052305 4048608738384566610039229)
                    ·
                      refine ⟨1518228276894212478764711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048608738384566610039229 1518228276894212478764711)
                      ·
                        rfl

theorem cell23_2956739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_2956739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956739 prefixEnd_2956739 := by exact prefixLift 2956739
  have htrace : WordTrace (prefixWord ++ tailWord_2956739) baseStart_2956739 baseEnd_2956739 := by
    simpa [prefixWord, tailWord_2956739, baseEnd_2956739] using wordTrace_append hprefix tailTrace_2956739
  have hstable : (prefixWord ++ tailWord_2956739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956739).length < 2 ^ (prefixWord ++ tailWord_2956739).sum := by decide
  have hdescent : baseEnd_2956739 < baseStart_2956739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956752 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3]
def baseStart_2956752 : Nat := 118140960795 + 2956752 * 2 ^ 59
def prefixEnd_2956752 : Nat := 4983230072969 + 3 ^ 40 * 2956752 * 2
def baseEnd_2956752 : Nat := 1518234952142720927902151

theorem tailTrace_2956752 : CollatzResearch.WordTrace tailWord_2956752 prefixEnd_2956752 1518234952142720927902151 := by
  unfold tailWord_2956752
  simp only [CollatzResearch.WordTrace]
  refine ⟨53920802492099975941876255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71894403322799967922501673 53920802492099975941876255)
  ·
    refine ⟨80881203738149963912814383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53920802492099975941876255 80881203738149963912814383)
    ·
      refine ⟨121321805607224945869221575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80881203738149963912814383 121321805607224945869221575)
      ·
        refine ⟨181982708410837418803832363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121321805607224945869221575 181982708410837418803832363)
        ·
          refine ⟨272974062616256128205748545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181982708410837418803832363 272974062616256128205748545)
          ·
            refine ⟨204730546962192096154311409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272974062616256128205748545 204730546962192096154311409)
            ·
              refine ⟨153547910221644072115733557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204730546962192096154311409 153547910221644072115733557)
              ·
                refine ⟨14395116583279131760850021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153547910221644072115733557 14395116583279131760850021)
                ·
                  refine ⟨2699084359364837205159379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14395116583279131760850021 2699084359364837205159379)
                  ·
                    refine ⟨4048626539047255807739069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2699084359364837205159379 4048626539047255807739069)
                    ·
                      refine ⟨1518234952142720927902151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048626539047255807739069 1518234952142720927902151)
                      ·
                        rfl

theorem cell23_2956752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_2956752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956752 prefixEnd_2956752 := by exact prefixLift 2956752
  have htrace : WordTrace (prefixWord ++ tailWord_2956752) baseStart_2956752 baseEnd_2956752 := by
    simpa [prefixWord, tailWord_2956752, baseEnd_2956752] using wordTrace_append hprefix tailTrace_2956752
  have hstable : (prefixWord ++ tailWord_2956752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956752).length < 2 ^ (prefixWord ++ tailWord_2956752).sum := by decide
  have hdescent : baseEnd_2956752 < baseStart_2956752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956769 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2956769 : Nat := 118140960795 + 2956769 * 2 ^ 59
def prefixEnd_2956769 : Nat := 4983230072969 + 3 ^ 40 * 2956769 * 2
def baseEnd_2956769 : Nat := 1518243681313847361389573

theorem tailTrace_2956769 : CollatzResearch.WordTrace tailWord_2956769 prefixEnd_2956769 1518243681313847361389573 := by
  unfold tailWord_2956769
  simp only [CollatzResearch.WordTrace]
  refine ⟨107842225025138363787121361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71894816683425575858080907 107842225025138363787121361)
  ·
    refine ⟨80881668768853772840341021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107842225025138363787121361 80881668768853772840341021)
    ·
      refine ⟨30330625788320164815127883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80881668768853772840341021 30330625788320164815127883)
      ·
        refine ⟨45495938682480247222691825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30330625788320164815127883 45495938682480247222691825)
        ·
          refine ⟨34121954011860185417018869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45495938682480247222691825 34121954011860185417018869)
          ·
            refine ⟨3198933188611892382845519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34121954011860185417018869 3198933188611892382845519)
            ·
              refine ⟨4798399782917838574268279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198933188611892382845519 4798399782917838574268279)
              ·
                refine ⟨7197599674376757861402419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798399782917838574268279 7197599674376757861402419)
                ·
                  refine ⟨10796399511565136792103629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7197599674376757861402419 10796399511565136792103629)
                  ·
                    refine ⟨4048649816836926297038861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10796399511565136792103629 4048649816836926297038861)
                    ·
                      refine ⟨1518243681313847361389573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048649816836926297038861 1518243681313847361389573)
                      ·
                        rfl

theorem cell23_2956769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2956769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956769 prefixEnd_2956769 := by exact prefixLift 2956769
  have htrace : WordTrace (prefixWord ++ tailWord_2956769) baseStart_2956769 baseEnd_2956769 := by
    simpa [prefixWord, tailWord_2956769, baseEnd_2956769] using wordTrace_append hprefix tailTrace_2956769
  have hstable : (prefixWord ++ tailWord_2956769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956769).length < 2 ^ (prefixWord ++ tailWord_2956769).sum := by decide
  have hdescent : baseEnd_2956769 < baseStart_2956769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956795 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_2956795 : Nat := 118140960795 + 2956795 * 2 ^ 59
def prefixEnd_2956795 : Nat := 4983230072969 + 3 ^ 40 * 2956795 * 2
def baseEnd_2956795 : Nat := 1518257031810864259664453

theorem tailTrace_2956795 : CollatzResearch.WordTrace tailWord_2956795 prefixEnd_2956795 1518257031810864259664453 := by
  unfold tailWord_2956795
  simp only [CollatzResearch.WordTrace]
  refine ⟨107843173323044170227567839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71895448882029446818378559 107843173323044170227567839)
  ·
    refine ⟨161764759984566255341351759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107843173323044170227567839 161764759984566255341351759)
    ·
      refine ⟨242647139976849383012027639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161764759984566255341351759 242647139976849383012027639)
      ·
        refine ⟨363970709965274074518041459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242647139976849383012027639 363970709965274074518041459)
        ·
          refine ⟨545956064947911111777062189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363970709965274074518041459 545956064947911111777062189)
          ·
            refine ⟨204733524355466666916398321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 545956064947911111777062189 204733524355466666916398321)
            ·
              refine ⟨153550143266600000187298741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204733524355466666916398321 153550143266600000187298741)
              ·
                refine ⟨14395325931243750017559257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153550143266600000187298741 14395325931243750017559257)
                ·
                  refine ⟨10796494448432812513169443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14395325931243750017559257 10796494448432812513169443)
                  ·
                    refine ⟨16194741672649218769754165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10796494448432812513169443 16194741672649218769754165)
                    ·
                      refine ⟨1518257031810864259664453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16194741672649218769754165 1518257031810864259664453)
                      ·
                        rfl

theorem cell23_2956795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_2956795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956795 prefixEnd_2956795 := by exact prefixLift 2956795
  have htrace : WordTrace (prefixWord ++ tailWord_2956795) baseStart_2956795 baseEnd_2956795 := by
    simpa [prefixWord, tailWord_2956795, baseEnd_2956795] using wordTrace_append hprefix tailTrace_2956795
  have hstable : (prefixWord ++ tailWord_2956795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956795).length < 2 ^ (prefixWord ++ tailWord_2956795).sum := by decide
  have hdescent : baseEnd_2956795 < baseStart_2956795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956809 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 4, 2, 2]
def baseStart_2956809 : Nat := 118140960795 + 2956809 * 2 ^ 59
def prefixEnd_2956809 : Nat := 4983230072969 + 3 ^ 40 * 2956809 * 2
def baseEnd_2956809 : Nat := 1518264220540027204889389

theorem tailTrace_2956809 : CollatzResearch.WordTrace tailWord_2956809 prefixEnd_2956809 1518264220540027204889389 := by
  unfold tailWord_2956809
  simp only [CollatzResearch.WordTrace]
  refine ⟨107843683944993450618577481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71895789296662300412384987 107843683944993450618577481)
  ·
    refine ⟨80882762958745087963933111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107843683944993450618577481 80882762958745087963933111)
    ·
      refine ⟨121324144438117631945899667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80882762958745087963933111 121324144438117631945899667)
      ·
        refine ⟨181986216657176447918849501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121324144438117631945899667 181986216657176447918849501)
        ·
          refine ⟨68244831246441167969568563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181986216657176447918849501 68244831246441167969568563)
          ·
            refine ⟨102367246869661751954352845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68244831246441167969568563 102367246869661751954352845)
            ·
              refine ⟨38387717576123156982882317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102367246869661751954352845 38387717576123156982882317)
              ·
                refine ⟨14395394091046183868580869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38387717576123156982882317 14395394091046183868580869)
                ·
                  refine ⟨2699136392071159475358913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14395394091046183868580869 2699136392071159475358913)
                  ·
                    refine ⟨2024352294053369606519185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2699136392071159475358913 2024352294053369606519185)
                    ·
                      refine ⟨1518264220540027204889389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024352294053369606519185 1518264220540027204889389)
                      ·
                        rfl

theorem cell23_2956809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2, 2].length) (baseStart_2956809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956809 prefixEnd_2956809 := by exact prefixLift 2956809
  have htrace : WordTrace (prefixWord ++ tailWord_2956809) baseStart_2956809 baseEnd_2956809 := by
    simpa [prefixWord, tailWord_2956809, baseEnd_2956809] using wordTrace_append hprefix tailTrace_2956809
  have hstable : (prefixWord ++ tailWord_2956809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956809).length < 2 ^ (prefixWord ++ tailWord_2956809).sum := by decide
  have hdescent : baseEnd_2956809 < baseStart_2956809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956875 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 8]
def baseStart_2956875 : Nat := 118140960795 + 2956875 * 2 ^ 59
def prefixEnd_2956875 : Nat := 4983230072969 + 3 ^ 40 * 2956875 * 2
def baseEnd_2956875 : Nat := 506099370087741315554695

theorem tailTrace_2956875 : CollatzResearch.WordTrace tailWord_2956875 prefixEnd_2956875 506099370087741315554695 := by
  unfold tailWord_2956875
  simp only [CollatzResearch.WordTrace]
  refine ⟨107846091162754343890480079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71897394108502895926986719 107846091162754343890480079)
  ·
    refine ⟨161769136744131515835720119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107846091162754343890480079 161769136744131515835720119)
    ·
      refine ⟨242653705116197273753580179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161769136744131515835720119 242653705116197273753580179)
      ·
        refine ⟨363980557674295910630370269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242653705116197273753580179 363980557674295910630370269)
        ·
          refine ⟨136492709127860966486388851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363980557674295910630370269 136492709127860966486388851)
          ·
            refine ⟨204739063691791449729583277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136492709127860966486388851 204739063691791449729583277)
            ·
              refine ⟨76777148884421793648593729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204739063691791449729583277 76777148884421793648593729)
              ·
                refine ⟨57582861663316345236445297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76777148884421793648593729 57582861663316345236445297)
                ·
                  refine ⟨43187146247487258927333973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57582861663316345236445297 43187146247487258927333973)
                  ·
                    refine ⟨506099370087741315554695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43187146247487258927333973 506099370087741315554695)
                    ·
                      rfl

theorem cell23_2956875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_2956875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956875 prefixEnd_2956875 := by exact prefixLift 2956875
  have htrace : WordTrace (prefixWord ++ tailWord_2956875) baseStart_2956875 baseEnd_2956875 := by
    simpa [prefixWord, tailWord_2956875, baseEnd_2956875] using wordTrace_append hprefix tailTrace_2956875
  have hstable : (prefixWord ++ tailWord_2956875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956875).length < 2 ^ (prefixWord ++ tailWord_2956875).sum := by decide
  have hdescent : baseEnd_2956875 < baseStart_2956875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956899 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2956899 : Nat := 118140960795 + 2956899 * 2 ^ 59
def prefixEnd_2956899 : Nat := 4983230072969 + 3 ^ 40 * 2956899 * 2
def baseEnd_2956899 : Nat := 1518310433798931852763975

theorem tailTrace_2956899 : CollatzResearch.WordTrace tailWord_2956899 prefixEnd_2956899 1518310433798931852763975 := by
  unfold tailWord_2956899
  simp only [CollatzResearch.WordTrace]
  refine ⟨107846966514667395989353751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71897977676444930659569167 107846966514667395989353751)
  ·
    refine ⟨161770449772001093984030627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107846966514667395989353751 161770449772001093984030627)
    ·
      refine ⟨242655674658001640976045941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161770449772001093984030627 242655674658001640976045941)
      ·
        refine ⟨22748969499187653841504307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242655674658001640976045941 22748969499187653841504307)
        ·
          refine ⟨34123454248781480762256461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22748969499187653841504307 34123454248781480762256461)
          ·
            refine ⟨12796295343293055285846173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34123454248781480762256461 12796295343293055285846173)
            ·
              refine ⟨4798610753734895732192315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12796295343293055285846173 4798610753734895732192315)
              ·
                refine ⟨7197916130602343598288473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798610753734895732192315 7197916130602343598288473)
                ·
                  refine ⟨5398437097951757698716355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7197916130602343598288473 5398437097951757698716355)
                  ·
                    refine ⟨8097655646927636548074533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5398437097951757698716355 8097655646927636548074533)
                    ·
                      refine ⟨1518310433798931852763975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8097655646927636548074533 1518310433798931852763975)
                      ·
                        rfl

theorem cell23_2956899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2956899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956899 prefixEnd_2956899 := by exact prefixLift 2956899
  have htrace : WordTrace (prefixWord ++ tailWord_2956899) baseStart_2956899 baseEnd_2956899 := by
    simpa [prefixWord, tailWord_2956899, baseEnd_2956899] using wordTrace_append hprefix tailTrace_2956899
  have hstable : (prefixWord ++ tailWord_2956899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956899).length < 2 ^ (prefixWord ++ tailWord_2956899).sum := by decide
  have hdescent : baseEnd_2956899 < baseStart_2956899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956912 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_2956912 : Nat := 118140960795 + 2956912 * 2 ^ 59
def prefixEnd_2956912 : Nat := 4983230072969 + 3 ^ 40 * 2956912 * 2
def baseEnd_2956912 : Nat := 1518317109047440301901415

theorem tailTrace_2956912 : CollatzResearch.WordTrace tailWord_2956912 prefixEnd_2956912 1518317109047440301901415 := by
  unfold tailWord_2956912
  simp only [CollatzResearch.WordTrace]
  refine ⟨53923720331810149604788495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71898293775746866139717993 53923720331810149604788495)
  ·
    refine ⟨80885580497715224407182743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53923720331810149604788495 80885580497715224407182743)
    ·
      refine ⟨121328370746572836610774115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80885580497715224407182743 121328370746572836610774115)
      ·
        refine ⟨181992556119859254916161173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121328370746572836610774115 181992556119859254916161173)
        ·
          refine ⟨8530901068118402574195055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181992556119859254916161173 8530901068118402574195055)
          ·
            refine ⟨12796351602177603861292583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530901068118402574195055 12796351602177603861292583)
            ·
              refine ⟨19194527403266405791938875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12796351602177603861292583 19194527403266405791938875)
              ·
                refine ⟨28791791104899608687908313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19194527403266405791938875 28791791104899608687908313)
                ·
                  refine ⟨21593843328674706515931235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28791791104899608687908313 21593843328674706515931235)
                  ·
                    refine ⟨32390764993012059773896853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21593843328674706515931235 32390764993012059773896853)
                    ·
                      refine ⟨1518317109047440301901415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32390764993012059773896853 1518317109047440301901415)
                      ·
                        rfl

theorem cell23_2956912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_2956912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956912 prefixEnd_2956912 := by exact prefixLift 2956912
  have htrace : WordTrace (prefixWord ++ tailWord_2956912) baseStart_2956912 baseEnd_2956912 := by
    simpa [prefixWord, tailWord_2956912, baseEnd_2956912] using wordTrace_append hprefix tailTrace_2956912
  have hstable : (prefixWord ++ tailWord_2956912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956912).length < 2 ^ (prefixWord ++ tailWord_2956912).sum := by decide
  have hdescent : baseEnd_2956912 < baseStart_2956912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956922 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_2956922 : Nat := 118140960795 + 2956922 * 2 ^ 59
def prefixEnd_2956922 : Nat := 4983230072969 + 3 ^ 40 * 2956922 * 2
def baseEnd_2956922 : Nat := 168702471539331695864041

theorem tailTrace_2956922 : CollatzResearch.WordTrace tailWord_2956922 prefixEnd_2956922 168702471539331695864041 := by
  unfold tailWord_2956922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26961951348396017729360255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71898536929056047278294013 26961951348396017729360255)
  ·
    refine ⟨40442927022594026594040383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26961951348396017729360255 40442927022594026594040383)
    ·
      refine ⟨60664390533891039891060575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40442927022594026594040383 60664390533891039891060575)
      ·
        refine ⟨90996585800836559836590863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60664390533891039891060575 90996585800836559836590863)
        ·
          refine ⟨136494878701254839754886295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90996585800836559836590863 136494878701254839754886295)
          ·
            refine ⟨204742318051882259632329443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136494878701254839754886295 204742318051882259632329443)
            ·
              refine ⟨307113477077823389448494165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204742318051882259632329443 307113477077823389448494165)
              ·
                refine ⟨3598986059505742845099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 307113477077823389448494165 3598986059505742845099541)
                ·
                  refine ⟨168702471539331695864041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3598986059505742845099541 168702471539331695864041)
                  ·
                    rfl

theorem cell23_2956922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_2956922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956922 prefixEnd_2956922 := by exact prefixLift 2956922
  have htrace : WordTrace (prefixWord ++ tailWord_2956922) baseStart_2956922 baseEnd_2956922 := by
    simpa [prefixWord, tailWord_2956922, baseEnd_2956922] using wordTrace_append hprefix tailTrace_2956922
  have hstable : (prefixWord ++ tailWord_2956922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956922).length < 2 ^ (prefixWord ++ tailWord_2956922).sum := by decide
  have hdescent : baseEnd_2956922 < baseStart_2956922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956939 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 6]
def baseStart_2956939 : Nat := 118140960795 + 2956939 * 2 ^ 59
def prefixEnd_2956939 : Nat := 4983230072969 + 3 ^ 40 * 2956939 * 2
def baseEnd_2956939 : Nat := 168703441447234632918199

theorem tailTrace_2956939 : CollatzResearch.WordTrace tailWord_2956939 prefixEnd_2956939 168703441447234632918199 := by
  unfold tailWord_2956939
  simp only [CollatzResearch.WordTrace]
  refine ⟨107848425434522482820809871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71898950289681655213873247 107848425434522482820809871)
  ·
    refine ⟨161772638151783724231214807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107848425434522482820809871 161772638151783724231214807)
    ·
      refine ⟨242658957227675586346822211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161772638151783724231214807 242658957227675586346822211)
      ·
        refine ⟨363988435841513379520233317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242658957227675586346822211 363988435841513379520233317)
        ·
          refine ⟨68247831720283758660043747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363988435841513379520233317 68247831720283758660043747)
          ·
            refine ⟨102371747580425637990065621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68247831720283758660043747 102371747580425637990065621)
            ·
              refine ⟨2399337833916225890392163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102371747580425637990065621 2399337833916225890392163)
              ·
                refine ⟨3599006750874338835588245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399337833916225890392163 3599006750874338835588245)
                ·
                  refine ⟨168703441447234632918199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3599006750874338835588245 168703441447234632918199)
                  ·
                    rfl

theorem cell23_2956939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 6].length) (baseStart_2956939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956939 prefixEnd_2956939 := by exact prefixLift 2956939
  have htrace : WordTrace (prefixWord ++ tailWord_2956939) baseStart_2956939 baseEnd_2956939 := by
    simpa [prefixWord, tailWord_2956939, baseEnd_2956939] using wordTrace_append hprefix tailTrace_2956939
  have hstable : (prefixWord ++ tailWord_2956939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956939).length < 2 ^ (prefixWord ++ tailWord_2956939).sum := by decide
  have hdescent : baseEnd_2956939 < baseStart_2956939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956983 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_2956983 : Nat := 118140960795 + 2956983 * 2 ^ 59
def prefixEnd_2956983 : Nat := 4983230072969 + 3 ^ 40 * 2956983 * 2
def baseEnd_2956983 : Nat := 1518353566173909524113589

theorem tailTrace_2956983 : CollatzResearch.WordTrace tailWord_2956983 prefixEnd_2956983 1518353566173909524113589 := by
  unfold tailWord_2956983
  simp only [CollatzResearch.WordTrace]
  refine ⟨107850030246363078335411603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71900020164242052223607735 107850030246363078335411603)
  ·
    refine ⟨161775045369544617503117405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107850030246363078335411603 161775045369544617503117405)
    ·
      refine ⟨60665642013579231563669027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161775045369544617503117405 60665642013579231563669027)
      ·
        refine ⟨90998463020368847345503541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60665642013579231563669027 90998463020368847345503541)
        ·
          refine ⟨8531105908159579438640957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90998463020368847345503541 8531105908159579438640957)
          ·
            refine ⟨3199164715559842289490359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8531105908159579438640957 3199164715559842289490359)
            ·
              refine ⟨4798747073339763434235539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199164715559842289490359 4798747073339763434235539)
              ·
                refine ⟨7198120610009645151353309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798747073339763434235539 7198120610009645151353309)
                ·
                  refine ⟨2699295228753616931757491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7198120610009645151353309 2699295228753616931757491)
                  ·
                    refine ⟨4048942843130425397636237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2699295228753616931757491 4048942843130425397636237)
                    ·
                      refine ⟨1518353566173909524113589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4048942843130425397636237 1518353566173909524113589)
                      ·
                        rfl

theorem cell23_2956983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_2956983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956983 prefixEnd_2956983 := by exact prefixLift 2956983
  have htrace : WordTrace (prefixWord ++ tailWord_2956983) baseStart_2956983 baseEnd_2956983 := by
    simpa [prefixWord, tailWord_2956983, baseEnd_2956983] using wordTrace_append hprefix tailTrace_2956983
  have hstable : (prefixWord ++ tailWord_2956983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956983).length < 2 ^ (prefixWord ++ tailWord_2956983).sum := by decide
  have hdescent : baseEnd_2956983 < baseStart_2956983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956989 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2956989 : Nat := 118140960795 + 2956989 * 2 ^ 59
def prefixEnd_2956989 : Nat := 4983230072969 + 3 ^ 40 * 2956989 * 2
def baseEnd_2956989 : Nat := 1518356647057836500638561

theorem tailTrace_2956989 : CollatzResearch.WordTrace tailWord_2956989 prefixEnd_2956989 1518356647057836500638561 := by
  unfold tailWord_2956989
  simp only [CollatzResearch.WordTrace]
  refine ⟨107850249084341341360130021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71900166056227560906753347 107850249084341341360130021)
  ·
    refine ⟨20221921703314001505024379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107850249084341341360130021 20221921703314001505024379)
    ·
      refine ⟨30332882554971002257536569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20221921703314001505024379 30332882554971002257536569)
      ·
        refine ⟨22749661916228251693152427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30332882554971002257536569 22749661916228251693152427)
        ·
          refine ⟨34124492874342377539728641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22749661916228251693152427 34124492874342377539728641)
          ·
            refine ⟨25593369655756783154796481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34124492874342377539728641 25593369655756783154796481)
            ·
              refine ⟨19195027241817587366097361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25593369655756783154796481 19195027241817587366097361)
              ·
                refine ⟨14396270431363190524573021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19195027241817587366097361 14396270431363190524573021)
                ·
                  refine ⟨5398601411761196446714883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14396270431363190524573021 5398601411761196446714883)
                  ·
                    refine ⟨8097902117641794670072325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5398601411761196446714883 8097902117641794670072325)
                    ·
                      refine ⟨1518356647057836500638561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8097902117641794670072325 1518356647057836500638561)
                      ·
                        rfl

theorem cell23_2956989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2956989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2956989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2956989 prefixEnd_2956989 := by exact prefixLift 2956989
  have htrace : WordTrace (prefixWord ++ tailWord_2956989) baseStart_2956989 baseEnd_2956989 := by
    simpa [prefixWord, tailWord_2956989, baseEnd_2956989] using wordTrace_append hprefix tailTrace_2956989
  have hstable : (prefixWord ++ tailWord_2956989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956989).length < 2 ^ (prefixWord ++ tailWord_2956989).sum := by decide
  have hdescent : baseEnd_2956989 < baseStart_2956989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957020 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2957020 : Nat := 118140960795 + 2957020 * 2 ^ 59
def prefixEnd_2957020 : Nat := 4983230072969 + 3 ^ 40 * 2957020 * 2
def baseEnd_2957020 : Nat := 506124188319375293116973

theorem tailTrace_2957020 : CollatzResearch.WordTrace tailWord_2957020 prefixEnd_2957020 506124188319375293116973 := by
  unfold tailWord_2957020
  simp only [CollatzResearch.WordTrace]
  refine ⟨53925689873614516827254257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71900919831486022436339009 53925689873614516827254257)
  ·
    refine ⟨40444267405210887620440693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53925689873614516827254257 40444267405210887620440693)
    ·
      refine ⟨3791650069238520714416315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40444267405210887620440693 3791650069238520714416315)
      ·
        refine ⟨5687475103857781071624473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791650069238520714416315 5687475103857781071624473)
        ·
          refine ⟨4265606327893335803718355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5687475103857781071624473 4265606327893335803718355)
          ·
            refine ⟨6398409491840003705577533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265606327893335803718355 6398409491840003705577533)
            ·
              refine ⟨2399403559440001389591575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6398409491840003705577533 2399403559440001389591575)
              ·
                refine ⟨3599105339160002084387363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399403559440001389591575 3599105339160002084387363)
                ·
                  refine ⟨5398658008740003126581045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599105339160002084387363 5398658008740003126581045)
                  ·
                    refine ⟨506124188319375293116973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5398658008740003126581045 506124188319375293116973)
                    ·
                      rfl

theorem cell23_2957020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2957020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957020 prefixEnd_2957020 := by exact prefixLift 2957020
  have htrace : WordTrace (prefixWord ++ tailWord_2957020) baseStart_2957020 baseEnd_2957020 := by
    simpa [prefixWord, tailWord_2957020, baseEnd_2957020] using wordTrace_append hprefix tailTrace_2957020
  have hstable : (prefixWord ++ tailWord_2957020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957020).length < 2 ^ (prefixWord ++ tailWord_2957020).sum := by decide
  have hdescent : baseEnd_2957020 < baseStart_2957020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957039 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_2957039 : Nat := 118140960795 + 2957039 * 2 ^ 59
def prefixEnd_2957039 : Nat := 4983230072969 + 3 ^ 40 * 2957039 * 2
def baseEnd_2957039 : Nat := 1518382321090561305013331

theorem tailTrace_2957039 : CollatzResearch.WordTrace tailWord_2957039 prefixEnd_2957039 1518382321090561305013331 := by
  unfold tailWord_2957039
  simp only [CollatzResearch.WordTrace]
  refine ⟨107852072734160199899450171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71901381822773466599633447 107852072734160199899450171)
  ·
    refine ⟨161778109101240299849175257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107852072734160199899450171 161778109101240299849175257)
    ·
      refine ⟨121333581825930224886881443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161778109101240299849175257 121333581825930224886881443)
      ·
        refine ⟨182000372738895337330322165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121333581825930224886881443 182000372738895337330322165)
        ·
          refine ⟨17062534944271437874717703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182000372738895337330322165 17062534944271437874717703)
          ·
            refine ⟨25593802416407156812076555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17062534944271437874717703 25593802416407156812076555)
            ·
              refine ⟨38390703624610735218114833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25593802416407156812076555 38390703624610735218114833)
              ·
                refine ⟨28793027718458051413586125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38390703624610735218114833 28793027718458051413586125)
                ·
                  refine ⟨10797385394421769280094797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28793027718458051413586125 10797385394421769280094797)
                  ·
                    refine ⟨4049019522908163480035549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10797385394421769280094797 4049019522908163480035549)
                    ·
                      refine ⟨1518382321090561305013331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4049019522908163480035549 1518382321090561305013331)
                      ·
                        rfl

theorem cell23_2957039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_2957039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957039 prefixEnd_2957039 := by exact prefixLift 2957039
  have htrace : WordTrace (prefixWord ++ tailWord_2957039) baseStart_2957039 baseEnd_2957039 := by
    simpa [prefixWord, tailWord_2957039, baseEnd_2957039] using wordTrace_append hprefix tailTrace_2957039
  have hstable : (prefixWord ++ tailWord_2957039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957039).length < 2 ^ (prefixWord ++ tailWord_2957039).sum := by decide
  have hdescent : baseEnd_2957039 < baseStart_2957039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957046 : List Nat := [5, 1, 1, 1, 1, 5, 1, 8]
def baseStart_2957046 : Nat := 118140960795 + 2957046 * 2 ^ 59
def prefixEnd_2957046 : Nat := 4983230072969 + 3 ^ 40 * 2957046 * 2
def baseEnd_2957046 : Nat := 56236515387227510282437

theorem tailTrace_2957046 : CollatzResearch.WordTrace tailWord_2957046 prefixEnd_2957046 56236515387227510282437 := by
  unfold tailWord_2957046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740770502820927505934687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71901552030089893396636661 6740770502820927505934687)
  ·
    refine ⟨10111155754231391258902031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6740770502820927505934687 10111155754231391258902031)
    ·
      refine ⟨15166733631347086888353047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10111155754231391258902031 15166733631347086888353047)
      ·
        refine ⟨22750100447020630332529571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15166733631347086888353047 22750100447020630332529571)
        ·
          refine ⟨34125150670530945498794357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22750100447020630332529571 34125150670530945498794357)
          ·
            refine ⟨3199232875362276140511971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34125150670530945498794357 3199232875362276140511971)
            ·
              refine ⟨4798849313043414210767957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199232875362276140511971 4798849313043414210767957)
              ·
                refine ⟨56236515387227510282437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4798849313043414210767957 56236515387227510282437)
                ·
                  rfl

theorem cell23_2957046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_2957046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957046 prefixEnd_2957046 := by exact prefixLift 2957046
  have htrace : WordTrace (prefixWord ++ tailWord_2957046) baseStart_2957046 baseEnd_2957046 := by
    simpa [prefixWord, tailWord_2957046, baseEnd_2957046] using wordTrace_append hprefix tailTrace_2957046
  have hstable : (prefixWord ++ tailWord_2957046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957046).length < 2 ^ (prefixWord ++ tailWord_2957046).sum := by decide
  have hdescent : baseEnd_2957046 < baseStart_2957046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957074 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2957074 : Nat := 118140960795 + 2957074 * 2 ^ 59
def prefixEnd_2957074 : Nat := 4983230072969 + 3 ^ 40 * 2957074 * 2
def baseEnd_2957074 : Nat := 1518400292913468668075671

theorem tailTrace_2957074 : CollatzResearch.WordTrace tailWord_2957074 prefixEnd_2957074 1518400292913468668075671 := by
  unfold tailWord_2957074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26963337322258350219243569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71902232859355600584649517 26963337322258350219243569)
  ·
    refine ⟨20222502991693762664432677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26963337322258350219243569 20222502991693762664432677)
    ·
      refine ⟨3791719310942580499581127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20222502991693762664432677 3791719310942580499581127)
      ·
        refine ⟨5687578966413870749371691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791719310942580499581127 5687578966413870749371691)
        ·
          refine ⟨8531368449620806124057537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5687578966413870749371691 8531368449620806124057537)
          ·
            refine ⟨6398526337215604593043153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8531368449620806124057537 6398526337215604593043153)
            ·
              refine ⟨4798894752911703444782365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398526337215604593043153 4798894752911703444782365)
              ·
                refine ⟨1799585532341888791793387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4798894752911703444782365 1799585532341888791793387)
                ·
                  refine ⟨2699378298512833187690081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799585532341888791793387 2699378298512833187690081)
                  ·
                    refine ⟨2024533723884624890767561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2699378298512833187690081 2024533723884624890767561)
                    ·
                      refine ⟨1518400292913468668075671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024533723884624890767561 1518400292913468668075671)
                      ·
                        rfl

theorem cell23_2957074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2957074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957074 prefixEnd_2957074 := by exact prefixLift 2957074
  have htrace : WordTrace (prefixWord ++ tailWord_2957074) baseStart_2957074 baseEnd_2957074 := by
    simpa [prefixWord, tailWord_2957074, baseEnd_2957074] using wordTrace_append hprefix tailTrace_2957074
  have hstable : (prefixWord ++ tailWord_2957074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957074).length < 2 ^ (prefixWord ++ tailWord_2957074).sum := by decide
  have hdescent : baseEnd_2957074 < baseStart_2957074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957089 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2957089 : Nat := 118140960795 + 2957089 * 2 ^ 59
def prefixEnd_2957089 : Nat := 4983230072969 + 3 ^ 40 * 2957089 * 2
def baseEnd_2957089 : Nat := 506135998374428703129367

theorem tailTrace_2957089 : CollatzResearch.WordTrace tailWord_2957089 prefixEnd_2957089 506135998374428703129367 := by
  unfold tailWord_2957089
  simp only [CollatzResearch.WordTrace]
  refine ⟨107853896383979058438770321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71902597589319372292513547 107853896383979058438770321)
  ·
    refine ⟨80890422287984293829077741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107853896383979058438770321 80890422287984293829077741)
    ·
      refine ⟨30333908357994110185904153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80890422287984293829077741 30333908357994110185904153)
      ·
        refine ⟨22750431268495582639428115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30333908357994110185904153 22750431268495582639428115)
        ·
          refine ⟨34125646902743373959142173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22750431268495582639428115 34125646902743373959142173)
          ·
            refine ⟨12797117588528765234678315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34125646902743373959142173 12797117588528765234678315)
            ·
              refine ⟨19195676382793147852017473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12797117588528765234678315 19195676382793147852017473)
              ·
                refine ⟨14396757287094860889013105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19195676382793147852017473 14396757287094860889013105)
                ·
                  refine ⟨10797567965321145666759829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14396757287094860889013105 10797567965321145666759829)
                  ·
                    refine ⟨506135998374428703129367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10797567965321145666759829 506135998374428703129367)
                    ·
                      rfl

theorem cell23_2957089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2957089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957089 prefixEnd_2957089 := by exact prefixLift 2957089
  have htrace : WordTrace (prefixWord ++ tailWord_2957089) baseStart_2957089 baseEnd_2957089 := by
    simpa [prefixWord, tailWord_2957089, baseEnd_2957089] using wordTrace_append hprefix tailTrace_2957089
  have hstable : (prefixWord ++ tailWord_2957089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957089).length < 2 ^ (prefixWord ++ tailWord_2957089).sum := by decide
  have hdescent : baseEnd_2957089 < baseStart_2957089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957133 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2957133 : Nat := 118140960795 + 2957133 * 2 ^ 59
def prefixEnd_2957133 : Nat := 4983230072969 + 3 ^ 40 * 2957133 * 2
def baseEnd_2957133 : Nat := 1518430588272083937237899

theorem tailTrace_2957133 : CollatzResearch.WordTrace tailWord_2957133 prefixEnd_2957133 1518430588272083937237899 := by
  unfold tailWord_2957133
  simp only [CollatzResearch.WordTrace]
  refine ⟨107855501195819653953372053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71903667463879769302248035 107855501195819653953372053)
  ·
    refine ⟨5055726618554046279064315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107855501195819653953372053 5055726618554046279064315)
    ·
      refine ⟨7583589927831069418596473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055726618554046279064315 7583589927831069418596473)
      ·
        refine ⟨5687692445873302063947355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7583589927831069418596473 5687692445873302063947355)
        ·
          refine ⟨8531538668809953095921033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5687692445873302063947355 8531538668809953095921033)
          ·
            refine ⟨6398654001607464821940775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8531538668809953095921033 6398654001607464821940775)
            ·
              refine ⟨9597981002411197232911163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6398654001607464821940775 9597981002411197232911163)
              ·
                refine ⟨14396971503616795849366745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9597981002411197232911163 14396971503616795849366745)
                ·
                  refine ⟨10797728627712596887025059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14396971503616795849366745 10797728627712596887025059)
                  ·
                    refine ⟨16196592941568895330537589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10797728627712596887025059 16196592941568895330537589)
                    ·
                      refine ⟨1518430588272083937237899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16196592941568895330537589 1518430588272083937237899)
                      ·
                        rfl

theorem cell23_2957133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2957133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957133 prefixEnd_2957133 := by exact prefixLift 2957133
  have htrace : WordTrace (prefixWord ++ tailWord_2957133) baseStart_2957133 baseEnd_2957133 := by
    simpa [prefixWord, tailWord_2957133, baseEnd_2957133] using wordTrace_append hprefix tailTrace_2957133
  have hstable : (prefixWord ++ tailWord_2957133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957133).length < 2 ^ (prefixWord ++ tailWord_2957133).sum := by decide
  have hdescent : baseEnd_2957133 < baseStart_2957133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957153 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 5]
def baseStart_2957153 : Nat := 118140960795 + 2957153 * 2 ^ 59
def prefixEnd_2957153 : Nat := 4983230072969 + 3 ^ 40 * 2957153 * 2
def baseEnd_2957153 : Nat := 168715650876130428776423

theorem tailTrace_2957153 : CollatzResearch.WordTrace tailWord_2957153 prefixEnd_2957153 168715650876130428776423 := by
  unfold tailWord_2957153
  simp only [CollatzResearch.WordTrace]
  refine ⟨107856230655747197369100113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71904153770498131579400075 107856230655747197369100113)
  ·
    refine ⟨80892172991810398026825085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107856230655747197369100113 80892172991810398026825085)
    ·
      refine ⟨30334564871928899260059407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80892172991810398026825085 30334564871928899260059407)
      ·
        refine ⟨45501847307893348890089111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30334564871928899260059407 45501847307893348890089111)
        ·
          refine ⟨68252770961840023335133667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45501847307893348890089111 68252770961840023335133667)
          ·
            refine ⟨102379156442760035002700501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68252770961840023335133667 102379156442760035002700501)
            ·
              refine ⟨2399511479127188320375793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102379156442760035002700501 2399511479127188320375793)
              ·
                refine ⟨1799633609345391240281845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399511479127188320375793 1799633609345391240281845)
                ·
                  refine ⟨168715650876130428776423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799633609345391240281845 168715650876130428776423)
                  ·
                    rfl

theorem cell23_2957153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 5].length) (baseStart_2957153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957153 prefixEnd_2957153 := by exact prefixLift 2957153
  have htrace : WordTrace (prefixWord ++ tailWord_2957153) baseStart_2957153 baseEnd_2957153 := by
    simpa [prefixWord, tailWord_2957153, baseEnd_2957153] using wordTrace_append hprefix tailTrace_2957153
  have hstable : (prefixWord ++ tailWord_2957153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957153).length < 2 ^ (prefixWord ++ tailWord_2957153).sum := by decide
  have hdescent : baseEnd_2957153 < baseStart_2957153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957199 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_2957199 : Nat := 118140960795 + 2957199 * 2 ^ 59
def prefixEnd_2957199 : Nat := 4983230072969 + 3 ^ 40 * 2957199 * 2
def baseEnd_2957199 : Nat := 1518464477995280679012595

theorem tailTrace_2957199 : CollatzResearch.WordTrace tailWord_2957199 prefixEnd_2957199 1518464477995280679012595 := by
  unfold tailWord_2957199
  simp only [CollatzResearch.WordTrace]
  refine ⟨107857908413580547225274651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71905272275720364816849767 107857908413580547225274651)
  ·
    refine ⟨161786862620370820837911977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107857908413580547225274651 161786862620370820837911977)
    ·
      refine ⟨121340146965278115628433983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161786862620370820837911977 121340146965278115628433983)
      ·
        refine ⟨182010220447917173442650975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121340146965278115628433983 182010220447917173442650975)
        ·
          refine ⟨273015330671875760163976463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182010220447917173442650975 273015330671875760163976463)
          ·
            refine ⟨409522996007813640245964695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273015330671875760163976463 409522996007813640245964695)
            ·
              refine ⟨614284494011720460368947043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409522996007813640245964695 614284494011720460368947043)
              ·
                refine ⟨921426741017580690553420565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614284494011720460368947043 921426741017580690553420565)
                ·
                  refine ⟨43191878485199094869691589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 921426741017580690553420565 43191878485199094869691589)
                  ·
                    refine ⟨8098477215974830288067173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43191878485199094869691589 8098477215974830288067173)
                    ·
                      refine ⟨1518464477995280679012595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8098477215974830288067173 1518464477995280679012595)
                      ·
                        rfl

theorem cell23_2957199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_2957199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957199 prefixEnd_2957199 := by exact prefixLift 2957199
  have htrace : WordTrace (prefixWord ++ tailWord_2957199) baseStart_2957199 baseEnd_2957199 := by
    simpa [prefixWord, tailWord_2957199, baseEnd_2957199] using wordTrace_append hprefix tailTrace_2957199
  have hstable : (prefixWord ++ tailWord_2957199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957199).length < 2 ^ (prefixWord ++ tailWord_2957199).sum := by decide
  have hdescent : baseEnd_2957199 < baseStart_2957199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957209 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 8]
def baseStart_2957209 : Nat := 118140960795 + 2957209 * 2 ^ 59
def prefixEnd_2957209 : Nat := 4983230072969 + 3 ^ 40 * 2957209 * 2
def baseEnd_2957209 : Nat := 168718845866869515543061

theorem tailTrace_2957209 : CollatzResearch.WordTrace tailWord_2957209 prefixEnd_2957209 168718845866869515543061 := by
  unfold tailWord_2957209
  simp only [CollatzResearch.WordTrace]
  refine ⟨107858273143544318933138681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71905515429029545955425787 107858273143544318933138681)
  ·
    refine ⟨80893704857658239199854011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107858273143544318933138681 80893704857658239199854011)
    ·
      refine ⟨121340557286487358799781017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80893704857658239199854011 121340557286487358799781017)
      ·
        refine ⟨91005417964865519099835763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121340557286487358799781017 91005417964865519099835763)
        ·
          refine ⟨136508126947298278649753645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91005417964865519099835763 136508126947298278649753645)
          ·
            refine ⟨51190547605236854493657617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136508126947298278649753645 51190547605236854493657617)
            ·
              refine ⟨38392910703927640870243213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51190547605236854493657617 38392910703927640870243213)
              ·
                refine ⟨14397341513972865326341205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38392910703927640870243213 14397341513972865326341205)
                ·
                  refine ⟨168718845866869515543061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14397341513972865326341205 168718845866869515543061)
                  ·
                    rfl

theorem cell23_2957209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_2957209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957209 prefixEnd_2957209 := by exact prefixLift 2957209
  have htrace : WordTrace (prefixWord ++ tailWord_2957209) baseStart_2957209 baseEnd_2957209 := by
    simpa [prefixWord, tailWord_2957209, baseEnd_2957209] using wordTrace_append hprefix tailTrace_2957209
  have hstable : (prefixWord ++ tailWord_2957209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957209).length < 2 ^ (prefixWord ++ tailWord_2957209).sum := by decide
  have hdescent : baseEnd_2957209 < baseStart_2957209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957263 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 4, 3, 2]
def baseStart_2957263 : Nat := 118140960795 + 2957263 * 2 ^ 59
def prefixEnd_2957263 : Nat := 4983230072969 + 3 ^ 40 * 2957263 * 2
def baseEnd_2957263 : Nat := 1518497340757168428612301

theorem tailTrace_2957263 : CollatzResearch.WordTrace tailWord_2957263 prefixEnd_2957263 1518497340757168428612301 := by
  unfold tailWord_2957263
  simp only [CollatzResearch.WordTrace]
  refine ⟨107860242685348686155604443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71906828456899124103736295 107860242685348686155604443)
  ·
    refine ⟨161790364028023029233406665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107860242685348686155604443 161790364028023029233406665)
    ·
      refine ⟨121342773021017271925054999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161790364028023029233406665 121342773021017271925054999)
      ·
        refine ⟨182014159531525907887582499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121342773021017271925054999 182014159531525907887582499)
        ·
          refine ⟨273021239297288861831373749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182014159531525907887582499 273021239297288861831373749)
          ·
            refine ⟨25595741184120830796691289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273021239297288861831373749 25595741184120830796691289)
            ·
              refine ⟨19196805888090623097518467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25595741184120830796691289 19196805888090623097518467)
              ·
                refine ⟨28795208832135934646277701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19196805888090623097518467 28795208832135934646277701)
                ·
                  refine ⟨5399101656025487746177069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28795208832135934646277701 5399101656025487746177069)
                  ·
                    refine ⟨2024663121009557904816401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5399101656025487746177069 2024663121009557904816401)
                    ·
                      refine ⟨1518497340757168428612301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024663121009557904816401 1518497340757168428612301)
                      ·
                        rfl

theorem cell23_2957263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3, 2].length) (baseStart_2957263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957263 prefixEnd_2957263 := by exact prefixLift 2957263
  have htrace : WordTrace (prefixWord ++ tailWord_2957263) baseStart_2957263 baseEnd_2957263 := by
    simpa [prefixWord, tailWord_2957263, baseEnd_2957263] using wordTrace_append hprefix tailTrace_2957263
  have hstable : (prefixWord ++ tailWord_2957263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957263).length < 2 ^ (prefixWord ++ tailWord_2957263).sum := by decide
  have hdescent : baseEnd_2957263 < baseStart_2957263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957313 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2957313 : Nat := 118140960795 + 2957313 * 2 ^ 59
def prefixEnd_2957313 : Nat := 4983230072969 + 3 ^ 40 * 2957313 * 2
def baseEnd_2957313 : Nat := 1518523014789893232987071

theorem tailTrace_2957313 : CollatzResearch.WordTrace tailWord_2957313 prefixEnd_2957313 1518523014789893232987071 := by
  unfold tailWord_2957313
  simp only [CollatzResearch.WordTrace]
  refine ⟨107862066335167544694924593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71908044223445029796616395 107862066335167544694924593)
  ·
    refine ⟨80896549751375658521193445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107862066335167544694924593 80896549751375658521193445)
    ·
      refine ⟨15168103078382935972723771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80896549751375658521193445 15168103078382935972723771)
      ·
        refine ⟨22752154617574403959085657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15168103078382935972723771 22752154617574403959085657)
        ·
          refine ⟨17064115963180802969314243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22752154617574403959085657 17064115963180802969314243)
          ·
            refine ⟨25596173944771204453971365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17064115963180802969314243 25596173944771204453971365)
            ·
              refine ⟨4799282614644600835119631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25596173944771204453971365 4799282614644600835119631)
              ·
                refine ⟨7198923921966901252679447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799282614644600835119631 7198923921966901252679447)
                ·
                  refine ⟨10798385882950351879019171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198923921966901252679447 10798385882950351879019171)
                  ·
                    refine ⟨16197578824425527818528757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10798385882950351879019171 16197578824425527818528757)
                    ·
                      refine ⟨1518523014789893232987071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16197578824425527818528757 1518523014789893232987071)
                      ·
                        rfl

theorem cell23_2957313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2957313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957313 prefixEnd_2957313 := by exact prefixLift 2957313
  have htrace : WordTrace (prefixWord ++ tailWord_2957313) baseStart_2957313 baseEnd_2957313 := by
    simpa [prefixWord, tailWord_2957313, baseEnd_2957313] using wordTrace_append hprefix tailTrace_2957313
  have hstable : (prefixWord ++ tailWord_2957313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957313).length < 2 ^ (prefixWord ++ tailWord_2957313).sum := by decide
  have hdescent : baseEnd_2957313 < baseStart_2957313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957333 : List Nat := [1, 3, 2, 1, 5, 1, 2, 8]
def baseStart_2957333 : Nat := 118140960795 + 2957333 * 2 ^ 59
def prefixEnd_2957333 : Nat := 4983230072969 + 3 ^ 40 * 2957333 * 2
def baseEnd_2957333 : Nat := 56241973496406783508777

theorem tailTrace_2957333 : CollatzResearch.WordTrace tailWord_2957333 prefixEnd_2957333 56241973496406783508777 := by
  unfold tailWord_2957333
  simp only [CollatzResearch.WordTrace]
  refine ⟨107862795795095088110652653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71908530530063392073768435 107862795795095088110652653)
  ·
    refine ⟨40448548423160658041494745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107862795795095088110652653 40448548423160658041494745)
    ·
      refine ⟨30336411317370493531121059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40448548423160658041494745 30336411317370493531121059)
      ·
        refine ⟨45504616976055740296681589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30336411317370493531121059 45504616976055740296681589)
        ·
          refine ⟨4266057841505225652813899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45504616976055740296681589 4266057841505225652813899)
          ·
            refine ⟨6399086762257838479220849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266057841505225652813899 6399086762257838479220849)
            ·
              refine ⟨4799315071693378859415637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399086762257838479220849 4799315071693378859415637)
              ·
                refine ⟨56241973496406783508777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4799315071693378859415637 56241973496406783508777)
                ·
                  rfl

theorem cell23_2957333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 8].length) (baseStart_2957333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957333 prefixEnd_2957333 := by exact prefixLift 2957333
  have htrace : WordTrace (prefixWord ++ tailWord_2957333) baseStart_2957333 baseEnd_2957333 := by
    simpa [prefixWord, tailWord_2957333, baseEnd_2957333] using wordTrace_append hprefix tailTrace_2957333
  have hstable : (prefixWord ++ tailWord_2957333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957333).length < 2 ^ (prefixWord ++ tailWord_2957333).sum := by decide
  have hdescent : baseEnd_2957333 < baseStart_2957333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957336 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2957336 : Nat := 118140960795 + 2957336 * 2 ^ 59
def prefixEnd_2957336 : Nat := 4983230072969 + 3 ^ 40 * 2957336 * 2
def baseEnd_2957336 : Nat := 1518534824844946642999465

theorem tailTrace_2957336 : CollatzResearch.WordTrace tailWord_2957336 prefixEnd_2957336 1518534824844946642999465 := by
  unfold tailWord_2957336
  simp only [CollatzResearch.WordTrace]
  refine ⟨53931452607042109811505931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71908603476056146415341241 53931452607042109811505931)
  ·
    refine ⟨80897178910563164717258897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53931452607042109811505931 80897178910563164717258897)
    ·
      refine ⟨60672884182922373537944173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80897178910563164717258897 60672884182922373537944173)
      ·
        refine ⟨22752331568595890076729065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60672884182922373537944173 22752331568595890076729065)
        ·
          refine ⟨17064248676446917557546799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22752331568595890076729065 17064248676446917557546799)
          ·
            refine ⟨25596373014670376336320199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17064248676446917557546799 25596373014670376336320199)
            ·
              refine ⟨38394559522005564504480299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25596373014670376336320199 38394559522005564504480299)
              ·
                refine ⟨57591839283008346756720449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38394559522005564504480299 57591839283008346756720449)
                ·
                  refine ⟨43193879462256260067540337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57591839283008346756720449 43193879462256260067540337)
                  ·
                    refine ⟨32395409596692195050655253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43193879462256260067540337 32395409596692195050655253)
                    ·
                      refine ⟨1518534824844946642999465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32395409596692195050655253 1518534824844946642999465)
                      ·
                        rfl

theorem cell23_2957336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2957336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957336 prefixEnd_2957336 := by exact prefixLift 2957336
  have htrace : WordTrace (prefixWord ++ tailWord_2957336) baseStart_2957336 baseEnd_2957336 := by
    simpa [prefixWord, tailWord_2957336, baseEnd_2957336] using wordTrace_append hprefix tailTrace_2957336
  have hstable : (prefixWord ++ tailWord_2957336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957336).length < 2 ^ (prefixWord ++ tailWord_2957336).sum := by decide
  have hdescent : baseEnd_2957336 < baseStart_2957336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957343 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_2957343 : Nat := 118140960795 + 2957343 * 2 ^ 59
def prefixEnd_2957343 : Nat := 4983230072969 + 3 ^ 40 * 2957343 * 2
def baseEnd_2957343 : Nat := 1518538419209528115611933

theorem tailTrace_2957343 : CollatzResearch.WordTrace tailWord_2957343 prefixEnd_2957343 1518538419209528115611933 := by
  unfold tailWord_2957343
  simp only [CollatzResearch.WordTrace]
  refine ⟨107863160525058859818516683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71908773683372573212344455 107863160525058859818516683)
  ·
    refine ⟨161794740787588289727775025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107863160525058859818516683 161794740787588289727775025)
    ·
      refine ⟨121346055590691217295831269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161794740787588289727775025 121346055590691217295831269)
      ·
        refine ⟨22752385423254603242968363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121346055590691217295831269 22752385423254603242968363)
        ·
          refine ⟨34128578134881904864452545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22752385423254603242968363 34128578134881904864452545)
          ·
            refine ⟨25596433601161428648339409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34128578134881904864452545 25596433601161428648339409)
            ·
              refine ⟨19197325200871071486254557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25596433601161428648339409 19197325200871071486254557)
              ·
                refine ⟨7198996950326651807345459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19197325200871071486254557 7198996950326651807345459)
                ·
                  refine ⟨10798495425489977711018189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198996950326651807345459 10798495425489977711018189)
                  ·
                    refine ⟨4049435784558741641631821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10798495425489977711018189 4049435784558741641631821)
                    ·
                      refine ⟨1518538419209528115611933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4049435784558741641631821 1518538419209528115611933)
                      ·
                        rfl

theorem cell23_2957343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_2957343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957343 prefixEnd_2957343 := by exact prefixLift 2957343
  have htrace : WordTrace (prefixWord ++ tailWord_2957343) baseStart_2957343 baseEnd_2957343 := by
    simpa [prefixWord, tailWord_2957343, baseEnd_2957343] using wordTrace_append hprefix tailTrace_2957343
  have hstable : (prefixWord ++ tailWord_2957343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957343).length < 2 ^ (prefixWord ++ tailWord_2957343).sum := by decide
  have hdescent : baseEnd_2957343 < baseStart_2957343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957356 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2957356 : Nat := 118140960795 + 2957356 * 2 ^ 59
def prefixEnd_2957356 : Nat := 4983230072969 + 3 ^ 40 * 2957356 * 2
def baseEnd_2957356 : Nat := 1518545094458036564749373

theorem tailTrace_2957356 : CollatzResearch.WordTrace tailWord_2957356 prefixEnd_2957356 1518545094458036564749373 := by
  unfold tailWord_2957356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53931817337005881519369961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71909089782674508692493281 53931817337005881519369961)
  ·
    refine ⟨40448863002754411139527471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53931817337005881519369961 40448863002754411139527471)
    ·
      refine ⟨60673294504131616709291207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40448863002754411139527471 60673294504131616709291207)
      ·
        refine ⟨91009941756197425063936811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60673294504131616709291207 91009941756197425063936811)
        ·
          refine ⟨136514912634296137595905217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91009941756197425063936811 136514912634296137595905217)
          ·
            refine ⟨102386184475722103196928913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136514912634296137595905217 102386184475722103196928913)
            ·
              refine ⟨76789638356791577397696685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102386184475722103196928913 76789638356791577397696685)
              ·
                refine ⟨28796114383796841524136257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76789638356791577397696685 28796114383796841524136257)
                ·
                  refine ⟨21597085787847631143102193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28796114383796841524136257 21597085787847631143102193)
                  ·
                    refine ⟨16197814340885723357326645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21597085787847631143102193 16197814340885723357326645)
                    ·
                      refine ⟨1518545094458036564749373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16197814340885723357326645 1518545094458036564749373)
                      ·
                        rfl

theorem cell23_2957356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2957356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957356 prefixEnd_2957356 := by exact prefixLift 2957356
  have htrace : WordTrace (prefixWord ++ tailWord_2957356) baseStart_2957356 baseEnd_2957356 := by
    simpa [prefixWord, tailWord_2957356, baseEnd_2957356] using wordTrace_append hprefix tailTrace_2957356
  have hstable : (prefixWord ++ tailWord_2957356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957356).length < 2 ^ (prefixWord ++ tailWord_2957356).sum := by decide
  have hdescent : baseEnd_2957356 < baseStart_2957356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957364 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2957364 : Nat := 118140960795 + 2957364 * 2 ^ 59
def prefixEnd_2957364 : Nat := 4983230072969 + 3 ^ 40 * 2957364 * 2
def baseEnd_2957364 : Nat := 1518549202303272533449337

theorem tailTrace_2957364 : CollatzResearch.WordTrace tailWord_2957364 prefixEnd_2957364 1518549202303272533449337 := by
  unfold tailWord_2957364
  simp only [CollatzResearch.WordTrace]
  refine ⟨53931963228991390202515573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71909284305321853603354097 53931963228991390202515573)
  ·
    refine ⟨5056121552717942831485835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53931963228991390202515573 5056121552717942831485835)
    ·
      refine ⟨7584182329076914247228753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056121552717942831485835 7584182329076914247228753)
      ·
        refine ⟨5688136746807685685421565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7584182329076914247228753 5688136746807685685421565)
        ·
          refine ⟨2133051280052882132033087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5688136746807685685421565 2133051280052882132033087)
          ·
            refine ⟨3199576920079323198049631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133051280052882132033087 3199576920079323198049631)
            ·
              refine ⟨4799365380118984797074447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199576920079323198049631 4799365380118984797074447)
              ·
                refine ⟨7199048070178477195611671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799365380118984797074447 7199048070178477195611671)
                ·
                  refine ⟨10798572105267715793417507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199048070178477195611671 10798572105267715793417507)
                  ·
                    refine ⟨16197858157901573690126261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10798572105267715793417507 16197858157901573690126261)
                    ·
                      refine ⟨1518549202303272533449337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16197858157901573690126261 1518549202303272533449337)
                      ·
                        rfl

theorem cell23_2957364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2957364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957364 prefixEnd_2957364 := by exact prefixLift 2957364
  have htrace : WordTrace (prefixWord ++ tailWord_2957364) baseStart_2957364 baseEnd_2957364 := by
    simpa [prefixWord, tailWord_2957364, baseEnd_2957364] using wordTrace_append hprefix tailTrace_2957364
  have hstable : (prefixWord ++ tailWord_2957364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957364).length < 2 ^ (prefixWord ++ tailWord_2957364).sum := by decide
  have hdescent : baseEnd_2957364 < baseStart_2957364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957377 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2957377 : Nat := 118140960795 + 2957377 * 2 ^ 59
def prefixEnd_2957377 : Nat := 4983230072969 + 3 ^ 40 * 2957377 * 2
def baseEnd_2957377 : Nat := 1518555877551780982586777

theorem tailTrace_2957377 : CollatzResearch.WordTrace tailWord_2957377 prefixEnd_2957377 1518555877551780982586777 := by
  unfold tailWord_2957377
  simp only [CollatzResearch.WordTrace]
  refine ⟨107864400606935683625254385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71909600404623789083502923 107864400606935683625254385)
  ·
    refine ⟨80898300455201762718940789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107864400606935683625254385 80898300455201762718940789)
    ·
      refine ⟨7584215667675165254900699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80898300455201762718940789 7584215667675165254900699)
      ·
        refine ⟨11376323501512747882351049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584215667675165254900699 11376323501512747882351049)
        ·
          refine ⟨8532242626134560911763287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11376323501512747882351049 8532242626134560911763287)
          ·
            refine ⟨12798363939201841367644931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8532242626134560911763287 12798363939201841367644931)
            ·
              refine ⟨19197545908802762051467397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798363939201841367644931 19197545908802762051467397)
              ·
                refine ⟨3599539857900517884650137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19197545908802762051467397 3599539857900517884650137)
                ·
                  refine ⟨2699654893425388413487603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3599539857900517884650137 2699654893425388413487603)
                  ·
                    refine ⟨4049482340138082620231405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2699654893425388413487603 4049482340138082620231405)
                    ·
                      refine ⟨1518555877551780982586777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4049482340138082620231405 1518555877551780982586777)
                      ·
                        rfl

theorem cell23_2957377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2957377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957377 prefixEnd_2957377 := by exact prefixLift 2957377
  have htrace : WordTrace (prefixWord ++ tailWord_2957377) baseStart_2957377 baseEnd_2957377 := by
    simpa [prefixWord, tailWord_2957377, baseEnd_2957377] using wordTrace_append hprefix tailTrace_2957377
  have hstable : (prefixWord ++ tailWord_2957377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957377).length < 2 ^ (prefixWord ++ tailWord_2957377).sum := by decide
  have hdescent : baseEnd_2957377 < baseStart_2957377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957400 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_2957400 : Nat := 118140960795 + 2957400 * 2 ^ 59
def prefixEnd_2957400 : Nat := 4983230072969 + 3 ^ 40 * 2957400 * 2
def baseEnd_2957400 : Nat := 1518567687606834392599171

theorem tailTrace_2957400 : CollatzResearch.WordTrace tailWord_2957400 prefixEnd_2957400 1518567687606834392599171 := by
  unfold tailWord_2957400
  simp only [CollatzResearch.WordTrace]
  refine ⟨53932619742926179276670827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71910159657234905702227769 53932619742926179276670827)
  ·
    refine ⟨80898929614389268915006241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53932619742926179276670827 80898929614389268915006241)
    ·
      refine ⟨60674197210791951686254681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80898929614389268915006241 60674197210791951686254681)
      ·
        refine ⟨45505647908093963764691011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60674197210791951686254681 45505647908093963764691011)
        ·
          refine ⟨68258471862140945647036517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45505647908093963764691011 68258471862140945647036517)
          ·
            refine ⟨12798463474151427308819347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68258471862140945647036517 12798463474151427308819347)
            ·
              refine ⟨19197695211227140963229021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798463474151427308819347 19197695211227140963229021)
              ·
                refine ⟨7199135704210177861210883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19197695211227140963229021 7199135704210177861210883)
                ·
                  refine ⟨10798703556315266791816325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199135704210177861210883 10798703556315266791816325)
                  ·
                    refine ⟨2024756916809112523465561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10798703556315266791816325 2024756916809112523465561)
                    ·
                      refine ⟨1518567687606834392599171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024756916809112523465561 1518567687606834392599171)
                      ·
                        rfl

theorem cell23_2957400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_2957400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957400 prefixEnd_2957400 := by exact prefixLift 2957400
  have htrace : WordTrace (prefixWord ++ tailWord_2957400) baseStart_2957400 baseEnd_2957400 := by
    simpa [prefixWord, tailWord_2957400, baseEnd_2957400] using wordTrace_append hprefix tailTrace_2957400
  have hstable : (prefixWord ++ tailWord_2957400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957400).length < 2 ^ (prefixWord ++ tailWord_2957400).sum := by decide
  have hdescent : baseEnd_2957400 < baseStart_2957400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957430 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2957430 : Nat := 118140960795 + 2957430 * 2 ^ 59
def prefixEnd_2957430 : Nat := 4983230072969 + 3 ^ 40 * 2957430 * 2
def baseEnd_2957430 : Nat := 1518583092026469275224033

theorem tailTrace_2957430 : CollatzResearch.WordTrace tailWord_2957430 prefixEnd_2957430 1518583092026469275224033 := by
  unfold tailWord_2957430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741645854733979604808359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71910889117162449117955829 6741645854733979604808359)
  ·
    refine ⟨10112468782100969407212539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6741645854733979604808359 10112468782100969407212539)
    ·
      refine ⟨15168703173151454110818809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10112468782100969407212539 15168703173151454110818809)
      ·
        refine ⟨11376527379863590583114107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15168703173151454110818809 11376527379863590583114107)
        ·
          refine ⟨17064791069795385874671161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376527379863590583114107 17064791069795385874671161)
          ·
            refine ⟨12798593302346539406003371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17064791069795385874671161 12798593302346539406003371)
            ·
              refine ⟨19197889953519809109005057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798593302346539406003371 19197889953519809109005057)
              ·
                refine ⟨14398417465139856831753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19197889953519809109005057 14398417465139856831753793)
                ·
                  refine ⟨10798813098854892623815345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14398417465139856831753793 10798813098854892623815345)
                  ·
                    refine ⟨8099109824141169467861509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10798813098854892623815345 8099109824141169467861509)
                    ·
                      refine ⟨1518583092026469275224033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8099109824141169467861509 1518583092026469275224033)
                      ·
                        rfl

theorem cell23_2957430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2957430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957430 prefixEnd_2957430 := by exact prefixLift 2957430
  have htrace : WordTrace (prefixWord ++ tailWord_2957430) baseStart_2957430 baseEnd_2957430 := by
    simpa [prefixWord, tailWord_2957430, baseEnd_2957430] using wordTrace_append hprefix tailTrace_2957430
  have hstable : (prefixWord ++ tailWord_2957430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957430).length < 2 ^ (prefixWord ++ tailWord_2957430).sum := by decide
  have hdescent : baseEnd_2957430 < baseStart_2957430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957450 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2957450 : Nat := 118140960795 + 2957450 * 2 ^ 59
def prefixEnd_2957450 : Nat := 4983230072969 + 3 ^ 40 * 2957450 * 2
def baseEnd_2957450 : Nat := 1518593361639559196973941

theorem tailTrace_2957450 : CollatzResearch.WordTrace tailWord_2957450 prefixEnd_2957450 1518593361639559196973941 := by
  unfold tailWord_2957450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966765783917804273165451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71911375423780811395107869 26966765783917804273165451)
  ·
    refine ⟨40450148675876706409748177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26966765783917804273165451 40450148675876706409748177)
    ·
      refine ⟨30337611506907529807311133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40450148675876706409748177 30337611506907529807311133)
      ·
        refine ⟨11376604315090323677741675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30337611506907529807311133 11376604315090323677741675)
        ·
          refine ⟨17064906472635485516612513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376604315090323677741675 17064906472635485516612513)
          ·
            refine ⟨12798679854476614137459385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17064906472635485516612513 12798679854476614137459385)
            ·
              refine ⟨9599009890857460603094539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12798679854476614137459385 9599009890857460603094539)
              ·
                refine ⟨14398514836286190904641809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9599009890857460603094539 14398514836286190904641809)
                ·
                  refine ⟨10798886127214643178481357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14398514836286190904641809 10798886127214643178481357)
                  ·
                    refine ⟨4049582297705491191930509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10798886127214643178481357 4049582297705491191930509)
                    ·
                      refine ⟨1518593361639559196973941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4049582297705491191930509 1518593361639559196973941)
                      ·
                        rfl

theorem cell23_2957450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2957450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957450 prefixEnd_2957450 := by exact prefixLift 2957450
  have htrace : WordTrace (prefixWord ++ tailWord_2957450) baseStart_2957450 baseEnd_2957450 := by
    simpa [prefixWord, tailWord_2957450, baseEnd_2957450] using wordTrace_append hprefix tailTrace_2957450
  have hstable : (prefixWord ++ tailWord_2957450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957450).length < 2 ^ (prefixWord ++ tailWord_2957450).sum := by decide
  have hdescent : baseEnd_2957450 < baseStart_2957450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957474 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_2957474 : Nat := 118140960795 + 2957474 * 2 ^ 59
def prefixEnd_2957474 : Nat := 4983230072969 + 3 ^ 40 * 2957474 * 2
def baseEnd_2957474 : Nat := 168733965019474122563759

theorem tailTrace_2957474 : CollatzResearch.WordTrace tailWord_2957474 prefixEnd_2957474 168733965019474122563759 := by
  unfold tailWord_2957474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966984621896067297883869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71911958991722846127690317 26966984621896067297883869)
  ·
    refine ⟨10112619233211025236706451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26966984621896067297883869 10112619233211025236706451)
    ·
      refine ⟨15168928849816537855059677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10112619233211025236706451 15168928849816537855059677)
      ·
        refine ⟨5688348318681201695647379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15168928849816537855059677 5688348318681201695647379)
        ·
          refine ⟨8532522478021802543471069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688348318681201695647379 8532522478021802543471069)
          ·
            refine ⟨3199695929258175953801651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8532522478021802543471069 3199695929258175953801651)
            ·
              refine ⟨4799543893887263930702477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199695929258175953801651 4799543893887263930702477)
              ·
                refine ⟨1799828960207723974013429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4799543893887263930702477 1799828960207723974013429)
                ·
                  refine ⟨168733965019474122563759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799828960207723974013429 168733965019474122563759)
                  ·
                    rfl

theorem cell23_2957474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_2957474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957474 prefixEnd_2957474 := by exact prefixLift 2957474
  have htrace : WordTrace (prefixWord ++ tailWord_2957474) baseStart_2957474 baseEnd_2957474 := by
    simpa [prefixWord, tailWord_2957474, baseEnd_2957474] using wordTrace_append hprefix tailTrace_2957474
  have hstable : (prefixWord ++ tailWord_2957474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957474).length < 2 ^ (prefixWord ++ tailWord_2957474).sum := by decide
  have hdescent : baseEnd_2957474 < baseStart_2957474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957490 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_2957490 : Nat := 118140960795 + 2957490 * 2 ^ 59
def prefixEnd_2957490 : Nat := 4983230072969 + 3 ^ 40 * 2957490 * 2
def baseEnd_2957490 : Nat := 1518613900865739040473757

theorem tailTrace_2957490 : CollatzResearch.WordTrace tailWord_2957490 prefixEnd_2957490 1518613900865739040473757 := by
  unfold tailWord_2957490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26967130513881575981029481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71912348037017535949411949 26967130513881575981029481)
  ·
    refine ⟨20225347885411181985772111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26967130513881575981029481 20225347885411181985772111)
    ·
      refine ⟨30338021828116772978658167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20225347885411181985772111 30338021828116772978658167)
      ·
        refine ⟨45507032742175159467987251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30338021828116772978658167 45507032742175159467987251)
        ·
          refine ⟨68260549113262739201980877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45507032742175159467987251 68260549113262739201980877)
          ·
            refine ⟨25597705917473527200742829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68260549113262739201980877 25597705917473527200742829)
            ·
              refine ⟨9599139719052572700278561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25597705917473527200742829 9599139719052572700278561)
              ·
                refine ⟨7199354789289429525208921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599139719052572700278561 7199354789289429525208921)
                ·
                  refine ⟨5399516091967072143906691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199354789289429525208921 5399516091967072143906691)
                  ·
                    refine ⟨8099274137950608215860037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5399516091967072143906691 8099274137950608215860037)
                    ·
                      refine ⟨1518613900865739040473757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8099274137950608215860037 1518613900865739040473757)
                      ·
                        rfl

theorem cell23_2957490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_2957490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957490 prefixEnd_2957490 := by exact prefixLift 2957490
  have htrace : WordTrace (prefixWord ++ tailWord_2957490) baseStart_2957490 baseEnd_2957490 := by
    simpa [prefixWord, tailWord_2957490, baseEnd_2957490] using wordTrace_append hprefix tailTrace_2957490
  have hstable : (prefixWord ++ tailWord_2957490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957490).length < 2 ^ (prefixWord ++ tailWord_2957490).sum := by decide
  have hdescent : baseEnd_2957490 < baseStart_2957490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957551 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 1, 4]
def baseStart_2957551 : Nat := 118140960795 + 2957551 * 2 ^ 59
def prefixEnd_2957551 : Nat := 4983230072969 + 3 ^ 40 * 2957551 * 2
def baseEnd_2957551 : Nat := 506215074395221100603659

theorem tailTrace_2957551 : CollatzResearch.WordTrace tailWord_2957551 prefixEnd_2957551 506215074395221100603659 := by
  unfold tailWord_2957551
  simp only [CollatzResearch.WordTrace]
  refine ⟨107870746908305311342088507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71913831272203540894725671 107870746908305311342088507)
  ·
    refine ⟨161806120362457967013132761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107870746908305311342088507 161806120362457967013132761)
    ·
      refine ⟨121354590271843475259849571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161806120362457967013132761 121354590271843475259849571)
      ·
        refine ⟨182031885407765212889774357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121354590271843475259849571 182031885407765212889774357)
        ·
          refine ⟨8532744628488994354208173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182031885407765212889774357 8532744628488994354208173)
          ·
            refine ⟨3199779235683372882828065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8532744628488994354208173 3199779235683372882828065)
            ·
              refine ⟨2399834426762529662121049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3199779235683372882828065 2399834426762529662121049)
              ·
                refine ⟨1799875820071897246590787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399834426762529662121049 1799875820071897246590787)
                ·
                  refine ⟨2699813730107845869886181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799875820071897246590787 2699813730107845869886181)
                  ·
                    refine ⟨506215074395221100603659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2699813730107845869886181 506215074395221100603659)
                    ·
                      rfl

theorem cell23_2957551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 4].length) (baseStart_2957551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957551 prefixEnd_2957551 := by exact prefixLift 2957551
  have htrace : WordTrace (prefixWord ++ tailWord_2957551) baseStart_2957551 baseEnd_2957551 := by
    simpa [prefixWord, tailWord_2957551, baseEnd_2957551] using wordTrace_append hprefix tailTrace_2957551
  have hstable : (prefixWord ++ tailWord_2957551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957551).length < 2 ^ (prefixWord ++ tailWord_2957551).sum := by decide
  have hdescent : baseEnd_2957551 < baseStart_2957551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957580 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2957580 : Nat := 118140960795 + 2957580 * 2 ^ 59
def prefixEnd_2957580 : Nat := 4983230072969 + 3 ^ 40 * 2957580 * 2
def baseEnd_2957580 : Nat := 1518660114124643688348343

theorem tailTrace_2957580 : CollatzResearch.WordTrace tailWord_2957580 prefixEnd_2957580 1518660114124643688348343 := by
  unfold tailWord_2957580
  simp only [CollatzResearch.WordTrace]
  refine ⟨53935902312600124647447097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71914536416800166196596129 53935902312600124647447097)
  ·
    refine ⟨40451926734450093485585323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53935902312600124647447097 40451926734450093485585323)
    ·
      refine ⟨60677890101675140228377985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40451926734450093485585323 60677890101675140228377985)
      ·
        refine ⟨45508417576256355171283489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60677890101675140228377985 45508417576256355171283489)
        ·
          refine ⟨34131313182192266378462617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45508417576256355171283489 34131313182192266378462617)
          ·
            refine ⟨25598484886644199783846963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34131313182192266378462617 25598484886644199783846963)
            ·
              refine ⟨38397727329966299675770445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25598484886644199783846963 38397727329966299675770445)
              ·
                refine ⟨14399147748737362378413917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38397727329966299675770445 14399147748737362378413917)
                ·
                  refine ⟨5399680405776510891905219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14399147748737362378413917 5399680405776510891905219)
                  ·
                    refine ⟨8099520608664766337857829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5399680405776510891905219 8099520608664766337857829)
                    ·
                      refine ⟨1518660114124643688348343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8099520608664766337857829 1518660114124643688348343)
                      ·
                        rfl

theorem cell23_2957580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2957580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957580 prefixEnd_2957580 := by exact prefixLift 2957580
  have htrace : WordTrace (prefixWord ++ tailWord_2957580) baseStart_2957580 baseEnd_2957580 := by
    simpa [prefixWord, tailWord_2957580, baseEnd_2957580] using wordTrace_append hprefix tailTrace_2957580
  have hstable : (prefixWord ++ tailWord_2957580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957580).length < 2 ^ (prefixWord ++ tailWord_2957580).sum := by decide
  have hdescent : baseEnd_2957580 < baseStart_2957580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957591 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2957591 : Nat := 118140960795 + 2957591 * 2 ^ 59
def prefixEnd_2957591 : Nat := 4983230072969 + 3 ^ 40 * 2957591 * 2
def baseEnd_2957591 : Nat := 1518665762411843145310793

theorem tailTrace_2957591 : CollatzResearch.WordTrace tailWord_2957591 prefixEnd_2957591 1518665762411843145310793 := by
  unfold tailWord_2957591
  simp only [CollatzResearch.WordTrace]
  refine ⟨107872205828160398173544627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71914803885440265449029751 107872205828160398173544627)
  ·
    refine ⟨161808308742240597260316941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107872205828160398173544627 161808308742240597260316941)
    ·
      refine ⟨60678115778340223972618853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161808308742240597260316941 60678115778340223972618853)
      ·
        refine ⟨11377146708438791994866035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60678115778340223972618853 11377146708438791994866035)
        ·
          refine ⟨17065720062658187992299053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377146708438791994866035 17065720062658187992299053)
          ·
            refine ⟨6399645023496820497112145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17065720062658187992299053 6399645023496820497112145)
            ·
              refine ⟨4799733767622615372834109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399645023496820497112145 4799733767622615372834109)
              ·
                refine ⟨1799900162858480764812791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4799733767622615372834109 1799900162858480764812791)
                ·
                  refine ⟨2699850244287721147219187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799900162858480764812791 2699850244287721147219187)
                  ·
                    refine ⟨4049775366431581720828781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2699850244287721147219187 4049775366431581720828781)
                    ·
                      refine ⟨1518665762411843145310793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4049775366431581720828781 1518665762411843145310793)
                      ·
                        rfl

theorem cell23_2957591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2957591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957591 prefixEnd_2957591 := by exact prefixLift 2957591
  have htrace : WordTrace (prefixWord ++ tailWord_2957591) baseStart_2957591 baseEnd_2957591 := by
    simpa [prefixWord, tailWord_2957591, baseEnd_2957591] using wordTrace_append hprefix tailTrace_2957591
  have hstable : (prefixWord ++ tailWord_2957591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957591).length < 2 ^ (prefixWord ++ tailWord_2957591).sum := by decide
  have hdescent : baseEnd_2957591 < baseStart_2957591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957603 : List Nat := [1, 1, 1, 4, 2, 2, 12]
def baseStart_2957603 : Nat := 118140960795 + 2957603 * 2 ^ 59
def prefixEnd_2957603 : Nat := 4983230072969 + 3 ^ 40 * 2957603 * 2
def baseEnd_2957603 : Nat := 18749036100983914794577

theorem tailTrace_2957603 : CollatzResearch.WordTrace tailWord_2957603 prefixEnd_2957603 18749036100983914794577 := by
  unfold tailWord_2957603
  simp only [CollatzResearch.WordTrace]
  refine ⟨107872643504116924222981463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71915095669411282815320975 107872643504116924222981463)
  ·
    refine ⟨161808965256175386334472195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107872643504116924222981463 161808965256175386334472195)
    ·
      refine ⟨242713447884263079501708293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161808965256175386334472195 242713447884263079501708293)
      ·
        refine ⟨45508771478299327406570305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242713447884263079501708293 45508771478299327406570305)
        ·
          refine ⟨34131578608724495554927729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45508771478299327406570305 34131578608724495554927729)
          ·
            refine ⟨25598683956543371666195797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34131578608724495554927729 25598683956543371666195797)
            ·
              refine ⟨18749036100983914794577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25598683956543371666195797 18749036100983914794577)
              ·
                rfl

theorem cell23_2957603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 12].length) (baseStart_2957603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957603 prefixEnd_2957603 := by exact prefixLift 2957603
  have htrace : WordTrace (prefixWord ++ tailWord_2957603) baseStart_2957603 baseEnd_2957603 := by
    simpa [prefixWord, tailWord_2957603, baseEnd_2957603] using wordTrace_append hprefix tailTrace_2957603
  have hstable : (prefixWord ++ tailWord_2957603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957603).length < 2 ^ (prefixWord ++ tailWord_2957603).sum := by decide
  have hdescent : baseEnd_2957603 < baseStart_2957603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957617 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2957617 : Nat := 118140960795 + 2957617 * 2 ^ 59
def prefixEnd_2957617 : Nat := 4983230072969 + 3 ^ 40 * 2957617 * 2
def baseEnd_2957617 : Nat := 1518679112908860043585673

theorem tailTrace_2957617 : CollatzResearch.WordTrace tailWord_2957617 prefixEnd_2957617 1518679112908860043585673 := by
  unfold tailWord_2957617
  simp only [CollatzResearch.WordTrace]
  refine ⟨107873154126066204613991105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71915436084044136409327403 107873154126066204613991105)
  ·
    refine ⟨80904865594549653460493329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107873154126066204613991105 80904865594549653460493329)
    ·
      refine ⟨60678649195912240095369997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80904865594549653460493329 60678649195912240095369997)
      ·
        refine ⟨22754493448467090035763749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60678649195912240095369997 22754493448467090035763749)
        ·
          refine ⟨4266467521587579381705703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22754493448467090035763749 4266467521587579381705703)
          ·
            refine ⟨6399701282381369072558555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266467521587579381705703 6399701282381369072558555)
            ·
              refine ⟨9599551923572053608837833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399701282381369072558555 9599551923572053608837833)
              ·
                refine ⟨7199663942679040206628375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599551923572053608837833 7199663942679040206628375)
                ·
                  refine ⟨10799495914018560309942563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199663942679040206628375 10799495914018560309942563)
                  ·
                    refine ⟨16199243871027840464913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10799495914018560309942563 16199243871027840464913845)
                    ·
                      refine ⟨1518679112908860043585673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16199243871027840464913845 1518679112908860043585673)
                      ·
                        rfl

theorem cell23_2957617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2957617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957617 prefixEnd_2957617 := by exact prefixLift 2957617
  have htrace : WordTrace (prefixWord ++ tailWord_2957617) baseStart_2957617 baseEnd_2957617 := by
    simpa [prefixWord, tailWord_2957617, baseEnd_2957617] using wordTrace_append hprefix tailTrace_2957617
  have hstable : (prefixWord ++ tailWord_2957617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957617).length < 2 ^ (prefixWord ++ tailWord_2957617).sum := by decide
  have hdescent : baseEnd_2957617 < baseStart_2957617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957648 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 1, 2, 2]
def baseStart_2957648 : Nat := 118140960795 + 2957648 * 2 ^ 59
def prefixEnd_2957648 : Nat := 4983230072969 + 3 ^ 40 * 2957648 * 2
def baseEnd_2957648 : Nat := 1518695030809149422298031

theorem tailTrace_2957648 : CollatzResearch.WordTrace tailWord_2957648 prefixEnd_2957648 1518695030809149422298031 := by
  unfold tailWord_2957648
  simp only [CollatzResearch.WordTrace]
  refine ⟨53937142394476948454184799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71916189859302597938913065 53937142394476948454184799)
  ·
    refine ⟨80905713591715422681277199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53937142394476948454184799 80905713591715422681277199)
    ·
      refine ⟨121358570387573134021915799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80905713591715422681277199 121358570387573134021915799)
      ·
        refine ⟨182037855581359701032873699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121358570387573134021915799 182037855581359701032873699)
        ·
          refine ⟨273056783372039551549310549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182037855581359701032873699 273056783372039551549310549)
          ·
            refine ⟨3199884180141088494718483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 273056783372039551549310549 3199884180141088494718483)
            ·
              refine ⟨4799826270211632742077725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199884180141088494718483 4799826270211632742077725)
              ·
                refine ⟨1799934851329362278279147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4799826270211632742077725 1799934851329362278279147)
                ·
                  refine ⟨2699902276994043417418721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799934851329362278279147 2699902276994043417418721)
                  ·
                    refine ⟨2024926707745532563064041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2699902276994043417418721 2024926707745532563064041)
                    ·
                      refine ⟨1518695030809149422298031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024926707745532563064041 1518695030809149422298031)
                      ·
                        rfl

theorem cell23_2957648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 2, 2].length) (baseStart_2957648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957648 prefixEnd_2957648 := by exact prefixLift 2957648
  have htrace : WordTrace (prefixWord ++ tailWord_2957648) baseStart_2957648 baseEnd_2957648 := by
    simpa [prefixWord, tailWord_2957648, baseEnd_2957648] using wordTrace_append hprefix tailTrace_2957648
  have hstable : (prefixWord ++ tailWord_2957648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957648).length < 2 ^ (prefixWord ++ tailWord_2957648).sum := by decide
  have hdescent : baseEnd_2957648 < baseStart_2957648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957657 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 5, 3, 2]
def baseStart_2957657 : Nat := 118140960795 + 2957657 * 2 ^ 59
def prefixEnd_2957657 : Nat := 4983230072969 + 3 ^ 40 * 2957657 * 2
def baseEnd_2957657 : Nat := 1518699652135039887085489

theorem tailTrace_2957657 : CollatzResearch.WordTrace tailWord_2957657 prefixEnd_2957657 1518699652135039887085489 := by
  unfold tailWord_2957657
  simp only [CollatzResearch.WordTrace]
  refine ⟨107874613045921291445447225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71916408697280860963631483 107874613045921291445447225)
  ·
    refine ⟨80905959784440968584085419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107874613045921291445447225 80905959784440968584085419)
    ·
      refine ⟨121358939676661452876128129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80905959784440968584085419 121358939676661452876128129)
      ·
        refine ⟨91019204757496089657096097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121358939676661452876128129 91019204757496089657096097)
        ·
          refine ⟨68264403568122067242822073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91019204757496089657096097 68264403568122067242822073)
          ·
            refine ⟨51198302676091550432116555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68264403568122067242822073 51198302676091550432116555)
            ·
              refine ⟨76797454014137325648174833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51198302676091550432116555 76797454014137325648174833)
              ·
                refine ⟨57598090510602994236131125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76797454014137325648174833 57598090510602994236131125)
                ·
                  refine ⟨5399820985369030709637293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57598090510602994236131125 5399820985369030709637293)
                  ·
                    refine ⟨2024932869513386516113985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5399820985369030709637293 2024932869513386516113985)
                    ·
                      refine ⟨1518699652135039887085489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024932869513386516113985 1518699652135039887085489)
                      ·
                        rfl

theorem cell23_2957657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_2957657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957657 prefixEnd_2957657 := by exact prefixLift 2957657
  have htrace : WordTrace (prefixWord ++ tailWord_2957657) baseStart_2957657 baseEnd_2957657 := by
    simpa [prefixWord, tailWord_2957657, baseEnd_2957657] using wordTrace_append hprefix tailTrace_2957657
  have hstable : (prefixWord ++ tailWord_2957657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957657).length < 2 ^ (prefixWord ++ tailWord_2957657).sum := by decide
  have hdescent : baseEnd_2957657 < baseStart_2957657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
