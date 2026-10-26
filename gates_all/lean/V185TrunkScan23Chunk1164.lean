import V185TrunkScan23Chunk1163

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6896007 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_6896007 : Nat := 118140960795 + 6896007 * 2 ^ 59
def prefixEnd_6896007 : Nat := 4983230072969 + 3 ^ 40 * 6896007 * 2
def baseEnd_6896007 : Nat := 3540966187769706074598347

theorem tailTrace_6896007 : CollatzResearch.WordTrace tailWord_6896007 prefixEnd_6896007 3540966187769706074598347 := by
  unfold tailWord_6896007
  simp only [CollatzResearch.WordTrace]
  refine ⟨251518038327951858075702275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167678692218634572050468183 251518038327951858075702275)
  ·
    refine ⟨377277057491927787113553413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251518038327951858075702275 377277057491927787113553413)
    ·
      refine ⟨70739448279736460083791265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377277057491927787113553413 70739448279736460083791265)
      ·
        refine ⟨53054586209802345062843449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70739448279736460083791265 53054586209802345062843449)
        ·
          refine ⟨39790939657351758797132587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53054586209802345062843449 39790939657351758797132587)
          ·
            refine ⟨59686409486027638195698881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39790939657351758797132587 59686409486027638195698881)
            ·
              refine ⟨44764807114520728646774161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59686409486027638195698881 44764807114520728646774161)
              ·
                refine ⟨33573605335890546485080621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44764807114520728646774161 33573605335890546485080621)
                ·
                  refine ⟨12590102000958954931905233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33573605335890546485080621 12590102000958954931905233)
                  ·
                    refine ⟨9442576500719216198928925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12590102000958954931905233 9442576500719216198928925)
                    ·
                      refine ⟨3540966187769706074598347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442576500719216198928925 3540966187769706074598347)
                      ·
                        rfl

theorem cell23_6896007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_6896007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896007 prefixEnd_6896007 := by exact prefixLift 6896007
  have htrace : WordTrace (prefixWord ++ tailWord_6896007) baseStart_6896007 baseEnd_6896007 := by
    simpa [prefixWord, tailWord_6896007, baseEnd_6896007] using wordTrace_append hprefix tailTrace_6896007
  have hstable : (prefixWord ++ tailWord_6896007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896007).length < 2 ^ (prefixWord ++ tailWord_6896007).sum := by decide
  have hdescent : baseEnd_6896007 < baseStart_6896007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896024 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6896024 : Nat := 118140960795 + 6896024 * 2 ^ 59
def prefixEnd_6896024 : Nat := 4983230072969 + 3 ^ 40 * 6896024 * 2
def baseEnd_6896024 : Nat := 3540974916940832508085769

theorem tailTrace_6896024 : CollatzResearch.WordTrace tailWord_6896024 prefixEnd_6896024 3540974916940832508085769 := by
  unfold tailWord_6896024
  simp only [CollatzResearch.WordTrace]
  refine ⟨125759329184445134989535563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167679105579260179986047417 125759329184445134989535563)
  ·
    refine ⟨188638993776667702484303345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125759329184445134989535563 188638993776667702484303345)
    ·
      refine ⟨141479245332500776863227509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188638993776667702484303345 141479245332500776863227509)
      ·
        refine ⟨13263679249921947830927579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141479245332500776863227509 13263679249921947830927579)
        ·
          refine ⟨19895518874882921746391369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263679249921947830927579 19895518874882921746391369)
          ·
            refine ⟨14921639156162191309793527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19895518874882921746391369 14921639156162191309793527)
            ·
              refine ⟨22382458734243286964690291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921639156162191309793527 22382458734243286964690291)
              ·
                refine ⟨33573688101364930447035437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22382458734243286964690291 33573688101364930447035437)
                ·
                  refine ⟨12590133038011848917638289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33573688101364930447035437 12590133038011848917638289)
                  ·
                    refine ⟨9442599778508886688228717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12590133038011848917638289 9442599778508886688228717)
                    ·
                      refine ⟨3540974916940832508085769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442599778508886688228717 3540974916940832508085769)
                      ·
                        rfl

theorem cell23_6896024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6896024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896024 prefixEnd_6896024 := by exact prefixLift 6896024
  have htrace : WordTrace (prefixWord ++ tailWord_6896024) baseStart_6896024 baseEnd_6896024 := by
    simpa [prefixWord, tailWord_6896024, baseEnd_6896024] using wordTrace_append hprefix tailTrace_6896024
  have hstable : (prefixWord ++ tailWord_6896024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896024).length < 2 ^ (prefixWord ++ tailWord_6896024).sum := by decide
  have hdescent : baseEnd_6896024 < baseStart_6896024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896037 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_6896037 : Nat := 118140960795 + 6896037 * 2 ^ 59
def prefixEnd_6896037 : Nat := 4983230072969 + 3 ^ 40 * 6896037 * 2
def baseEnd_6896037 : Nat := 3540981592189340957223209

theorem tailTrace_6896037 : CollatzResearch.WordTrace tailWord_6896037 prefixEnd_6896037 3540981592189340957223209 := by
  unfold tailWord_6896037
  simp only [CollatzResearch.WordTrace]
  refine ⟨251519132517843173199294365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167679421678562115466196243 251519132517843173199294365)
  ·
    refine ⟨94319674694191189949735387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251519132517843173199294365 94319674694191189949735387)
    ·
      refine ⟨141479512041286784924603081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94319674694191189949735387 141479512041286784924603081)
      ·
        refine ⟨106109634030965088693452311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141479512041286784924603081 106109634030965088693452311)
        ·
          refine ⟨159164451046447633040178467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106109634030965088693452311 159164451046447633040178467)
          ·
            refine ⟨238746676569671449560267701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159164451046447633040178467 238746676569671449560267701)
            ·
              refine ⟨22382500928406698396275097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238746676569671449560267701 22382500928406698396275097)
              ·
                refine ⟨16786875696305023797206323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22382500928406698396275097 16786875696305023797206323)
                ·
                  refine ⟨25180313544457535695809485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16786875696305023797206323 25180313544457535695809485)
                  ·
                    refine ⟨9442617579171575885928557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25180313544457535695809485 9442617579171575885928557)
                    ·
                      refine ⟨3540981592189340957223209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442617579171575885928557 3540981592189340957223209)
                      ·
                        rfl

theorem cell23_6896037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_6896037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896037 prefixEnd_6896037 := by exact prefixLift 6896037
  have htrace : WordTrace (prefixWord ++ tailWord_6896037) baseStart_6896037 baseEnd_6896037 := by
    simpa [prefixWord, tailWord_6896037, baseEnd_6896037] using wordTrace_append hprefix tailTrace_6896037
  have hstable : (prefixWord ++ tailWord_6896037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896037).length < 2 ^ (prefixWord ++ tailWord_6896037).sum := by decide
  have hdescent : baseEnd_6896037 < baseStart_6896037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896055 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 1, 2, 2]
def baseStart_6896055 : Nat := 118140960795 + 6896055 * 2 ^ 59
def prefixEnd_6896055 : Nat := 4983230072969 + 3 ^ 40 * 6896055 * 2
def baseEnd_6896055 : Nat := 3540990834841121886798127

theorem tailTrace_6896055 : CollatzResearch.WordTrace tailWord_6896055 prefixEnd_6896055 3540990834841121886798127 := by
  unfold tailWord_6896055
  simp only [CollatzResearch.WordTrace]
  refine ⟨251519789031777962273449619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167679859354518641515633079 251519789031777962273449619)
  ·
    refine ⟨377279683547666943410174429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251519789031777962273449619 377279683547666943410174429)
    ·
      refine ⟨141479881330375103778815411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377279683547666943410174429 141479881330375103778815411)
      ·
        refine ⟨212219821995562655668223117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141479881330375103778815411 212219821995562655668223117)
        ·
          refine ⟨79582433248335995875583669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212219821995562655668223117 79582433248335995875583669)
          ·
            refine ⟨7460853117031499613335969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79582433248335995875583669 7460853117031499613335969)
            ·
              refine ⟨5595639837773624710001977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460853117031499613335969 5595639837773624710001977)
              ·
                refine ⟨4196729878330218532501483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595639837773624710001977 4196729878330218532501483)
                ·
                  refine ⟨6295094817495327798752225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196729878330218532501483 6295094817495327798752225)
                  ·
                    refine ⟨4721321113121495849064169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6295094817495327798752225 4721321113121495849064169)
                    ·
                      refine ⟨3540990834841121886798127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721321113121495849064169 3540990834841121886798127)
                      ·
                        rfl

theorem cell23_6896055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_6896055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896055 prefixEnd_6896055 := by exact prefixLift 6896055
  have htrace : WordTrace (prefixWord ++ tailWord_6896055) baseStart_6896055 baseEnd_6896055 := by
    simpa [prefixWord, tailWord_6896055, baseEnd_6896055] using wordTrace_append hprefix tailTrace_6896055
  have hstable : (prefixWord ++ tailWord_6896055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896055).length < 2 ^ (prefixWord ++ tailWord_6896055).sum := by decide
  have hdescent : baseEnd_6896055 < baseStart_6896055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896127 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_6896127 : Nat := 118140960795 + 6896127 * 2 ^ 59
def prefixEnd_6896127 : Nat := 4983230072969 + 3 ^ 40 * 6896127 * 2
def baseEnd_6896127 : Nat := 3541027805448245605097795

theorem tailTrace_6896127 : CollatzResearch.WordTrace tailWord_6896127 prefixEnd_6896127 3541027805448245605097795 := by
  unfold tailWord_6896127
  simp only [CollatzResearch.WordTrace]
  refine ⟨251522415087517118570070635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167681610058344745713380423 251522415087517118570070635)
  ·
    refine ⟨377283622631275677855105953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251522415087517118570070635 377283622631275677855105953)
    ·
      refine ⟨282962716973456758391329465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377283622631275677855105953 282962716973456758391329465)
      ·
        refine ⟨212222037730092568793497099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282962716973456758391329465 212222037730092568793497099)
        ·
          refine ⟨318333056595138853190245649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212222037730092568793497099 318333056595138853190245649)
          ·
            refine ⟨238749792446354139892684237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318333056595138853190245649 238749792446354139892684237)
            ·
              refine ⟨89531172167382802459756589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238749792446354139892684237 89531172167382802459756589)
              ·
                refine ⟨33574189562768550922408721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89531172167382802459756589 33574189562768550922408721)
                ·
                  refine ⟨25180642172076413191806541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33574189562768550922408721 25180642172076413191806541)
                  ·
                    refine ⟨9442740814528654946927453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25180642172076413191806541 9442740814528654946927453)
                    ·
                      refine ⟨3541027805448245605097795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442740814528654946927453 3541027805448245605097795)
                      ·
                        rfl

theorem cell23_6896127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_6896127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896127 prefixEnd_6896127 := by exact prefixLift 6896127
  have htrace : WordTrace (prefixWord ++ tailWord_6896127) baseStart_6896127 baseEnd_6896127 := by
    simpa [prefixWord, tailWord_6896127, baseEnd_6896127] using wordTrace_append hprefix tailTrace_6896127
  have hstable : (prefixWord ++ tailWord_6896127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896127).length < 2 ^ (prefixWord ++ tailWord_6896127).sum := by decide
  have hdescent : baseEnd_6896127 < baseStart_6896127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896147 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 2, 5]
def baseStart_6896147 : Nat := 118140960795 + 6896147 * 2 ^ 59
def prefixEnd_6896147 : Nat := 4983230072969 + 3 ^ 40 * 6896147 * 2
def baseEnd_6896147 : Nat := 1180346025020445175615901

theorem tailTrace_6896147 : CollatzResearch.WordTrace tailWord_6896147 prefixEnd_6896147 1180346025020445175615901 := by
  unfold tailWord_6896147
  simp only [CollatzResearch.WordTrace]
  refine ⟨251523144547444661985798695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167682096364963107990532463 251523144547444661985798695)
  ·
    refine ⟨377284716821166992978698043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251523144547444661985798695 377284716821166992978698043)
    ·
      refine ⟨565927075231750489468047065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377284716821166992978698043 565927075231750489468047065)
      ·
        refine ⟨424445306423812867101035299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565927075231750489468047065 424445306423812867101035299)
        ·
          refine ⟨636667959635719300651552949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424445306423812867101035299 636667959635719300651552949)
          ·
            refine ⟨59687621215848684436083089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 636667959635719300651552949 59687621215848684436083089)
            ·
              refine ⟨44765715911886513327062317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59687621215848684436083089 44765715911886513327062317)
              ·
                refine ⟨16787143466957442497648369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44765715911886513327062317 16787143466957442497648369)
                ·
                  refine ⟨12590357600218081873236277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16787143466957442497648369 12590357600218081873236277)
                  ·
                    refine ⟨1180346025020445175615901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12590357600218081873236277 1180346025020445175615901)
                    ·
                      rfl

theorem cell23_6896147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 5].length) (baseStart_6896147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896147 prefixEnd_6896147 := by exact prefixLift 6896147
  have htrace : WordTrace (prefixWord ++ tailWord_6896147) baseStart_6896147 baseEnd_6896147 := by
    simpa [prefixWord, tailWord_6896147, baseEnd_6896147] using wordTrace_append hprefix tailTrace_6896147
  have hstable : (prefixWord ++ tailWord_6896147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896147).length < 2 ^ (prefixWord ++ tailWord_6896147).sum := by decide
  have hdescent : baseEnd_6896147 < baseStart_6896147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896168 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 5]
def baseStart_6896168 : Nat := 118140960795 + 6896168 * 2 ^ 59
def prefixEnd_6896168 : Nat := 4983230072969 + 3 ^ 40 * 6896168 * 2
def baseEnd_6896168 : Nat := 393449873128342216076123

theorem tailTrace_6896168 : CollatzResearch.WordTrace tailWord_6896168 prefixEnd_6896168 393449873128342216076123 := by
  unfold tailWord_6896168
  simp only [CollatzResearch.WordTrace]
  refine ⟨125761955240184291286156579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167682606986912388381542105 125761955240184291286156579)
  ·
    refine ⟨188642932860276436929234869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125761955240184291286156579 188642932860276436929234869)
    ·
      refine ⟨17685274955650915962115769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188642932860276436929234869 17685274955650915962115769)
      ·
        refine ⟨13263956216738186971586827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17685274955650915962115769 13263956216738186971586827)
        ·
          refine ⟨19895934325107280457380241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263956216738186971586827 19895934325107280457380241)
          ·
            refine ⟨14921950743830460343035181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19895934325107280457380241 14921950743830460343035181)
            ·
              refine ⟨5595731528936422628638193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14921950743830460343035181 5595731528936422628638193)
              ·
                refine ⟨4196798646702316971478645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595731528936422628638193 4196798646702316971478645)
                ·
                  refine ⟨393449873128342216076123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196798646702316971478645 393449873128342216076123)
                  ·
                    rfl

theorem cell23_6896168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 5].length) (baseStart_6896168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896168 prefixEnd_6896168 := by exact prefixLift 6896168
  have htrace : WordTrace (prefixWord ++ tailWord_6896168) baseStart_6896168 baseEnd_6896168 := by
    simpa [prefixWord, tailWord_6896168, baseEnd_6896168] using wordTrace_append hprefix tailTrace_6896168
  have hstable : (prefixWord ++ tailWord_6896168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896168).length < 2 ^ (prefixWord ++ tailWord_6896168).sum := by decide
  have hdescent : baseEnd_6896168 < baseStart_6896168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896184 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_6896184 : Nat := 118140960795 + 6896184 * 2 ^ 59
def prefixEnd_6896184 : Nat := 4983230072969 + 3 ^ 40 * 6896184 * 2
def baseEnd_6896184 : Nat := 3541057073845551882085033

theorem tailTrace_6896184 : CollatzResearch.WordTrace tailWord_6896184 prefixEnd_6896184 3541057073845551882085033 := by
  unfold tailWord_6896184
  simp only [CollatzResearch.WordTrace]
  refine ⟨125762247024155308652447803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167682996032207078203263737 125762247024155308652447803)
  ·
    refine ⟨188643370536232962978671705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125762247024155308652447803 188643370536232962978671705)
    ·
      refine ⟨141482527902174722234003779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188643370536232962978671705 141482527902174722234003779)
      ·
        refine ⟨212223791853262083351005669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141482527902174722234003779 212223791853262083351005669)
        ·
          refine ⟨39791960972486640628313563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212223791853262083351005669 39791960972486640628313563)
          ·
            refine ⟨59687941458729960942470345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39791960972486640628313563 59687941458729960942470345)
            ·
              refine ⟨44765956094047470706852759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59687941458729960942470345 44765956094047470706852759)
              ·
                refine ⟨67148934141071206060279139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44765956094047470706852759 67148934141071206060279139)
                ·
                  refine ⟨100723401211606809090418709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67148934141071206060279139 100723401211606809090418709)
                  ·
                    refine ⟨4721409431794069176113377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100723401211606809090418709 4721409431794069176113377)
                    ·
                      refine ⟨3541057073845551882085033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721409431794069176113377 3541057073845551882085033)
                      ·
                        rfl

theorem cell23_6896184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_6896184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896184 prefixEnd_6896184 := by exact prefixLift 6896184
  have htrace : WordTrace (prefixWord ++ tailWord_6896184) baseStart_6896184 baseEnd_6896184 := by
    simpa [prefixWord, tailWord_6896184, baseEnd_6896184] using wordTrace_append hprefix tailTrace_6896184
  have hstable : (prefixWord ++ tailWord_6896184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896184).length < 2 ^ (prefixWord ++ tailWord_6896184).sum := by decide
  have hdescent : baseEnd_6896184 < baseStart_6896184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896198 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6896198 : Nat := 118140960795 + 6896198 * 2 ^ 59
def prefixEnd_6896198 : Nat := 4983230072969 + 3 ^ 40 * 6896198 * 2
def baseEnd_6896198 : Nat := 1180354754191571609103323

theorem tailTrace_6896198 : CollatzResearch.WordTrace tailWord_6896198 prefixEnd_6896198 1180354754191571609103323 := by
  unfold tailWord_6896198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860156395945621802997039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167683336446839931797270165 7860156395945621802997039)
  ·
    refine ⟨11790234593918432704495559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7860156395945621802997039 11790234593918432704495559)
    ·
      refine ⟨17685351890877649056743339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790234593918432704495559 17685351890877649056743339)
      ·
        refine ⟨26528027836316473585115009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17685351890877649056743339 26528027836316473585115009)
        ·
          refine ⟨19896020877237355188836257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26528027836316473585115009 19896020877237355188836257)
          ·
            refine ⟨14922015657928016391627193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19896020877237355188836257 14922015657928016391627193)
            ·
              refine ⟨11191511743446012293720395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14922015657928016391627193 11191511743446012293720395)
              ·
                refine ⟨16787267615169018440580593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11191511743446012293720395 16787267615169018440580593)
                ·
                  refine ⟨12590450711376763830435445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16787267615169018440580593 12590450711376763830435445)
                  ·
                    refine ⟨1180354754191571609103323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12590450711376763830435445 1180354754191571609103323)
                    ·
                      rfl

theorem cell23_6896198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6896198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896198 prefixEnd_6896198 := by exact prefixLift 6896198
  have htrace : WordTrace (prefixWord ++ tailWord_6896198) baseStart_6896198 baseEnd_6896198 := by
    simpa [prefixWord, tailWord_6896198, baseEnd_6896198] using wordTrace_append hprefix tailTrace_6896198
  have hstable : (prefixWord ++ tailWord_6896198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896198).length < 2 ^ (prefixWord ++ tailWord_6896198).sum := by decide
  have hdescent : baseEnd_6896198 < baseStart_6896198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896227 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6896227 : Nat := 118140960795 + 6896227 * 2 ^ 59
def prefixEnd_6896227 : Nat := 4983230072969 + 3 ^ 40 * 6896227 * 2
def baseEnd_6896227 : Nat := 3541079153513695213847335

theorem tailTrace_6896227 : CollatzResearch.WordTrace tailWord_6896227 prefixEnd_6896227 3541079153513695213847335 := by
  unfold tailWord_6896227
  simp only [CollatzResearch.WordTrace]
  refine ⟨251526062387154835648710935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167684041591436557099140623 251526062387154835648710935)
  ·
    refine ⟨377289093580732253473066403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251526062387154835648710935 377289093580732253473066403)
    ·
      refine ⟨565933640371098380209599605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377289093580732253473066403 565933640371098380209599605)
      ·
        refine ⟨53056278784790473144649963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 565933640371098380209599605 53056278784790473144649963)
        ·
          refine ⟨79584418177185709716974945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53056278784790473144649963 79584418177185709716974945)
          ·
            refine ⟨59688313632889282287731209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79584418177185709716974945 59688313632889282287731209)
            ·
              refine ⟨44766235224666961715798407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59688313632889282287731209 44766235224666961715798407)
              ·
                refine ⟨67149352837000442573697611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44766235224666961715798407 67149352837000442573697611)
                ·
                  refine ⟨100724029255500663860546417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67149352837000442573697611 100724029255500663860546417)
                  ·
                    refine ⟨75543021941625497895409813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100724029255500663860546417 75543021941625497895409813)
                    ·
                      refine ⟨3541079153513695213847335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75543021941625497895409813 3541079153513695213847335)
                      ·
                        rfl

theorem cell23_6896227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6896227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896227 prefixEnd_6896227 := by exact prefixLift 6896227
  have htrace : WordTrace (prefixWord ++ tailWord_6896227) baseStart_6896227 baseEnd_6896227 := by
    simpa [prefixWord, tailWord_6896227, baseEnd_6896227] using wordTrace_append hprefix tailTrace_6896227
  have hstable : (prefixWord ++ tailWord_6896227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896227).length < 2 ^ (prefixWord ++ tailWord_6896227).sum := by decide
  have hdescent : baseEnd_6896227 < baseStart_6896227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896261 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_6896261 : Nat := 118140960795 + 6896261 * 2 ^ 59
def prefixEnd_6896261 : Nat := 4983230072969 + 3 ^ 40 * 6896261 * 2
def baseEnd_6896261 : Nat := 3541096611855948080822179

theorem tailTrace_6896261 : CollatzResearch.WordTrace tailWord_6896261 prefixEnd_6896261 3541096611855948080822179 := by
  unfold tailWord_6896261
  simp only [CollatzResearch.WordTrace]
  refine ⟨251527302469031659455448637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167684868312687772970299091 251527302469031659455448637)
  ·
    refine ⟨94322738425886872295793239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251527302469031659455448637 94322738425886872295793239)
    ·
      refine ⟨141484107638830308443689859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94322738425886872295793239 141484107638830308443689859)
      ·
        refine ⟨212226161458245462665534789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141484107638830308443689859 212226161458245462665534789)
        ·
          refine ⟨39792405273421024249787773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212226161458245462665534789 39792405273421024249787773)
          ·
            refine ⟨14922151977532884093670415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39792405273421024249787773 14922151977532884093670415)
            ·
              refine ⟨22383227966299326140505623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14922151977532884093670415 22383227966299326140505623)
              ·
                refine ⟨33574841949448989210758435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22383227966299326140505623 33574841949448989210758435)
                ·
                  refine ⟨50362262924173483816137653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33574841949448989210758435 50362262924173483816137653)
                  ·
                    refine ⟨4721462149141264107762905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50362262924173483816137653 4721462149141264107762905)
                    ·
                      refine ⟨3541096611855948080822179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721462149141264107762905 3541096611855948080822179)
                      ·
                        rfl

theorem cell23_6896261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_6896261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896261 prefixEnd_6896261 := by exact prefixLift 6896261
  have htrace : WordTrace (prefixWord ++ tailWord_6896261) baseStart_6896261 baseEnd_6896261 := by
    simpa [prefixWord, tailWord_6896261, baseEnd_6896261] using wordTrace_append hprefix tailTrace_6896261
  have hstable : (prefixWord ++ tailWord_6896261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896261).length < 2 ^ (prefixWord ++ tailWord_6896261).sum := by decide
  have hdescent : baseEnd_6896261 < baseStart_6896261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896267 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 3, 6]
def baseStart_6896267 : Nat := 118140960795 + 6896267 * 2 ^ 59
def prefixEnd_6896267 : Nat := 4983230072969 + 3 ^ 40 * 6896267 * 2
def baseEnd_6896267 : Nat := 1180366564246625019115717

theorem tailTrace_6896267 : CollatzResearch.WordTrace tailWord_6896267 prefixEnd_6896267 1180366564246625019115717 := by
  unfold tailWord_6896267
  simp only [CollatzResearch.WordTrace]
  refine ⟨251527521307009922480167055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167685014204673281653444703 251527521307009922480167055)
  ·
    refine ⟨377291281960514883720250583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251527521307009922480167055 377291281960514883720250583)
    ·
      refine ⟨565936922940772325580375875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377291281960514883720250583 565936922940772325580375875)
      ·
        refine ⟨848905384411158488370563813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565936922940772325580375875 848905384411158488370563813)
        ·
          refine ⟨159169759577092216569480715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 848905384411158488370563813 159169759577092216569480715)
          ·
            refine ⟨238754639365638324854221073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159169759577092216569480715 238754639365638324854221073)
            ·
              refine ⟨179065979524228743640665805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238754639365638324854221073 179065979524228743640665805)
              ·
                refine ⟨67149742321585778865249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179065979524228743640665805 67149742321585778865249677)
                ·
                  refine ⟨25181153370594667074468629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67149742321585778865249677 25181153370594667074468629)
                  ·
                    refine ⟨1180366564246625019115717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25181153370594667074468629 1180366564246625019115717)
                    ·
                      rfl

theorem cell23_6896267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_6896267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896267 prefixEnd_6896267 := by exact prefixLift 6896267
  have htrace : WordTrace (prefixWord ++ tailWord_6896267) baseStart_6896267 baseEnd_6896267 := by
    simpa [prefixWord, tailWord_6896267, baseEnd_6896267] using wordTrace_append hprefix tailTrace_6896267
  have hstable : (prefixWord ++ tailWord_6896267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896267).length < 2 ^ (prefixWord ++ tailWord_6896267).sum := by decide
  have hdescent : baseEnd_6896267 < baseStart_6896267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896301 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_6896301 : Nat := 118140960795 + 6896301 * 2 ^ 59
def prefixEnd_6896301 : Nat := 4983230072969 + 3 ^ 40 * 6896301 * 2
def baseEnd_6896301 : Nat := 1180372383694042641440665

theorem tailTrace_6896301 : CollatzResearch.WordTrace tailWord_6896301 prefixEnd_6896301 1180372383694042641440665 := by
  unfold tailWord_6896301
  simp only [CollatzResearch.WordTrace]
  refine ⟨251528761388886746286904757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167685840925924497524603171 251528761388886746286904757)
  ·
    refine ⟨23580821380208132464397321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251528761388886746286904757 23580821380208132464397321)
    ·
      refine ⟨17685616035156099348297991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23580821380208132464397321 17685616035156099348297991)
      ·
        refine ⟨26528424052734149022446987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17685616035156099348297991 26528424052734149022446987)
        ·
          refine ⟨39792636079101223533670481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26528424052734149022446987 39792636079101223533670481)
          ·
            refine ⟨29844477059325917650252861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39792636079101223533670481 29844477059325917650252861)
            ·
              refine ⟨11191678897247219118844823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29844477059325917650252861 11191678897247219118844823)
              ·
                refine ⟨16787518345870828678267235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11191678897247219118844823 16787518345870828678267235)
                ·
                  refine ⟨25181277518806243017400853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16787518345870828678267235 25181277518806243017400853)
                  ·
                    refine ⟨1180372383694042641440665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25181277518806243017400853 1180372383694042641440665)
                    ·
                      rfl

theorem cell23_6896301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_6896301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896301 prefixEnd_6896301 := by exact prefixLift 6896301
  have htrace : WordTrace (prefixWord ++ tailWord_6896301) baseStart_6896301 baseEnd_6896301 := by
    simpa [prefixWord, tailWord_6896301, baseEnd_6896301] using wordTrace_append hprefix tailTrace_6896301
  have hstable : (prefixWord ++ tailWord_6896301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896301).length < 2 ^ (prefixWord ++ tailWord_6896301).sum := by decide
  have hdescent : baseEnd_6896301 < baseStart_6896301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896384 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_6896384 : Nat := 118140960795 + 6896384 * 2 ^ 59
def prefixEnd_6896384 : Nat := 4983230072969 + 3 ^ 40 * 6896384 * 2
def baseEnd_6896384 : Nat := 3541159769976451099584113

theorem tailTrace_6896384 : CollatzResearch.WordTrace tailWord_6896384 prefixEnd_6896384 3541159769976451099584113 := by
  unfold tailWord_6896384
  simp only [CollatzResearch.WordTrace]
  refine ⟨125765894323793025731088103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167687859098390700974784137 125765894323793025731088103)
  ·
    refine ⟨188648841485689538596632155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125765894323793025731088103 188648841485689538596632155)
    ·
      refine ⟨282973262228534307894948233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188648841485689538596632155 282973262228534307894948233)
      ·
        refine ⟨212229946671400730921211175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282973262228534307894948233 212229946671400730921211175)
        ·
          refine ⟨318344920007101096381816763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212229946671400730921211175 318344920007101096381816763)
          ·
            refine ⟨477517380010651644572725145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318344920007101096381816763 477517380010651644572725145)
            ·
              refine ⟨358138035007988733429543859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477517380010651644572725145 358138035007988733429543859)
              ·
                refine ⟨537207052511983100144315789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358138035007988733429543859 537207052511983100144315789)
                ·
                  refine ⟨201452644691993662554118421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537207052511983100144315789 201452644691993662554118421)
                  ·
                    refine ⟨9443092719937202932224301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201452644691993662554118421 9443092719937202932224301)
                    ·
                      refine ⟨3541159769976451099584113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9443092719937202932224301 3541159769976451099584113)
                      ·
                        rfl

theorem cell23_6896384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_6896384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896384 prefixEnd_6896384 := by exact prefixLift 6896384
  have htrace : WordTrace (prefixWord ++ tailWord_6896384) baseStart_6896384 baseEnd_6896384 := by
    simpa [prefixWord, tailWord_6896384, baseEnd_6896384] using wordTrace_append hprefix tailTrace_6896384
  have hstable : (prefixWord ++ tailWord_6896384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896384).length < 2 ^ (prefixWord ++ tailWord_6896384).sum := by decide
  have hdescent : baseEnd_6896384 < baseStart_6896384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896415 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 2, 2, 2]
def baseStart_6896415 : Nat := 118140960795 + 6896415 * 2 ^ 59
def prefixEnd_6896415 : Nat := 4983230072969 + 3 ^ 40 * 6896415 * 2
def baseEnd_6896415 : Nat := 3541175687876740478296471

theorem tailTrace_6896415 : CollatzResearch.WordTrace tailWord_6896415 prefixEnd_6896415 3541175687876740478296471 := by
  unfold tailWord_6896415
  simp only [CollatzResearch.WordTrace]
  refine ⟨251532919310473743756554699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167688612873649162504369799 251532919310473743756554699)
  ·
    refine ⟨377299378965710615634832049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251532919310473743756554699 377299378965710615634832049)
    ·
      refine ⟨282974534224282961726124037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377299378965710615634832049 282974534224282961726124037)
      ·
        refine ⟨53057725167053055323648257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282974534224282961726124037 53057725167053055323648257)
        ·
          refine ⟨39793293875289791492736193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53057725167053055323648257 39793293875289791492736193)
          ·
            refine ⟨29844970406467343619552145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39793293875289791492736193 29844970406467343619552145)
            ·
              refine ⟨22383727804850507714664109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29844970406467343619552145 22383727804850507714664109)
              ·
                refine ⟨8393897926818940392999041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22383727804850507714664109 8393897926818940392999041)
                ·
                  refine ⟨6295423445114205294749281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8393897926818940392999041 6295423445114205294749281)
                  ·
                    refine ⟨4721567583835653971061961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6295423445114205294749281 4721567583835653971061961)
                    ·
                      refine ⟨3541175687876740478296471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721567583835653971061961 3541175687876740478296471)
                      ·
                        rfl

theorem cell23_6896415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_6896415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896415 prefixEnd_6896415 := by exact prefixLift 6896415
  have htrace : WordTrace (prefixWord ++ tailWord_6896415) baseStart_6896415 baseEnd_6896415 := by
    simpa [prefixWord, tailWord_6896415, baseEnd_6896415] using wordTrace_append hprefix tailTrace_6896415
  have hstable : (prefixWord ++ tailWord_6896415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896415).length < 2 ^ (prefixWord ++ tailWord_6896415).sum := by decide
  have hdescent : baseEnd_6896415 < baseStart_6896415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896436 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_6896436 : Nat := 118140960795 + 6896436 * 2 ^ 59
def prefixEnd_6896436 : Nat := 4983230072969 + 3 ^ 40 * 6896436 * 2
def baseEnd_6896436 : Nat := 3541186470970484896133875

theorem tailTrace_6896436 : CollatzResearch.WordTrace tailWord_6896436 prefixEnd_6896436 3541186470970484896133875 := by
  unfold tailWord_6896436
  simp only [CollatzResearch.WordTrace]
  refine ⟨125766842621698832171534581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167689123495598442895379441 125766842621698832171534581)
  ·
    refine ⟨11790641495784265516081367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125766842621698832171534581 11790641495784265516081367)
    ·
      refine ⟨17685962243676398274122051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790641495784265516081367 17685962243676398274122051)
      ·
        refine ⟨26528943365514597411183077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17685962243676398274122051 26528943365514597411183077)
        ·
          refine ⟨4974176881033987014596827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26528943365514597411183077 4974176881033987014596827)
          ·
            refine ⟨7461265321550980521895241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974176881033987014596827 7461265321550980521895241)
            ·
              refine ⟨5595948991163235391421431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7461265321550980521895241 5595948991163235391421431)
              ·
                refine ⟨8393923486744853087132147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595948991163235391421431 8393923486744853087132147)
                ·
                  refine ⟨12590885230117279630698221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393923486744853087132147 12590885230117279630698221)
                  ·
                    refine ⟨4721581961293979861511833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12590885230117279630698221 4721581961293979861511833)
                    ·
                      refine ⟨3541186470970484896133875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721581961293979861511833 3541186470970484896133875)
                      ·
                        rfl

theorem cell23_6896436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_6896436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896436 prefixEnd_6896436 := by exact prefixLift 6896436
  have htrace : WordTrace (prefixWord ++ tailWord_6896436) baseStart_6896436 baseEnd_6896436 := by
    simpa [prefixWord, tailWord_6896436, baseEnd_6896436] using wordTrace_append hprefix tailTrace_6896436
  have hstable : (prefixWord ++ tailWord_6896436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896436).length < 2 ^ (prefixWord ++ tailWord_6896436).sum := by decide
  have hdescent : baseEnd_6896436 < baseStart_6896436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896471 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_6896471 : Nat := 118140960795 + 6896471 * 2 ^ 59
def prefixEnd_6896471 : Nat := 4983230072969 + 3 ^ 40 * 6896471 * 2
def baseEnd_6896471 : Nat := 3541204442793392259196213

theorem tailTrace_6896471 : CollatzResearch.WordTrace tailWord_6896471 prefixEnd_6896471 3541204442793392259196213 := by
  unfold tailWord_6896471
  simp only [CollatzResearch.WordTrace]
  refine ⟨251534961798270865320593267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167689974532180576880395511 251534961798270865320593267)
  ·
    refine ⟨377302442697406297980889901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251534961798270865320593267 377302442697406297980889901)
    ·
      refine ⟨141488416011527361742833713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377302442697406297980889901 141488416011527361742833713)
      ·
        refine ⟨106116312008645521307125285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141488416011527361742833713 106116312008645521307125285)
        ·
          refine ⟨19896808501621035245085991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106116312008645521307125285 19896808501621035245085991)
          ·
            refine ⟨29845212752431552867628987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19896808501621035245085991 29845212752431552867628987)
            ·
              refine ⟨44767819128647329301443481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29845212752431552867628987 44767819128647329301443481)
              ·
                refine ⟨33575864346485496976082611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44767819128647329301443481 33575864346485496976082611)
                ·
                  refine ⟨50363796519728245464123917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33575864346485496976082611 50363796519728245464123917)
                  ·
                    refine ⟨18886423694898092049046469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50363796519728245464123917 18886423694898092049046469)
                    ·
                      refine ⟨3541204442793392259196213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18886423694898092049046469 3541204442793392259196213)
                      ·
                        rfl

theorem cell23_6896471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_6896471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896471 prefixEnd_6896471 := by exact prefixLift 6896471
  have htrace : WordTrace (prefixWord ++ tailWord_6896471) baseStart_6896471 baseEnd_6896471 := by
    simpa [prefixWord, tailWord_6896471, baseEnd_6896471] using wordTrace_append hprefix tailTrace_6896471
  have hstable : (prefixWord ++ tailWord_6896471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896471).length < 2 ^ (prefixWord ++ tailWord_6896471).sum := by decide
  have hdescent : baseEnd_6896471 < baseStart_6896471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896481 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_6896481 : Nat := 118140960795 + 6896481 * 2 ^ 59
def prefixEnd_6896481 : Nat := 4983230072969 + 3 ^ 40 * 6896481 * 2
def baseEnd_6896481 : Nat := 1180403192533312406690389

theorem tailTrace_6896481 : CollatzResearch.WordTrace tailWord_6896481 prefixEnd_6896481 1180403192533312406690389 := by
  unfold tailWord_6896481
  simp only [CollatzResearch.WordTrace]
  refine ⟨251535326528234637028457297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167690217685489758018971531 251535326528234637028457297)
  ·
    refine ⟨188651494896175977771342973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251535326528234637028457297 188651494896175977771342973)
    ·
      refine ⟨70744310586065991664253615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188651494896175977771342973 70744310586065991664253615)
      ·
        refine ⟨106116465879098987496380423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70744310586065991664253615 106116465879098987496380423)
        ·
          refine ⟨159174698818648481244570635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106116465879098987496380423 159174698818648481244570635)
          ·
            refine ⟨238762048227972721866855953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159174698818648481244570635 238762048227972721866855953)
            ·
              refine ⟨179071536170979541400141965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238762048227972721866855953 179071536170979541400141965)
              ·
                refine ⟨67151826064117328025053237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179071536170979541400141965 67151826064117328025053237)
                ·
                  refine ⟨6295483693510999502348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67151826064117328025053237 6295483693510999502348741)
                  ·
                    refine ⟨1180403192533312406690389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6295483693510999502348741 1180403192533312406690389)
                    ·
                      rfl

theorem cell23_6896481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_6896481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896481 prefixEnd_6896481 := by exact prefixLift 6896481
  have htrace : WordTrace (prefixWord ++ tailWord_6896481) baseStart_6896481 baseEnd_6896481 := by
    simpa [prefixWord, tailWord_6896481, baseEnd_6896481] using wordTrace_append hprefix tailTrace_6896481
  have hstable : (prefixWord ++ tailWord_6896481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896481).length < 2 ^ (prefixWord ++ tailWord_6896481).sum := by decide
  have hdescent : baseEnd_6896481 < baseStart_6896481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896491 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3]
def baseStart_6896491 : Nat := 118140960795 + 6896491 * 2 ^ 59
def prefixEnd_6896491 : Nat := 4983230072969 + 3 ^ 40 * 6896491 * 2
def baseEnd_6896491 : Nat := 3541214712406482180946121

theorem tailTrace_6896491 : CollatzResearch.WordTrace tailWord_6896491 prefixEnd_6896491 3541214712406482180946121 := by
  unfold tailWord_6896491
  simp only [CollatzResearch.WordTrace]
  refine ⟨251535691258198408736321327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167690460838798939157547551 251535691258198408736321327)
  ·
    refine ⟨377303536887297613104481991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251535691258198408736321327 377303536887297613104481991)
    ·
      refine ⟨565955305330946419656722987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377303536887297613104481991 565955305330946419656722987)
      ·
        refine ⟨848932957996419629485084481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565955305330946419656722987 848932957996419629485084481)
        ·
          refine ⟨636699718497314722113813361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848932957996419629485084481 636699718497314722113813361)
          ·
            refine ⟨477524788872986041585360021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636699718497314722113813361 477524788872986041585360021)
            ·
              refine ⟨22383974478421220699313751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 477524788872986041585360021 22383974478421220699313751)
              ·
                refine ⟨33575961717631831048970627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22383974478421220699313751 33575961717631831048970627)
                ·
                  refine ⟨50363942576447746573455941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33575961717631831048970627 50363942576447746573455941)
                  ·
                    refine ⟨9443239233083952482522989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50363942576447746573455941 9443239233083952482522989)
                    ·
                      refine ⟨3541214712406482180946121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9443239233083952482522989 3541214712406482180946121)
                      ·
                        rfl

theorem cell23_6896491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3].length) (baseStart_6896491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896491 prefixEnd_6896491 := by exact prefixLift 6896491
  have htrace : WordTrace (prefixWord ++ tailWord_6896491) baseStart_6896491 baseEnd_6896491 := by
    simpa [prefixWord, tailWord_6896491, baseEnd_6896491] using wordTrace_append hprefix tailTrace_6896491
  have hstable : (prefixWord ++ tailWord_6896491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896491).length < 2 ^ (prefixWord ++ tailWord_6896491).sum := by decide
  have hdescent : baseEnd_6896491 < baseStart_6896491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896565 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6896565 : Nat := 118140960795 + 6896565 * 2 ^ 59
def prefixEnd_6896565 : Nat := 4983230072969 + 3 ^ 40 * 6896565 * 2
def baseEnd_6896565 : Nat := 3541252709974914891420781

theorem tailTrace_6896565 : CollatzResearch.WordTrace tailWord_6896565 prefixEnd_6896565 3541252709974914891420781 := by
  unfold tailWord_6896565
  simp only [CollatzResearch.WordTrace]
  refine ⟨251538390259930319374515149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167692260173286879583010099 251538390259930319374515149)
  ·
    refine ⟨94326896347473869765443181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251538390259930319374515149 94326896347473869765443181)
    ·
      refine ⟨35372586130302701162041193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94326896347473869765443181 35372586130302701162041193)
      ·
        refine ⟨26529439597727025871530895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35372586130302701162041193 26529439597727025871530895)
        ·
          refine ⟨39794159396590538807296343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26529439597727025871530895 39794159396590538807296343)
          ·
            refine ⟨59691239094885808210944515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39794159396590538807296343 59691239094885808210944515)
            ·
              refine ⟨89536858642328712316416773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59691239094885808210944515 89536858642328712316416773)
              ·
                refine ⟨16788160995436633559328145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89536858642328712316416773 16788160995436633559328145)
                ·
                  refine ⟨12591120746577475169496109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16788160995436633559328145 12591120746577475169496109)
                  ·
                    refine ⟨4721670279966553188561041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12591120746577475169496109 4721670279966553188561041)
                    ·
                      refine ⟨3541252709974914891420781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721670279966553188561041 3541252709974914891420781)
                      ·
                        rfl

theorem cell23_6896565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6896565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896565 prefixEnd_6896565 := by exact prefixLift 6896565
  have htrace : WordTrace (prefixWord ++ tailWord_6896565) baseStart_6896565 baseEnd_6896565 := by
    simpa [prefixWord, tailWord_6896565, baseEnd_6896565] using wordTrace_append hprefix tailTrace_6896565
  have hstable : (prefixWord ++ tailWord_6896565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896565).length < 2 ^ (prefixWord ++ tailWord_6896565).sum := by decide
  have hdescent : baseEnd_6896565 < baseStart_6896565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896588 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_6896588 : Nat := 118140960795 + 6896588 * 2 ^ 59
def prefixEnd_6896588 : Nat := 4983230072969 + 3 ^ 40 * 6896588 * 2
def baseEnd_6896588 : Nat := 1180421506676656100477725

theorem tailTrace_6896588 : CollatzResearch.WordTrace tailWord_6896588 prefixEnd_6896588 1180421506676656100477725 := by
  unfold tailWord_6896588
  simp only [CollatzResearch.WordTrace]
  refine ⟨125769614569423497151301209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167692819425897996201734945 125769614569423497151301209)
  ·
    refine ⟨94327210927067622863475907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125769614569423497151301209 94327210927067622863475907)
    ·
      refine ⟨141490816390601434295213861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94327210927067622863475907 141490816390601434295213861)
      ·
        refine ⟨26529528073237768930352599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141490816390601434295213861 26529528073237768930352599)
        ·
          refine ⟨39794292109856653395528899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26529528073237768930352599 39794292109856653395528899)
          ·
            refine ⟨59691438164784980093293349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39794292109856653395528899 59691438164784980093293349)
            ·
              refine ⟨11192144655897183767492503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59691438164784980093293349 11192144655897183767492503)
              ·
                refine ⟨16788216983845775651238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192144655897183767492503 16788216983845775651238755)
                ·
                  refine ⟨25182325475768663476858133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16788216983845775651238755 25182325475768663476858133)
                  ·
                    refine ⟨1180421506676656100477725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25182325475768663476858133 1180421506676656100477725)
                    ·
                      rfl

theorem cell23_6896588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_6896588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896588 prefixEnd_6896588 := by exact prefixLift 6896588
  have htrace : WordTrace (prefixWord ++ tailWord_6896588) baseStart_6896588 baseEnd_6896588 := by
    simpa [prefixWord, tailWord_6896588, baseEnd_6896588] using wordTrace_append hprefix tailTrace_6896588
  have hstable : (prefixWord ++ tailWord_6896588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896588).length < 2 ^ (prefixWord ++ tailWord_6896588).sum := by decide
  have hdescent : baseEnd_6896588 < baseStart_6896588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896642 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6896642 : Nat := 118140960795 + 6896642 * 2 ^ 59
def prefixEnd_6896642 : Nat := 4983230072969 + 3 ^ 40 * 6896642 * 2
def baseEnd_6896642 : Nat := 3541292247985311090157927

theorem tailTrace_6896642 : CollatzResearch.WordTrace tailWord_6896642 prefixEnd_6896642 3541292247985311090157927 := by
  unfold tailWord_6896642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62885299670162840381267045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167694132453767574350045453 62885299670162840381267045)
  ·
    refine ⟨11790993688155532571487571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62885299670162840381267045 11790993688155532571487571)
    ·
      refine ⟨17686490532233298857231357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790993688155532571487571 17686490532233298857231357)
      ·
        refine ⟨6632433949587487071461759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17686490532233298857231357 6632433949587487071461759)
        ·
          refine ⟨9948650924381230607192639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632433949587487071461759 9948650924381230607192639)
          ·
            refine ⟨14922976386571845910788959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9948650924381230607192639 14922976386571845910788959)
            ·
              refine ⟨22384464579857768866183439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14922976386571845910788959 22384464579857768866183439)
              ·
                refine ⟨33576696869786653299275159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22384464579857768866183439 33576696869786653299275159)
                ·
                  refine ⟨50365045304679979948912739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33576696869786653299275159 50365045304679979948912739)
                  ·
                    refine ⟨75547567957019969923369109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50365045304679979948912739 75547567957019969923369109)
                    ·
                      refine ⟨3541292247985311090157927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75547567957019969923369109 3541292247985311090157927)
                      ·
                        rfl

theorem cell23_6896642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6896642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896642 prefixEnd_6896642 := by exact prefixLift 6896642
  have htrace : WordTrace (prefixWord ++ tailWord_6896642) baseStart_6896642 baseEnd_6896642 := by
    simpa [prefixWord, tailWord_6896642, baseEnd_6896642] using wordTrace_append hprefix tailTrace_6896642
  have hstable : (prefixWord ++ tailWord_6896642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896642).length < 2 ^ (prefixWord ++ tailWord_6896642).sum := by decide
  have hdescent : baseEnd_6896642 < baseStart_6896642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896688 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_6896688 : Nat := 118140960795 + 6896688 * 2 ^ 59
def prefixEnd_6896688 : Nat := 4983230072969 + 3 ^ 40 * 6896688 * 2
def baseEnd_6896688 : Nat := 3541315868095417910182715

theorem tailTrace_6896688 : CollatzResearch.WordTrace tailWord_6896688 prefixEnd_6896688 3541315868095417910182715 := by
  unfold tailWord_6896688
  simp only [CollatzResearch.WordTrace]
  refine ⟨125771438219242355690621359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167695250958989807587495145 125771438219242355690621359)
  ·
    refine ⟨188657157328863533535932039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125771438219242355690621359 188657157328863533535932039)
    ·
      refine ⟨282985735993295300303898059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188657157328863533535932039 282985735993295300303898059)
      ·
        refine ⟨424478603989942950455847089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282985735993295300303898059 424478603989942950455847089)
        ·
          refine ⟨318358952992457212841885317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424478603989942950455847089 318358952992457212841885317)
          ·
            refine ⟨59692303686085727407853497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318358952992457212841885317 59692303686085727407853497)
            ·
              refine ⟨44769227764564295555890123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59692303686085727407853497 44769227764564295555890123)
              ·
                refine ⟨67153841646846443333835185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44769227764564295555890123 67153841646846443333835185)
                ·
                  refine ⟨50365381235134832500376389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67153841646846443333835185 50365381235134832500376389)
                  ·
                    refine ⟨9443508981587781093820573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50365381235134832500376389 9443508981587781093820573)
                    ·
                      refine ⟨3541315868095417910182715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9443508981587781093820573 3541315868095417910182715)
                      ·
                        rfl

theorem cell23_6896688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_6896688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896688 prefixEnd_6896688 := by exact prefixLift 6896688
  have htrace : WordTrace (prefixWord ++ tailWord_6896688) baseStart_6896688 baseEnd_6896688 := by
    simpa [prefixWord, tailWord_6896688, baseEnd_6896688] using wordTrace_append hprefix tailTrace_6896688
  have hstable : (prefixWord ++ tailWord_6896688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896688).length < 2 ^ (prefixWord ++ tailWord_6896688).sum := by decide
  have hdescent : baseEnd_6896688 < baseStart_6896688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896698 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_6896698 : Nat := 118140960795 + 6896698 * 2 ^ 59
def prefixEnd_6896698 : Nat := 4983230072969 + 3 ^ 40 * 6896698 * 2
def baseEnd_6896698 : Nat := 3541321002901962871057669

theorem tailTrace_6896698 : CollatzResearch.WordTrace tailWord_6896698 prefixEnd_6896698 3541321002901962871057669 := by
  unfold tailWord_6896698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62885810292112120772276687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167695494112298988726071165 62885810292112120772276687)
  ·
    refine ⟨94328715438168181158415031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62885810292112120772276687 94328715438168181158415031)
    ·
      refine ⟨141493073157252271737622547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94328715438168181158415031 141493073157252271737622547)
      ·
        refine ⟨212239609735878407606433821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141493073157252271737622547 212239609735878407606433821)
        ·
          refine ⟨79589853650954402852412683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212239609735878407606433821 79589853650954402852412683)
          ·
            refine ⟨119384780476431604278619025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79589853650954402852412683 119384780476431604278619025)
            ·
              refine ⟨89538585357323703208964269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119384780476431604278619025 89538585357323703208964269)
              ·
                refine ⟨33576969508996388703361601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89538585357323703208964269 33576969508996388703361601)
                ·
                  refine ⟨25182727131747291527521201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33576969508996388703361601 25182727131747291527521201)
                  ·
                    refine ⟨18887045348810468645640901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25182727131747291527521201 18887045348810468645640901)
                    ·
                      refine ⟨3541321002901962871057669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18887045348810468645640901 3541321002901962871057669)
                      ·
                        rfl

theorem cell23_6896698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_6896698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896698 prefixEnd_6896698 := by exact prefixLift 6896698
  have htrace : WordTrace (prefixWord ++ tailWord_6896698) baseStart_6896698 baseEnd_6896698 := by
    simpa [prefixWord, tailWord_6896698, baseEnd_6896698] using wordTrace_append hprefix tailTrace_6896698
  have hstable : (prefixWord ++ tailWord_6896698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896698).length < 2 ^ (prefixWord ++ tailWord_6896698).sum := by decide
  have hdescent : baseEnd_6896698 < baseStart_6896698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896725 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 5]
def baseStart_6896725 : Nat := 118140960795 + 6896725 * 2 ^ 59
def prefixEnd_6896725 : Nat := 4983230072969 + 3 ^ 40 * 6896725 * 2
def baseEnd_6896725 : Nat := 393481651875514918380005

theorem tailTrace_6896725 : CollatzResearch.WordTrace tailWord_6896725 prefixEnd_6896725 393481651875514918380005 := by
  unfold tailWord_6896725
  simp only [CollatzResearch.WordTrace]
  refine ⟨251544225939350666700339629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167696150626233777800226419 251544225939350666700339629)
  ·
    refine ⟨94329084727256500012627361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251544225939350666700339629 94329084727256500012627361)
    ·
      refine ⟨70746813545442375009470521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94329084727256500012627361 70746813545442375009470521)
      ·
        refine ⟨53060110159081781257102891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70746813545442375009470521 53060110159081781257102891)
        ·
          refine ⟨79590165238622671885654337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53060110159081781257102891 79590165238622671885654337)
          ·
            refine ⟨59692623928967003914240753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79590165238622671885654337 59692623928967003914240753)
            ·
              refine ⟨44769467946725252935680565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59692623928967003914240753 44769467946725252935680565)
              ·
                refine ⟨4197137620005492462720053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44769467946725252935680565 4197137620005492462720053)
                ·
                  refine ⟨393481651875514918380005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197137620005492462720053 393481651875514918380005)
                  ·
                    rfl

theorem cell23_6896725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_6896725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896725 prefixEnd_6896725 := by exact prefixLift 6896725
  have htrace : WordTrace (prefixWord ++ tailWord_6896725) baseStart_6896725 baseEnd_6896725 := by
    simpa [prefixWord, tailWord_6896725, baseEnd_6896725] using wordTrace_append hprefix tailTrace_6896725
  have hstable : (prefixWord ++ tailWord_6896725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896725).length < 2 ^ (prefixWord ++ tailWord_6896725).sum := by decide
  have hdescent : baseEnd_6896725 < baseStart_6896725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896745 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 5, 2]
def baseStart_6896745 : Nat := 118140960795 + 6896745 * 2 ^ 59
def prefixEnd_6896745 : Nat := 4983230072969 + 3 ^ 40 * 6896745 * 2
def baseEnd_6896745 : Nat := 3541345136492724187169953

theorem tailTrace_6896745 : CollatzResearch.WordTrace tailWord_6896745 prefixEnd_6896745 3541345136492724187169953 := by
  unfold tailWord_6896745
  simp only [CollatzResearch.WordTrace]
  refine ⟨251544955399278210116067689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167696636932852140077378459 251544955399278210116067689)
  ·
    refine ⟨188658716549458657587050767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251544955399278210116067689 188658716549458657587050767)
    ·
      refine ⟨282988074824187986380576151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188658716549458657587050767 282988074824187986380576151)
      ·
        refine ⟨424482112236281979570864227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282988074824187986380576151 424482112236281979570864227)
        ·
          refine ⟨636723168354422969356296341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424482112236281979570864227 636723168354422969356296341)
          ·
            refine ⟨29846398516613576688576391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 636723168354422969356296341 29846398516613576688576391)
            ·
              refine ⟨44769597774920365032864587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29846398516613576688576391 44769597774920365032864587)
              ·
                refine ⟨67154396662380547549296881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44769597774920365032864587 67154396662380547549296881)
                ·
                  refine ⟨50365797496785410661972661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67154396662380547549296881 50365797496785410661972661)
                  ·
                    refine ⟨4721793515323632249559937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50365797496785410661972661 4721793515323632249559937)
                    ·
                      refine ⟨3541345136492724187169953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721793515323632249559937 3541345136492724187169953)
                      ·
                        rfl

theorem cell23_6896745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5, 2].length) (baseStart_6896745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896745 prefixEnd_6896745 := by exact prefixLift 6896745
  have htrace : WordTrace (prefixWord ++ tailWord_6896745) baseStart_6896745 baseEnd_6896745 := by
    simpa [prefixWord, tailWord_6896745, baseEnd_6896745] using wordTrace_append hprefix tailTrace_6896745
  have hstable : (prefixWord ++ tailWord_6896745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896745).length < 2 ^ (prefixWord ++ tailWord_6896745).sum := by decide
  have hdescent : baseEnd_6896745 < baseStart_6896745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896748 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_6896748 : Nat := 118140960795 + 6896748 * 2 ^ 59
def prefixEnd_6896748 : Nat := 4983230072969 + 3 ^ 40 * 6896748 * 2
def baseEnd_6896748 : Nat := 3541346676934687675432439

theorem tailTrace_6896748 : CollatzResearch.WordTrace tailWord_6896748 prefixEnd_6896748 3541346676934687675432439 := by
  unfold tailWord_6896748
  simp only [CollatzResearch.WordTrace]
  refine ⟨125772532409133670814213449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167696709878844894418951265 125772532409133670814213449)
  ·
    refine ⟨94329399306850253110660087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125772532409133670814213449 94329399306850253110660087)
    ·
      refine ⟨141494098960275379665990131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94329399306850253110660087 141494098960275379665990131)
      ·
        refine ⟨212241148440413069498985197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141494098960275379665990131 212241148440413069498985197)
        ·
          refine ⟨79590430665154901062119449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212241148440413069498985197 79590430665154901062119449)
          ·
            refine ⟨59692822998866175796589587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79590430665154901062119449 59692822998866175796589587)
            ·
              refine ⟨89539234498299263694884381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59692822998866175796589587 89539234498299263694884381)
              ·
                refine ⟨33577212936862223885581643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89539234498299263694884381 33577212936862223885581643)
                ·
                  refine ⟨50365819405293335828372465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33577212936862223885581643 50365819405293335828372465)
                  ·
                    refine ⟨37774364553970001871279349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50365819405293335828372465 37774364553970001871279349)
                    ·
                      refine ⟨3541346676934687675432439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37774364553970001871279349 3541346676934687675432439)
                      ·
                        rfl

theorem cell23_6896748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_6896748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896748 prefixEnd_6896748 := by exact prefixLift 6896748
  have htrace : WordTrace (prefixWord ++ tailWord_6896748) baseStart_6896748 baseEnd_6896748 := by
    simpa [prefixWord, tailWord_6896748, baseEnd_6896748] using wordTrace_append hprefix tailTrace_6896748
  have hstable : (prefixWord ++ tailWord_6896748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896748).length < 2 ^ (prefixWord ++ tailWord_6896748).sum := by decide
  have hdescent : baseEnd_6896748 < baseStart_6896748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896772 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_6896772 : Nat := 118140960795 + 6896772 * 2 ^ 59
def prefixEnd_6896772 : Nat := 4983230072969 + 3 ^ 40 * 6896772 * 2
def baseEnd_6896772 : Nat := 1180453000156798527177443

theorem tailTrace_6896772 : CollatzResearch.WordTrace tailWord_6896772 prefixEnd_6896772 1180453000156798527177443 := by
  unfold tailWord_6896772
  simp only [CollatzResearch.WordTrace]
  refine ⟨125772970085090196863650285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167697293446786929151533713 125772970085090196863650285)
  ·
    refine ⟨47164863781908823823868857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125772970085090196863650285 47164863781908823823868857)
    ·
      refine ⟨35373647836431617867901643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47164863781908823823868857 35373647836431617867901643)
      ·
        refine ⟨53060471754647426801852465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35373647836431617867901643 53060471754647426801852465)
        ·
          refine ⟨39795353815985570101389349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53060471754647426801852465 39795353815985570101389349)
          ·
            refine ⟨7461628840497294394010503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39795353815985570101389349 7461628840497294394010503)
            ·
              refine ⟨11192443260745941591015755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461628840497294394010503 11192443260745941591015755)
              ·
                refine ⟨16788664891118912386523633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192443260745941591015755 16788664891118912386523633)
                ·
                  refine ⟨12591498668339184289892725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16788664891118912386523633 12591498668339184289892725)
                  ·
                    refine ⟨1180453000156798527177443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12591498668339184289892725 1180453000156798527177443)
                    ·
                      rfl

theorem cell23_6896772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_6896772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896772 prefixEnd_6896772 := by exact prefixLift 6896772
  have htrace : WordTrace (prefixWord ++ tailWord_6896772) baseStart_6896772 baseEnd_6896772 := by
    simpa [prefixWord, tailWord_6896772, baseEnd_6896772] using wordTrace_append hprefix tailTrace_6896772
  have hstable : (prefixWord ++ tailWord_6896772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896772).length < 2 ^ (prefixWord ++ tailWord_6896772).sum := by decide
  have hdescent : baseEnd_6896772 < baseStart_6896772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896775 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_6896775 : Nat := 118140960795 + 6896775 * 2 ^ 59
def prefixEnd_6896775 : Nat := 4983230072969 + 3 ^ 40 * 6896775 * 2
def baseEnd_6896775 : Nat := 3541360540912359069794815

theorem tailTrace_6896775 : CollatzResearch.WordTrace tailWord_6896775 prefixEnd_6896775 3541360540912359069794815 := by
  unfold tailWord_6896775
  simp only [CollatzResearch.WordTrace]
  refine ⟨251546049589169525239659779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167697366392779683493106519 251546049589169525239659779)
  ·
    refine ⟨377319074383754287859489669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251546049589169525239659779 377319074383754287859489669)
    ·
      refine ⟨70747326446953928973654313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377319074383754287859489669 70747326446953928973654313)
      ·
        refine ⟨53060494835215446730240735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70747326446953928973654313 53060494835215446730240735)
        ·
          refine ⟨79590742252823170095361103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53060494835215446730240735 79590742252823170095361103)
          ·
            refine ⟨119386113379234755143041655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79590742252823170095361103 119386113379234755143041655)
            ·
              refine ⟨179079170068852132714562483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119386113379234755143041655 179079170068852132714562483)
              ·
                refine ⟨268618755103278199071843725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179079170068852132714562483 268618755103278199071843725)
                ·
                  refine ⟨100732033163729324651941397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268618755103278199071843725 100732033163729324651941397)
                  ·
                    refine ⟨4721814054549812093059753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100732033163729324651941397 4721814054549812093059753)
                    ·
                      refine ⟨3541360540912359069794815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721814054549812093059753 3541360540912359069794815)
                      ·
                        rfl

theorem cell23_6896775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_6896775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896775 prefixEnd_6896775 := by exact prefixLift 6896775
  have htrace : WordTrace (prefixWord ++ tailWord_6896775) baseStart_6896775 baseEnd_6896775 := by
    simpa [prefixWord, tailWord_6896775, baseEnd_6896775] using wordTrace_append hprefix tailTrace_6896775
  have hstable : (prefixWord ++ tailWord_6896775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896775).length < 2 ^ (prefixWord ++ tailWord_6896775).sum := by decide
  have hdescent : baseEnd_6896775 < baseStart_6896775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896792 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_6896792 : Nat := 118140960795 + 6896792 * 2 ^ 59
def prefixEnd_6896792 : Nat := 4983230072969 + 3 ^ 40 * 6896792 * 2
def baseEnd_6896792 : Nat := 3541369270083485503282237

theorem tailTrace_6896792 : CollatzResearch.WordTrace tailWord_6896792 prefixEnd_6896792 3541369270083485503282237 := by
  unfold tailWord_6896792
  simp only [CollatzResearch.WordTrace]
  refine ⟨125773334815053968571514315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167697779753405291428685753 125773334815053968571514315)
  ·
    refine ⟨188660002222580952857271473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125773334815053968571514315 188660002222580952857271473)
    ·
      refine ⟨141495001666935714642953605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188660002222580952857271473 141495001666935714642953605)
      ·
        refine ⟨26530312812550446495553801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141495001666935714642953605 26530312812550446495553801)
        ·
          refine ⟨19897734609412834871665351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26530312812550446495553801 19897734609412834871665351)
          ·
            refine ⟨29846601914119252307498027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19897734609412834871665351 29846601914119252307498027)
            ·
              refine ⟨44769902871178878461247041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29846601914119252307498027 44769902871178878461247041)
              ·
                refine ⟨33577427153384158845935281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44769902871178878461247041 33577427153384158845935281)
                ·
                  refine ⟨25183070365038119134451461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33577427153384158845935281 25183070365038119134451461)
                  ·
                    refine ⟨4721825693444647337709649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25183070365038119134451461 4721825693444647337709649)
                    ·
                      refine ⟨3541369270083485503282237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721825693444647337709649 3541369270083485503282237)
                      ·
                        rfl

theorem cell23_6896792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_6896792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896792 prefixEnd_6896792 := by exact prefixLift 6896792
  have htrace : WordTrace (prefixWord ++ tailWord_6896792) baseStart_6896792 baseEnd_6896792 := by
    simpa [prefixWord, tailWord_6896792, baseEnd_6896792] using wordTrace_append hprefix tailTrace_6896792
  have hstable : (prefixWord ++ tailWord_6896792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896792).length < 2 ^ (prefixWord ++ tailWord_6896792).sum := by decide
  have hdescent : baseEnd_6896792 < baseStart_6896792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896879 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 1, 5]
def baseStart_6896879 : Nat := 118140960795 + 6896879 * 2 ^ 59
def prefixEnd_6896879 : Nat := 4983230072969 + 3 ^ 40 * 6896879 * 2
def baseEnd_6896879 : Nat := 1180471314300142220964779

theorem tailTrace_6896879 : CollatzResearch.WordTrace tailWord_6896879 prefixEnd_6896879 1180471314300142220964779 := by
  unfold tailWord_6896879
  simp only [CollatzResearch.WordTrace]
  refine ⟨251549842780792751001445691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167699895187195167334297127 251549842780792751001445691)
  ·
    refine ⟨377324764171189126502168537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251549842780792751001445691 377324764171189126502168537)
    ·
      refine ⟨282993573128391844876626403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377324764171189126502168537 282993573128391844876626403)
      ·
        refine ⟨424490359692587767314939605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282993573128391844876626403 424490359692587767314939605)
        ·
          refine ⟨9948992805295025796443897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 424490359692587767314939605 9948992805295025796443897)
          ·
            refine ⟨7461744603971269347332923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9948992805295025796443897 7461744603971269347332923)
            ·
              refine ⟨11192616905956904020999385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461744603971269347332923 11192616905956904020999385)
              ·
                refine ⟨8394462679467678015749539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11192616905956904020999385 8394462679467678015749539)
                ·
                  refine ⟨12591694019201517023624309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394462679467678015749539 12591694019201517023624309)
                  ·
                    refine ⟨1180471314300142220964779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12591694019201517023624309 1180471314300142220964779)
                    ·
                      rfl

theorem cell23_6896879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_6896879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896879 prefixEnd_6896879 := by exact prefixLift 6896879
  have htrace : WordTrace (prefixWord ++ tailWord_6896879) baseStart_6896879 baseEnd_6896879 := by
    simpa [prefixWord, tailWord_6896879, baseEnd_6896879] using wordTrace_append hprefix tailTrace_6896879
  have hstable : (prefixWord ++ tailWord_6896879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896879).length < 2 ^ (prefixWord ++ tailWord_6896879).sum := by decide
  have hdescent : baseEnd_6896879 < baseStart_6896879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896892 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_6896892 : Nat := 118140960795 + 6896892 * 2 ^ 59
def prefixEnd_6896892 : Nat := 4983230072969 + 3 ^ 40 * 6896892 * 2
def baseEnd_6896892 : Nat := 1180473539382978370677259

theorem tailTrace_6896892 : CollatzResearch.WordTrace tailWord_6896892 prefixEnd_6896892 1180473539382978370677259 := by
  unfold tailWord_6896892
  simp only [CollatzResearch.WordTrace]
  refine ⟨125775158464872827110834465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167700211286497102814445953 125775158464872827110834465)
  ·
    refine ⟨94331368848654620333125849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125775158464872827110834465 94331368848654620333125849)
    ·
      refine ⟨70748526636490965249844387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94331368848654620333125849 70748526636490965249844387)
      ·
        refine ⟨106122789954736447874766581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70748526636490965249844387 106122789954736447874766581)
        ·
          refine ⟨9949011558256541988259367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106122789954736447874766581 9949011558256541988259367)
          ·
            refine ⟨14923517337384812982389051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949011558256541988259367 14923517337384812982389051)
            ·
              refine ⟨22385276006077219473583577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14923517337384812982389051 22385276006077219473583577)
              ·
                refine ⟨16788957004557914605187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22385276006077219473583577 16788957004557914605187683)
                ·
                  refine ⟨25183435506836871907781525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16788957004557914605187683 25183435506836871907781525)
                  ·
                    refine ⟨1180473539382978370677259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25183435506836871907781525 1180473539382978370677259)
                    ·
                      rfl

theorem cell23_6896892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_6896892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896892 prefixEnd_6896892 := by exact prefixLift 6896892
  have htrace : WordTrace (prefixWord ++ tailWord_6896892) baseStart_6896892 baseEnd_6896892 := by
    simpa [prefixWord, tailWord_6896892, baseEnd_6896892] using wordTrace_append hprefix tailTrace_6896892
  have hstable : (prefixWord ++ tailWord_6896892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896892).length < 2 ^ (prefixWord ++ tailWord_6896892).sum := by decide
  have hdescent : baseEnd_6896892 < baseStart_6896892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896895 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_6896895 : Nat := 118140960795 + 6896895 * 2 ^ 59
def prefixEnd_6896895 : Nat := 4983230072969 + 3 ^ 40 * 6896895 * 2
def baseEnd_6896895 : Nat := 3541422158590898600294263

theorem tailTrace_6896895 : CollatzResearch.WordTrace tailWord_6896895 prefixEnd_6896895 3541422158590898600294263 := by
  unfold tailWord_6896895
  simp only [CollatzResearch.WordTrace]
  refine ⟨251550426348734785734028139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167700284232489857156018759 251550426348734785734028139)
  ·
    refine ⟨377325639523102178601042209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251550426348734785734028139 377325639523102178601042209)
    ·
      refine ⟨282994229642326633950781657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377325639523102178601042209 282994229642326633950781657)
      ·
        refine ⟨212245672231744975463086243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282994229642326633950781657 212245672231744975463086243)
        ·
          refine ⟨318368508347617463194629365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212245672231744975463086243 318368508347617463194629365)
          ·
            refine ⟨29847047657589137174496503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318368508347617463194629365 29847047657589137174496503)
            ·
              refine ⟨44770571486383705761744755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29847047657589137174496503 44770571486383705761744755)
              ·
                refine ⟨67155857229575558642617133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44770571486383705761744755 67155857229575558642617133)
                ·
                  refine ⟨25183446461090834490981425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67155857229575558642617133 25183446461090834490981425)
                  ·
                    refine ⟨18887584845818125868236069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25183446461090834490981425 18887584845818125868236069)
                    ·
                      refine ⟨3541422158590898600294263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18887584845818125868236069 3541422158590898600294263)
                      ·
                        rfl

theorem cell23_6896895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_6896895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896895 prefixEnd_6896895 := by exact prefixLift 6896895
  have htrace : WordTrace (prefixWord ++ tailWord_6896895) baseStart_6896895 baseEnd_6896895 := by
    simpa [prefixWord, tailWord_6896895, baseEnd_6896895] using wordTrace_append hprefix tailTrace_6896895
  have hstable : (prefixWord ++ tailWord_6896895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896895).length < 2 ^ (prefixWord ++ tailWord_6896895).sum := by decide
  have hdescent : baseEnd_6896895 < baseStart_6896895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896899 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 1, 1, 4]
def baseStart_6896899 : Nat := 118140960795 + 6896899 * 2 ^ 59
def prefixEnd_6896899 : Nat := 4983230072969 + 3 ^ 40 * 6896899 * 2
def baseEnd_6896899 : Nat := 3541424212513516584644245

theorem tailTrace_6896899 : CollatzResearch.WordTrace tailWord_6896899 prefixEnd_6896899 3541424212513516584644245 := by
  unfold tailWord_6896899
  simp only [CollatzResearch.WordTrace]
  refine ⟨251550572240720294417173751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167700381493813529611449167 251550572240720294417173751)
  ·
    refine ⟨377325858361080441625760627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251550572240720294417173751 377325858361080441625760627)
    ·
      refine ⟨565988787541620662438640941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377325858361080441625760627 565988787541620662438640941)
      ·
        refine ⟨212245795328107748414490353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565988787541620662438640941 212245795328107748414490353)
        ·
          refine ⟨159184346496080811310867765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212245795328107748414490353 159184346496080811310867765)
          ·
            refine ⟨14923532484007576060393853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159184346496080811310867765 14923532484007576060393853)
            ·
              refine ⟨5596324681502841022647695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14923532484007576060393853 5596324681502841022647695)
              ·
                refine ⟨8394487022254261533971543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596324681502841022647695 8394487022254261533971543)
                ·
                  refine ⟨12591730533381392300957315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394487022254261533971543 12591730533381392300957315)
                  ·
                    refine ⟨18887595800072088451435973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12591730533381392300957315 18887595800072088451435973)
                    ·
                      refine ⟨3541424212513516584644245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18887595800072088451435973 3541424212513516584644245)
                      ·
                        rfl

theorem cell23_6896899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_6896899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896899 prefixEnd_6896899 := by exact prefixLift 6896899
  have htrace : WordTrace (prefixWord ++ tailWord_6896899) baseStart_6896899 baseEnd_6896899 := by
    simpa [prefixWord, tailWord_6896899, baseEnd_6896899] using wordTrace_append hprefix tailTrace_6896899
  have hstable : (prefixWord ++ tailWord_6896899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896899).length < 2 ^ (prefixWord ++ tailWord_6896899).sum := by decide
  have hdescent : baseEnd_6896899 < baseStart_6896899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896922 : List Nat := [3, 1, 1, 3, 3, 3, 1, 8]
def baseStart_6896922 : Nat := 118140960795 + 6896922 * 2 ^ 59
def prefixEnd_6896922 : Nat := 4983230072969 + 3 ^ 40 * 6896922 * 2
def baseEnd_6896922 : Nat := 131164297132169259061357

theorem tailTrace_6896922 : CollatzResearch.WordTrace tailWord_6896922 prefixEnd_6896922 131164297132169259061357 := by
  unfold tailWord_6896922
  simp only [CollatzResearch.WordTrace]
  refine ⟨62887852779909242336315255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167700940746424646230174013 62887852779909242336315255)
  ·
    refine ⟨94331779169863863504472883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62887852779909242336315255 94331779169863863504472883)
    ·
      refine ⟨141497668754795795256709325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94331779169863863504472883 141497668754795795256709325)
      ·
        refine ⟨53061625783048423221265997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141497668754795795256709325 53061625783048423221265997)
        ·
          refine ⟨19898109668643158707974749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53061625783048423221265997 19898109668643158707974749)
          ·
            refine ⟨7461791125741184515490531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19898109668643158707974749 7461791125741184515490531)
            ·
              refine ⟨11192686688611776773235797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461791125741184515490531 11192686688611776773235797)
              ·
                refine ⟨131164297132169259061357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11192686688611776773235797 131164297132169259061357)
                ·
                  rfl

theorem cell23_6896922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_6896922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896922 prefixEnd_6896922 := by exact prefixLift 6896922
  have htrace : WordTrace (prefixWord ++ tailWord_6896922) baseStart_6896922 baseEnd_6896922 := by
    simpa [prefixWord, tailWord_6896922, baseEnd_6896922] using wordTrace_append hprefix tailTrace_6896922
  have hstable : (prefixWord ++ tailWord_6896922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896922).length < 2 ^ (prefixWord ++ tailWord_6896922).sum := by decide
  have hdescent : baseEnd_6896922 < baseStart_6896922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896926 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6896926 : Nat := 118140960795 + 6896926 * 2 ^ 59
def prefixEnd_6896926 : Nat := 4983230072969 + 3 ^ 40 * 6896926 * 2
def baseEnd_6896926 : Nat := 1180479358830395993002207

theorem tailTrace_6896926 : CollatzResearch.WordTrace tailWord_6896926 prefixEnd_6896926 1180479358830395993002207 := by
  unfold tailWord_6896926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31443944626452809753550829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167701038007748318685604421 31443944626452809753550829)
  ·
    refine ⟨11791479234919803657581561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31443944626452809753550829 11791479234919803657581561)
    ·
      refine ⟨8843609426189852743186171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11791479234919803657581561 8843609426189852743186171)
      ·
        refine ⟨13265414139284779114779257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8843609426189852743186171 13265414139284779114779257)
        ·
          refine ⟨9949060604463584336084443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13265414139284779114779257 9949060604463584336084443)
          ·
            refine ⟨14923590906695376504126665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949060604463584336084443 14923590906695376504126665)
            ·
              refine ⟨11192693180021532378094999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14923590906695376504126665 11192693180021532378094999)
              ·
                refine ⟨16789039770032298567142499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192693180021532378094999 16789039770032298567142499)
                ·
                  refine ⟨25183559655048447850713749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16789039770032298567142499 25183559655048447850713749)
                  ·
                    refine ⟨1180479358830395993002207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25183559655048447850713749 1180479358830395993002207)
                    ·
                      rfl

theorem cell23_6896926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6896926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896926 prefixEnd_6896926 := by exact prefixLift 6896926
  have htrace : WordTrace (prefixWord ++ tailWord_6896926) baseStart_6896926 baseEnd_6896926 := by
    simpa [prefixWord, tailWord_6896926, baseEnd_6896926] using wordTrace_append hprefix tailTrace_6896926
  have hstable : (prefixWord ++ tailWord_6896926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896926).length < 2 ^ (prefixWord ++ tailWord_6896926).sum := by decide
  have hdescent : baseEnd_6896926 < baseStart_6896926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896950 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6896950 : Nat := 118140960795 + 6896950 * 2 ^ 59
def prefixEnd_6896950 : Nat := 4983230072969 + 3 ^ 40 * 6896950 * 2
def baseEnd_6896950 : Nat := 3541450400026895885106511

theorem tailTrace_6896950 : CollatzResearch.WordTrace tailWord_6896950 prefixEnd_6896950 3541450400026895885106511 := by
  unfold tailWord_6896950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722027022720970632955019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167701621575690353418186869 15722027022720970632955019)
  ·
    refine ⟨23583040534081455949432529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15722027022720970632955019 23583040534081455949432529)
    ·
      refine ⟨17687280400561091962074397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23583040534081455949432529 17687280400561091962074397)
      ·
        refine ⟨6632730150210409485777899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17687280400561091962074397 6632730150210409485777899)
        ·
          refine ⟨9949095225315614228666849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632730150210409485777899 9949095225315614228666849)
          ·
            refine ⟨7461821418986710671500137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949095225315614228666849 7461821418986710671500137)
            ·
              refine ⟨5596366064240033003625103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7461821418986710671500137 5596366064240033003625103)
              ·
                refine ⟨8394549096360049505437655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596366064240033003625103 8394549096360049505437655)
                ·
                  refine ⟨12591823644540074258156483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394549096360049505437655 12591823644540074258156483)
                  ·
                    refine ⟨18887735466810111387234725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12591823644540074258156483 18887735466810111387234725)
                    ·
                      refine ⟨3541450400026895885106511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18887735466810111387234725 3541450400026895885106511)
                      ·
                        rfl

theorem cell23_6896950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6896950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896950 prefixEnd_6896950 := by exact prefixLift 6896950
  have htrace : WordTrace (prefixWord ++ tailWord_6896950) baseStart_6896950 baseEnd_6896950 := by
    simpa [prefixWord, tailWord_6896950, baseEnd_6896950] using wordTrace_append hprefix tailTrace_6896950
  have hstable : (prefixWord ++ tailWord_6896950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896950).length < 2 ^ (prefixWord ++ tailWord_6896950).sum := by decide
  have hdescent : baseEnd_6896950 < baseStart_6896950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6896953 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6896953 : Nat := 118140960795 + 6896953 * 2 ^ 59
def prefixEnd_6896953 : Nat := 4983230072969 + 3 ^ 40 * 6896953 * 2
def baseEnd_6896953 : Nat := 3541451940468859373368997

theorem tailTrace_6896953 : CollatzResearch.WordTrace tailWord_6896953 prefixEnd_6896953 3541451940468859373368997 := by
  unfold tailWord_6896953
  simp only [CollatzResearch.WordTrace]
  refine ⟨251552541782524661639639513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167701694521683107759759675 251552541782524661639639513)
  ·
    refine ⟨188664406336893496229729635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251552541782524661639639513 188664406336893496229729635)
    ·
      refine ⟨282996609505340244344594453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188664406336893496229729635 282996609505340244344594453)
      ·
        refine ⟨13265466070562823953652865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 282996609505340244344594453 13265466070562823953652865)
        ·
          refine ⟨9949099552922117965239649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13265466070562823953652865 9949099552922117965239649)
          ·
            refine ⟨7461824664691588473929737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949099552922117965239649 7461824664691588473929737)
            ·
              refine ⟨5596368498518691355447303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7461824664691588473929737 5596368498518691355447303)
              ·
                refine ⟨8394552747778037033170955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596368498518691355447303 8394552747778037033170955)
                ·
                  refine ⟨12591829121667055549756433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394552747778037033170955 12591829121667055549756433)
                  ·
                    refine ⟨9443871841250291662317325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12591829121667055549756433 9443871841250291662317325)
                    ·
                      refine ⟨3541451940468859373368997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9443871841250291662317325 3541451940468859373368997)
                      ·
                        rfl

theorem cell23_6896953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6896953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6896953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6896953 prefixEnd_6896953 := by exact prefixLift 6896953
  have htrace : WordTrace (prefixWord ++ tailWord_6896953) baseStart_6896953 baseEnd_6896953 := by
    simpa [prefixWord, tailWord_6896953, baseEnd_6896953] using wordTrace_append hprefix tailTrace_6896953
  have hstable : (prefixWord ++ tailWord_6896953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6896953).length < 2 ^ (prefixWord ++ tailWord_6896953).sum := by decide
  have hdescent : baseEnd_6896953 < baseStart_6896953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6896953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897065 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_6897065 : Nat := 118140960795 + 6897065 * 2 ^ 59
def prefixEnd_6897065 : Nat := 4983230072969 + 3 ^ 40 * 6897065 * 2
def baseEnd_6897065 : Nat := 3541509450302162935168481

theorem tailTrace_6897065 : CollatzResearch.WordTrace tailWord_6897065 prefixEnd_6897065 3541509450302162935168481 := by
  unfold tailWord_6897065
  simp only [CollatzResearch.WordTrace]
  refine ⟨251556626758118904767716649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167704417838745936511811099 251556626758118904767716649)
  ·
    refine ⟨188667470068589178575787487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251556626758118904767716649 188667470068589178575787487)
    ·
      refine ⟨283001205102883767863681231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188667470068589178575787487 283001205102883767863681231)
      ·
        refine ⟨424501807654325651795521847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283001205102883767863681231 424501807654325651795521847)
        ·
          refine ⟨636752711481488477693282771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424501807654325651795521847 636752711481488477693282771)
          ·
            refine ⟨955129067222232716539924157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636752711481488477693282771 955129067222232716539924157)
            ·
              refine ⟨358173400208337268702471559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 955129067222232716539924157 358173400208337268702471559)
              ·
                refine ⟨537260100312505903053707339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358173400208337268702471559 537260100312505903053707339)
                ·
                  refine ⟨805890150468758854580561009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537260100312505903053707339 805890150468758854580561009)
                  ·
                    refine ⟨604417612851569140935420757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 805890150468758854580561009 604417612851569140935420757)
                    ·
                      refine ⟨3541509450302162935168481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 604417612851569140935420757 3541509450302162935168481)
                      ·
                        rfl

theorem cell23_6897065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_6897065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897065 prefixEnd_6897065 := by exact prefixLift 6897065
  have htrace : WordTrace (prefixWord ++ tailWord_6897065) baseStart_6897065 baseEnd_6897065 := by
    simpa [prefixWord, tailWord_6897065, baseEnd_6897065] using wordTrace_append hprefix tailTrace_6897065
  have hstable : (prefixWord ++ tailWord_6897065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897065).length < 2 ^ (prefixWord ++ tailWord_6897065).sum := by decide
  have hdescent : baseEnd_6897065 < baseStart_6897065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897069 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6897069 : Nat := 118140960795 + 6897069 * 2 ^ 59
def prefixEnd_6897069 : Nat := 4983230072969 + 3 ^ 40 * 6897069 * 2
def baseEnd_6897069 : Nat := 3541511504224780919518463

theorem tailTrace_6897069 : CollatzResearch.WordTrace tailWord_6897069 prefixEnd_6897069 3541511504224780919518463 := by
  unfold tailWord_6897069
  simp only [CollatzResearch.WordTrace]
  refine ⟨251556772650104413450862261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167704515100069608967241507 251556772650104413450862261)
  ·
    refine ⟨23583447435947288761018337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251556772650104413450862261 23583447435947288761018337)
    ·
      refine ⟨17687585576960466570763753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23583447435947288761018337 17687585576960466570763753)
      ·
        refine ⟨13265689182720349928072815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17687585576960466570763753 13265689182720349928072815)
        ·
          refine ⟨19898533774080524892109223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13265689182720349928072815 19898533774080524892109223)
          ·
            refine ⟨29847800661120787338163835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19898533774080524892109223 29847800661120787338163835)
            ·
              refine ⟨44771700991681181007245753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29847800661120787338163835 44771700991681181007245753)
              ·
                refine ⟨33578775743760885755434315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44771700991681181007245753 33578775743760885755434315)
                ·
                  refine ⟨50368163615641328633151473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33578775743760885755434315 50368163615641328633151473)
                  ·
                    refine ⟨37776122711730996474863605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50368163615641328633151473 37776122711730996474863605)
                    ·
                      refine ⟨3541511504224780919518463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37776122711730996474863605 3541511504224780919518463)
                      ·
                        rfl

theorem cell23_6897069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6897069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897069 prefixEnd_6897069 := by exact prefixLift 6897069
  have htrace : WordTrace (prefixWord ++ tailWord_6897069) baseStart_6897069 baseEnd_6897069 := by
    simpa [prefixWord, tailWord_6897069, baseEnd_6897069] using wordTrace_append hprefix tailTrace_6897069
  have hstable : (prefixWord ++ tailWord_6897069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897069).length < 2 ^ (prefixWord ++ tailWord_6897069).sum := by decide
  have hdescent : baseEnd_6897069 < baseStart_6897069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897072 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_6897072 : Nat := 118140960795 + 6897072 * 2 ^ 59
def prefixEnd_6897072 : Nat := 4983230072969 + 3 ^ 40 * 6897072 * 2
def baseEnd_6897072 : Nat := 1180504348222248135926983

theorem tailTrace_6897072 : CollatzResearch.WordTrace tailWord_6897072 prefixEnd_6897072 1180504348222248135926983 := by
  unfold tailWord_6897072
  simp only [CollatzResearch.WordTrace]
  refine ⟨125778441034546772481610735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167704588046062363308814313 125778441034546772481610735)
  ·
    refine ⟨188667661551820158722416103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125778441034546772481610735 188667661551820158722416103)
    ·
      refine ⟨283001492327730238083624155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188667661551820158722416103 283001492327730238083624155)
      ·
        refine ⟨424502238491595357125436233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283001492327730238083624155 424502238491595357125436233)
        ·
          refine ⟨318376678868696517844077175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424502238491595357125436233 318376678868696517844077175)
          ·
            refine ⟨477565018303044776766115763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318376678868696517844077175 477565018303044776766115763)
            ·
              refine ⟨716347527454567165149173645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477565018303044776766115763 716347527454567165149173645)
              ·
                refine ⟨268630322795462686930940117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716347527454567165149173645 268630322795462686930940117)
                ·
                  refine ⟨6296023190518656724943909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268630322795462686930940117 6296023190518656724943909)
                  ·
                    refine ⟨1180504348222248135926983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296023190518656724943909 1180504348222248135926983)
                    ·
                      rfl

theorem cell23_6897072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_6897072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897072 prefixEnd_6897072 := by exact prefixLift 6897072
  have htrace : WordTrace (prefixWord ++ tailWord_6897072) baseStart_6897072 baseEnd_6897072 := by
    simpa [prefixWord, tailWord_6897072, baseEnd_6897072] using wordTrace_append hprefix tailTrace_6897072
  have hstable : (prefixWord ++ tailWord_6897072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897072).length < 2 ^ (prefixWord ++ tailWord_6897072).sum := by decide
  have hdescent : baseEnd_6897072 < baseStart_6897072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897079 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_6897079 : Nat := 118140960795 + 6897079 * 2 ^ 59
def prefixEnd_6897079 : Nat := 4983230072969 + 3 ^ 40 * 6897079 * 2
def baseEnd_6897079 : Nat := 3541516639031325880393417

theorem tailTrace_6897079 : CollatzResearch.WordTrace tailWord_6897079 prefixEnd_6897079 3541516639031325880393417 := by
  unfold tailWord_6897079
  simp only [CollatzResearch.WordTrace]
  refine ⟨251557137380068185158726291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167704758253378790105817527 251557137380068185158726291)
  ·
    refine ⟨377335706070102277738089437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251557137380068185158726291 377335706070102277738089437)
    ·
      refine ⟨141500889776288354151783539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377335706070102277738089437 141500889776288354151783539)
      ·
        refine ⟨212251334664432531227675309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141500889776288354151783539 212251334664432531227675309)
        ·
          refine ⟨79594250499162199210378241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212251334664432531227675309 79594250499162199210378241)
          ·
            refine ⟨59695687874371649407783681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79594250499162199210378241 59695687874371649407783681)
            ·
              refine ⟨44771765905778737055837761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59695687874371649407783681 44771765905778737055837761)
              ·
                refine ⟨33578824429334052791878321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44771765905778737055837761 33578824429334052791878321)
                ·
                  refine ⟨25184118322000539593908741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33578824429334052791878321 25184118322000539593908741)
                  ·
                    refine ⟨4722022185375101173857889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25184118322000539593908741 4722022185375101173857889)
                    ·
                      refine ⟨3541516639031325880393417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722022185375101173857889 3541516639031325880393417)
                      ·
                        rfl

theorem cell23_6897079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_6897079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897079 prefixEnd_6897079 := by exact prefixLift 6897079
  have htrace : WordTrace (prefixWord ++ tailWord_6897079) baseStart_6897079 baseEnd_6897079 := by
    simpa [prefixWord, tailWord_6897079, baseEnd_6897079] using wordTrace_append hprefix tailTrace_6897079
  have hstable : (prefixWord ++ tailWord_6897079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897079).length < 2 ^ (prefixWord ++ tailWord_6897079).sum := by decide
  have hdescent : baseEnd_6897079 < baseStart_6897079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897082 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_6897082 : Nat := 118140960795 + 6897082 * 2 ^ 59
def prefixEnd_6897082 : Nat := 4983230072969 + 3 ^ 40 * 6897082 * 2
def baseEnd_6897082 : Nat := 3541518179473289368655903

theorem tailTrace_6897082 : CollatzResearch.WordTrace tailWord_6897082 prefixEnd_6897082 3541518179473289368655903 := by
  unfold tailWord_6897082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62889311699764329167771375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167704831199371544447390333 62889311699764329167771375)
  ·
    refine ⟨94333967549646493751657063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62889311699764329167771375 94333967549646493751657063)
    ·
      refine ⟨141500951324469740627485595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94333967549646493751657063 141500951324469740627485595)
      ·
        refine ⟨212251426986704610941228393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141500951324469740627485595 212251426986704610941228393)
        ·
          refine ⟨159188570240028458205921295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212251426986704610941228393 159188570240028458205921295)
          ·
            refine ⟨238782855360042687308881943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159188570240028458205921295 238782855360042687308881943)
            ·
              refine ⟨358174283040064030963322915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238782855360042687308881943 358174283040064030963322915)
              ·
                refine ⟨537261424560096046444984373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358174283040064030963322915 537261424560096046444984373)
                ·
                  refine ⟨50368258552509004354217285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 537261424560096046444984373 50368258552509004354217285)
                  ·
                    refine ⟨9444048478595438316415741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50368258552509004354217285 9444048478595438316415741)
                    ·
                      refine ⟨3541518179473289368655903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444048478595438316415741 3541518179473289368655903)
                      ·
                        rfl

theorem cell23_6897082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_6897082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897082 prefixEnd_6897082 := by exact prefixLift 6897082
  have htrace : WordTrace (prefixWord ++ tailWord_6897082) baseStart_6897082 baseEnd_6897082 := by
    simpa [prefixWord, tailWord_6897082, baseEnd_6897082] using wordTrace_append hprefix tailTrace_6897082
  have hstable : (prefixWord ++ tailWord_6897082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897082).length < 2 ^ (prefixWord ++ tailWord_6897082).sum := by decide
  have hdescent : baseEnd_6897082 < baseStart_6897082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897123 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 1, 4]
def baseStart_6897123 : Nat := 118140960795 + 6897123 * 2 ^ 59
def prefixEnd_6897123 : Nat := 4983230072969 + 3 ^ 40 * 6897123 * 2
def baseEnd_6897123 : Nat := 1180513077393374569414405

theorem tailTrace_6897123 : CollatzResearch.WordTrace tailWord_6897123 prefixEnd_6897123 1180513077393374569414405 := by
  unfold tailWord_6897123
  simp only [CollatzResearch.WordTrace]
  refine ⟨251558742191908780673328023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167705828127939187115552015 251558742191908780673328023)
  ·
    refine ⟨377338113287863171009992035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251558742191908780673328023 377338113287863171009992035)
    ·
      refine ⟨566007169931794756514988053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377338113287863171009992035 566007169931794756514988053)
      ·
        refine ⟨26531586090552879211640065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 566007169931794756514988053 26531586090552879211640065)
        ·
          refine ⟨19898689567914659408730049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26531586090552879211640065 19898689567914659408730049)
          ·
            refine ⟨14924017175935994556547537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19898689567914659408730049 14924017175935994556547537)
            ·
              refine ⟨11193012881951995917410653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14924017175935994556547537 11193012881951995917410653)
              ·
                refine ⟨4197379830731998469028995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11193012881951995917410653 4197379830731998469028995)
                ·
                  refine ⟨6296069746097997703543493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197379830731998469028995 6296069746097997703543493)
                  ·
                    refine ⟨1180513077393374569414405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296069746097997703543493 1180513077393374569414405)
                    ·
                      rfl

theorem cell23_6897123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 4].length) (baseStart_6897123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897123 prefixEnd_6897123 := by exact prefixLift 6897123
  have htrace : WordTrace (prefixWord ++ tailWord_6897123) baseStart_6897123 baseEnd_6897123 := by
    simpa [prefixWord, tailWord_6897123, baseEnd_6897123] using wordTrace_append hprefix tailTrace_6897123
  have hstable : (prefixWord ++ tailWord_6897123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897123).length < 2 ^ (prefixWord ++ tailWord_6897123).sum := by decide
  have hdescent : baseEnd_6897123 < baseStart_6897123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897132 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_6897132 : Nat := 118140960795 + 6897132 * 2 ^ 59
def prefixEnd_6897132 : Nat := 4983230072969 + 3 ^ 40 * 6897132 * 2
def baseEnd_6897132 : Nat := 1180514617835338057676891

theorem tailTrace_6897132 : CollatzResearch.WordTrace tailWord_6897132 prefixEnd_6897132 1180514617835338057676891 := by
  unfold tailWord_6897132
  simp only [CollatzResearch.WordTrace]
  refine ⟨125779535224438087605202825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167706046965917450140270433 125779535224438087605202825)
  ·
    refine ⟨94334651418328565703902119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125779535224438087605202825 94334651418328565703902119)
    ·
      refine ⟨141501977127492848555853179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94334651418328565703902119 141501977127492848555853179)
      ·
        refine ⟨212252965691239272833779769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141501977127492848555853179 212252965691239272833779769)
        ·
          refine ⟨159189724268429454625334827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212252965691239272833779769 159189724268429454625334827)
          ·
            refine ⟨238784586402644181938002241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159189724268429454625334827 238784586402644181938002241)
            ·
              refine ⟨179088439801983136453501681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238784586402644181938002241 179088439801983136453501681)
              ·
                refine ⟨134316329851487352340126261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179088439801983136453501681 134316329851487352340126261)
                ·
                  refine ⟨12592155923576939281886837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134316329851487352340126261 12592155923576939281886837)
                  ·
                    refine ⟨1180514617835338057676891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12592155923576939281886837 1180514617835338057676891)
                    ·
                      rfl

theorem cell23_6897132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_6897132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897132 prefixEnd_6897132 := by exact prefixLift 6897132
  have htrace : WordTrace (prefixWord ++ tailWord_6897132) baseStart_6897132 baseEnd_6897132 := by
    simpa [prefixWord, tailWord_6897132, baseEnd_6897132] using wordTrace_append hprefix tailTrace_6897132
  have hstable : (prefixWord ++ tailWord_6897132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897132).length < 2 ^ (prefixWord ++ tailWord_6897132).sum := by decide
  have hdescent : baseEnd_6897132 < baseStart_6897132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897146 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_6897146 : Nat := 118140960795 + 6897146 * 2 ^ 59
def prefixEnd_6897146 : Nat := 4983230072969 + 3 ^ 40 * 6897146 * 2
def baseEnd_6897146 : Nat := 3541551042235177118255609

theorem tailTrace_6897146 : CollatzResearch.WordTrace tailWord_6897146 prefixEnd_6897146 3541551042235177118255609 := by
  unfold tailWord_6897146
  simp only [CollatzResearch.WordTrace]
  refine ⟨62889895267706363900353823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167706387380550303734276861 62889895267706363900353823)
  ·
    refine ⟨94334842901559545850530735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62889895267706363900353823 94334842901559545850530735)
    ·
      refine ⟨141502264352339318775796103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94334842901559545850530735 141502264352339318775796103)
      ·
        refine ⟨212253396528508978163694155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141502264352339318775796103 212253396528508978163694155)
        ·
          refine ⟨318380094792763467245541233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212253396528508978163694155 318380094792763467245541233)
          ·
            refine ⟨238785071094572600434155925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318380094792763467245541233 238785071094572600434155925)
            ·
              refine ⟨11193050207558090645351059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238785071094572600434155925 11193050207558090645351059)
              ·
                refine ⟨16789575311337135968026589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193050207558090645351059 16789575311337135968026589)
                ·
                  refine ⟨6296090741751425988009971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16789575311337135968026589 6296090741751425988009971)
                  ·
                    refine ⟨9444136112627138982014957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6296090741751425988009971 9444136112627138982014957)
                    ·
                      refine ⟨3541551042235177118255609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444136112627138982014957 3541551042235177118255609)
                      ·
                        rfl

theorem cell23_6897146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_6897146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897146 prefixEnd_6897146 := by exact prefixLift 6897146
  have htrace : WordTrace (prefixWord ++ tailWord_6897146) baseStart_6897146 baseEnd_6897146 := by
    simpa [prefixWord, tailWord_6897146, baseEnd_6897146] using wordTrace_append hprefix tailTrace_6897146
  have hstable : (prefixWord ++ tailWord_6897146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897146).length < 2 ^ (prefixWord ++ tailWord_6897146).sum := by decide
  have hdescent : baseEnd_6897146 < baseStart_6897146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897169 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_6897169 : Nat := 118140960795 + 6897169 * 2 ^ 59
def prefixEnd_6897169 : Nat := 4983230072969 + 3 ^ 40 * 6897169 * 2
def baseEnd_6897169 : Nat := 3541562852290230528268003

theorem tailTrace_6897169 : CollatzResearch.WordTrace tailWord_6897169 prefixEnd_6897169 3541562852290230528268003 := by
  unfold tailWord_6897169
  simp only [CollatzResearch.WordTrace]
  refine ⟨251560419949742130529502561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167706946633161420353001707 251560419949742130529502561)
  ·
    refine ⟨188670314962306597897126921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251560419949742130529502561 188670314962306597897126921)
    ·
      refine ⟨141502736221729948422845191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188670314962306597897126921 141502736221729948422845191)
      ·
        refine ⟨212254104332594922634267787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141502736221729948422845191 212254104332594922634267787)
        ·
          refine ⟨318381156498892383951401681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212254104332594922634267787 318381156498892383951401681)
          ·
            refine ⟨238785867374169287963551261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318381156498892383951401681 238785867374169287963551261)
            ·
              refine ⟨89544700265313482986331723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238785867374169287963551261 89544700265313482986331723)
              ·
                refine ⟨134317050397970224479497585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89544700265313482986331723 134317050397970224479497585)
                ·
                  refine ⟨100737787798477668359623189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134317050397970224479497585 100737787798477668359623189)
                  ·
                    refine ⟨4722083803053640704357337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100737787798477668359623189 4722083803053640704357337)
                    ·
                      refine ⟨3541562852290230528268003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722083803053640704357337 3541562852290230528268003)
                      ·
                        rfl

theorem cell23_6897169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_6897169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897169 prefixEnd_6897169 := by exact prefixLift 6897169
  have htrace : WordTrace (prefixWord ++ tailWord_6897169) baseStart_6897169 baseEnd_6897169 := by
    simpa [prefixWord, tailWord_6897169, baseEnd_6897169] using wordTrace_append hprefix tailTrace_6897169
  have hstable : (prefixWord ++ tailWord_6897169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897169).length < 2 ^ (prefixWord ++ tailWord_6897169).sum := by decide
  have hdescent : baseEnd_6897169 < baseStart_6897169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897186 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_6897186 : Nat := 118140960795 + 6897186 * 2 ^ 59
def prefixEnd_6897186 : Nat := 4983230072969 + 3 ^ 40 * 6897186 * 2
def baseEnd_6897186 : Nat := 3541571581461356961755425

theorem tailTrace_6897186 : CollatzResearch.WordTrace tailWord_6897186 prefixEnd_6897186 3541571581461356961755425 := by
  unfold tailWord_6897186
  simp only [CollatzResearch.WordTrace]
  refine ⟨62890259997670135608217853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167707359993787028288580941 62890259997670135608217853)
  ·
    refine ⟨23583847499126300853081695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62890259997670135608217853 23583847499126300853081695)
    ·
      refine ⟨35375771248689451279622543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23583847499126300853081695 35375771248689451279622543)
      ·
        refine ⟨53063656873034176919433815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35375771248689451279622543 53063656873034176919433815)
        ·
          refine ⟨79595485309551265379150723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53063656873034176919433815 79595485309551265379150723)
          ·
            refine ⟨119393227964326898068726085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79595485309551265379150723 119393227964326898068726085)
            ·
              refine ⟨22386230243311293387886141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119393227964326898068726085 22386230243311293387886141)
              ·
                refine ⟨8394836341241735020457303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22386230243311293387886141 8394836341241735020457303)
                ·
                  refine ⟨12592254511862602530685955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394836341241735020457303 12592254511862602530685955)
                  ·
                    refine ⟨18888381767793903796028933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12592254511862602530685955 18888381767793903796028933)
                    ·
                      refine ⟨3541571581461356961755425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18888381767793903796028933 3541571581461356961755425)
                      ·
                        rfl

theorem cell23_6897186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_6897186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897186 prefixEnd_6897186 := by exact prefixLift 6897186
  have htrace : WordTrace (prefixWord ++ tailWord_6897186) baseStart_6897186 baseEnd_6897186 := by
    simpa [prefixWord, tailWord_6897186, baseEnd_6897186] using wordTrace_append hprefix tailTrace_6897186
  have hstable : (prefixWord ++ tailWord_6897186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897186).length < 2 ^ (prefixWord ++ tailWord_6897186).sum := by decide
  have hdescent : baseEnd_6897186 < baseStart_6897186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897189 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_6897189 : Nat := 118140960795 + 6897189 * 2 ^ 59
def prefixEnd_6897189 : Nat := 4983230072969 + 3 ^ 40 * 6897189 * 2
def baseEnd_6897189 : Nat := 3541573121903320450017911

theorem tailTrace_6897189 : CollatzResearch.WordTrace tailWord_6897189 prefixEnd_6897189 3541573121903320450017911 := by
  unfold tailWord_6897189
  simp only [CollatzResearch.WordTrace]
  refine ⟨251561149409669673945230621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167707432939779782630153747 251561149409669673945230621)
  ·
    refine ⟨94335431028626127729461483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251561149409669673945230621 94335431028626127729461483)
    ·
      refine ⟨141503146542939191594192225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94335431028626127729461483 141503146542939191594192225)
      ·
        refine ⟨106127359907204393695644169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141503146542939191594192225 106127359907204393695644169)
        ·
          refine ⟨79595519930403295271733127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106127359907204393695644169 79595519930403295271733127)
          ·
            refine ⟨119393279895604942907599691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79595519930403295271733127 119393279895604942907599691)
            ·
              refine ⟨179089919843407414361399537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119393279895604942907599691 179089919843407414361399537)
              ·
                refine ⟨134317439882555560771049653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179089919843407414361399537 134317439882555560771049653)
                ·
                  refine ⟨12592259988989583822285905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134317439882555560771049653 12592259988989583822285905)
                  ·
                    refine ⟨9444194991742187866714429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12592259988989583822285905 9444194991742187866714429)
                    ·
                      refine ⟨3541573121903320450017911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444194991742187866714429 3541573121903320450017911)
                      ·
                        rfl

theorem cell23_6897189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_6897189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897189 prefixEnd_6897189 := by exact prefixLift 6897189
  have htrace : WordTrace (prefixWord ++ tailWord_6897189) baseStart_6897189 baseEnd_6897189 := by
    simpa [prefixWord, tailWord_6897189, baseEnd_6897189] using wordTrace_append hprefix tailTrace_6897189
  have hstable : (prefixWord ++ tailWord_6897189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897189).length < 2 ^ (prefixWord ++ tailWord_6897189).sum := by decide
  have hdescent : baseEnd_6897189 < baseStart_6897189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897203 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 3, 2, 2]
def baseStart_6897203 : Nat := 118140960795 + 6897203 * 2 ^ 59
def prefixEnd_6897203 : Nat := 4983230072969 + 3 ^ 40 * 6897203 * 2
def baseEnd_6897203 : Nat := 3541580310632483395242847

theorem tailTrace_6897203 : CollatzResearch.WordTrace tailWord_6897203 prefixEnd_6897203 3541580310632483395242847 := by
  unfold tailWord_6897203
  simp only [CollatzResearch.WordTrace]
  refine ⟨251561660031618954336240263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167707773354412636224160175 251561660031618954336240263)
  ·
    refine ⟨377342490047428431504360395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251561660031618954336240263 377342490047428431504360395)
    ·
      refine ⟨566013735071142647256540593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377342490047428431504360395 566013735071142647256540593)
      ·
        refine ⟨424510301303356985442405445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566013735071142647256540593 424510301303356985442405445)
        ·
          refine ⟨79595681494379434770451021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424510301303356985442405445 79595681494379434770451021)
          ·
            refine ⟨29848380560392288038919133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79595681494379434770451021 29848380560392288038919133)
            ·
              refine ⟨11193142710147108014594675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29848380560392288038919133 11193142710147108014594675)
              ·
                refine ⟨16789714065220662021892013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193142710147108014594675 16789714065220662021892013)
                ·
                  refine ⟨6296142774457748258209505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16789714065220662021892013 6296142774457748258209505)
                  ·
                    refine ⟨4722107080843311193657129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6296142774457748258209505 4722107080843311193657129)
                    ·
                      refine ⟨3541580310632483395242847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722107080843311193657129 3541580310632483395242847)
                      ·
                        rfl

theorem cell23_6897203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2, 2].length) (baseStart_6897203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897203 prefixEnd_6897203 := by exact prefixLift 6897203
  have htrace : WordTrace (prefixWord ++ tailWord_6897203) baseStart_6897203 baseEnd_6897203 := by
    simpa [prefixWord, tailWord_6897203, baseEnd_6897203] using wordTrace_append hprefix tailTrace_6897203
  have hstable : (prefixWord ++ tailWord_6897203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897203).length < 2 ^ (prefixWord ++ tailWord_6897203).sum := by decide
  have hdescent : baseEnd_6897203 < baseStart_6897203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897209 : List Nat := [1, 2, 1, 5, 1, 3, 2, 8]
def baseStart_6897209 : Nat := 118140960795 + 6897209 * 2 ^ 59
def prefixEnd_6897209 : Nat := 4983230072969 + 3 ^ 40 * 6897209 * 2
def baseEnd_6897209 : Nat := 131169755241348532287697

theorem tailTrace_6897209 : CollatzResearch.WordTrace tailWord_6897209 prefixEnd_6897209 131169755241348532287697 := by
  unfold tailWord_6897209
  simp only [CollatzResearch.WordTrace]
  refine ⟨251561878869597217360958681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167707919246398144907305787 251561878869597217360958681)
  ·
    refine ⟨188671409152197913020719011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251561878869597217360958681 188671409152197913020719011)
    ·
      refine ⟨283007113728296869531078517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188671409152197913020719011 283007113728296869531078517)
      ·
        refine ⟨26531916912027831518538611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283007113728296869531078517 26531916912027831518538611)
        ·
          refine ⟨39797875368041747277807917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26531916912027831518538611 39797875368041747277807917)
          ·
            refine ⟨14924203263015655229177969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39797875368041747277807917 14924203263015655229177969)
            ·
              refine ⟨11193152447261741421883477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14924203263015655229177969 11193152447261741421883477)
              ·
                refine ⟨131169755241348532287697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11193152447261741421883477 131169755241348532287697)
                ·
                  rfl

theorem cell23_6897209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 8].length) (baseStart_6897209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897209 prefixEnd_6897209 := by exact prefixLift 6897209
  have htrace : WordTrace (prefixWord ++ tailWord_6897209) baseStart_6897209 baseEnd_6897209 := by
    simpa [prefixWord, tailWord_6897209, baseEnd_6897209] using wordTrace_append hprefix tailTrace_6897209
  have hstable : (prefixWord ++ tailWord_6897209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897209).length < 2 ^ (prefixWord ++ tailWord_6897209).sum := by decide
  have hdescent : baseEnd_6897209 < baseStart_6897209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897213 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_6897213 : Nat := 118140960795 + 6897213 * 2 ^ 59
def prefixEnd_6897213 : Nat := 4983230072969 + 3 ^ 40 * 6897213 * 2
def baseEnd_6897213 : Nat := 1180528481813009452039267

theorem tailTrace_6897213 : CollatzResearch.WordTrace tailWord_6897213 prefixEnd_6897213 1180528481813009452039267 := by
  unfold tailWord_6897213
  simp only [CollatzResearch.WordTrace]
  refine ⟨251562024761582726044104293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167708016507721817362736195 251562024761582726044104293)
  ·
    refine ⟨47167879642796761133269555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251562024761582726044104293 47167879642796761133269555)
    ·
      refine ⟨70751819464195141699904333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47167879642796761133269555 70751819464195141699904333)
      ·
        refine ⟨26531932299073178137464125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70751819464195141699904333 26531932299073178137464125)
        ·
          refine ⟨9949474612152441801549047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26531932299073178137464125 9949474612152441801549047)
          ·
            refine ⟨14924211918228662702323571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949474612152441801549047 14924211918228662702323571)
            ·
              refine ⟨22386317877342994053485357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14924211918228662702323571 22386317877342994053485357)
              ·
                refine ⟨8394869204003622770057009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22386317877342994053485357 8394869204003622770057009)
                ·
                  refine ⟨6296151903002717077542757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8394869204003622770057009 6296151903002717077542757)
                  ·
                    refine ⟨1180528481813009452039267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296151903002717077542757 1180528481813009452039267)
                    ·
                      rfl

theorem cell23_6897213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_6897213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897213 prefixEnd_6897213 := by exact prefixLift 6897213
  have htrace : WordTrace (prefixWord ++ tailWord_6897213) baseStart_6897213 baseEnd_6897213 := by
    simpa [prefixWord, tailWord_6897213, baseEnd_6897213] using wordTrace_append hprefix tailTrace_6897213
  have hstable : (prefixWord ++ tailWord_6897213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897213).length < 2 ^ (prefixWord ++ tailWord_6897213).sum := by decide
  have hdescent : baseEnd_6897213 < baseStart_6897213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897236 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_6897236 : Nat := 118140960795 + 6897236 * 2 ^ 59
def prefixEnd_6897236 : Nat := 4983230072969 + 3 ^ 40 * 6897236 * 2
def baseEnd_6897236 : Nat := 3541597255494081766130195

theorem tailTrace_6897236 : CollatzResearch.WordTrace tailWord_6897236 prefixEnd_6897236 3541597255494081766130195 := by
  unfold tailWord_6897236
  simp only [CollatzResearch.WordTrace]
  refine ⟨125781431820249700486095781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167708575760332933981461041 125781431820249700486095781)
  ·
    refine ⟨23584018466296818841142959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125781431820249700486095781 23584018466296818841142959)
    ·
      refine ⟨35376027699445228261714439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23584018466296818841142959 35376027699445228261714439)
      ·
        refine ⟨53064041549167842392571659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35376027699445228261714439 53064041549167842392571659)
        ·
          refine ⟨79596062323751763588857489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53064041549167842392571659 79596062323751763588857489)
          ·
            refine ⟨59697046742813822691643117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79596062323751763588857489 59697046742813822691643117)
            ·
              refine ⟨22386392528555183509366169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59697046742813822691643117 22386392528555183509366169)
              ·
                refine ⟨16789794396416387632024627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22386392528555183509366169 16789794396416387632024627)
                ·
                  refine ⟨25184691594624581448036941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16789794396416387632024627 25184691594624581448036941)
                  ·
                    refine ⟨9444259347984218043013853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25184691594624581448036941 9444259347984218043013853)
                    ·
                      refine ⟨3541597255494081766130195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444259347984218043013853 3541597255494081766130195)
                      ·
                        rfl

theorem cell23_6897236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_6897236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897236 prefixEnd_6897236 := by exact prefixLift 6897236
  have htrace : WordTrace (prefixWord ++ tailWord_6897236) baseStart_6897236 baseEnd_6897236 := by
    simpa [prefixWord, tailWord_6897236, baseEnd_6897236] using wordTrace_append hprefix tailTrace_6897236
  have hstable : (prefixWord ++ tailWord_6897236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897236).length < 2 ^ (prefixWord ++ tailWord_6897236).sum := by decide
  have hdescent : baseEnd_6897236 < baseStart_6897236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897253 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_6897253 : Nat := 118140960795 + 6897253 * 2 ^ 59
def prefixEnd_6897253 : Nat := 4983230072969 + 3 ^ 40 * 6897253 * 2
def baseEnd_6897253 : Nat := 3541605984665208199617617

theorem tailTrace_6897253 : CollatzResearch.WordTrace tailWord_6897253 prefixEnd_6897253 3541605984665208199617617 := by
  unfold tailWord_6897253
  simp only [CollatzResearch.WordTrace]
  refine ⟨251563483681437812875560413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167708989120958541917040275 251563483681437812875560413)
  ·
    refine ⟨94336306380539179828335155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251563483681437812875560413 94336306380539179828335155)
    ·
      refine ⟨141504459570808769742502733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94336306380539179828335155 141504459570808769742502733)
      ·
        refine ⟨53064172339053288653438525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141504459570808769742502733 53064172339053288653438525)
        ·
          refine ⟨19899064627144983245039447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53064172339053288653438525 19899064627144983245039447)
          ·
            refine ⟨29848596940717474867559171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19899064627144983245039447 29848596940717474867559171)
            ·
              refine ⟨44772895411076212301338757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29848596940717474867559171 44772895411076212301338757)
              ·
                refine ⟨8394917889576789806501017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44772895411076212301338757 8394917889576789806501017)
                ·
                  refine ⟨6296188417182592354875763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8394917889576789806501017 6296188417182592354875763)
                  ·
                    refine ⟨9444282625773888532313645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6296188417182592354875763 9444282625773888532313645)
                    ·
                      refine ⟨3541605984665208199617617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444282625773888532313645 3541605984665208199617617)
                      ·
                        rfl

theorem cell23_6897253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_6897253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897253 prefixEnd_6897253 := by exact prefixLift 6897253
  have htrace : WordTrace (prefixWord ++ tailWord_6897253) baseStart_6897253 baseEnd_6897253 := by
    simpa [prefixWord, tailWord_6897253, baseEnd_6897253] using wordTrace_append hprefix tailTrace_6897253
  have hstable : (prefixWord ++ tailWord_6897253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897253).length < 2 ^ (prefixWord ++ tailWord_6897253).sum := by decide
  have hdescent : baseEnd_6897253 < baseStart_6897253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897270 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6897270 : Nat := 118140960795 + 6897270 * 2 ^ 59
def prefixEnd_6897270 : Nat := 4983230072969 + 3 ^ 40 * 6897270 * 2
def baseEnd_6897270 : Nat := 3541614713836334633105039

theorem tailTrace_6897270 : CollatzResearch.WordTrace tailWord_6897270 prefixEnd_6897270 3541614713836334633105039 := by
  unfold tailWord_6897270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722756482648514048683079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167709402481584149852619509 15722756482648514048683079)
  ·
    refine ⟨23584134723972771073024619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15722756482648514048683079 23584134723972771073024619)
    ·
      refine ⟨35376202085959156609536929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23584134723972771073024619 35376202085959156609536929)
      ·
        refine ⟨26532151564469367457152697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35376202085959156609536929 26532151564469367457152697)
        ·
          refine ⟨19899113673352025592864523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26532151564469367457152697 19899113673352025592864523)
          ·
            refine ⟨29848670510028038389296785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19899113673352025592864523 29848670510028038389296785)
            ·
              refine ⟨22386502882521028791972589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29848670510028038389296785 22386502882521028791972589)
              ·
                refine ⟨8394938580945385796989721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22386502882521028791972589 8394938580945385796989721)
                ·
                  refine ⟨6296203935709039347742291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8394938580945385796989721 6296203935709039347742291)
                  ·
                    refine ⟨9444305903563559021613437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6296203935709039347742291 9444305903563559021613437)
                    ·
                      refine ⟨3541614713836334633105039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444305903563559021613437 3541614713836334633105039)
                      ·
                        rfl

theorem cell23_6897270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6897270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897270 prefixEnd_6897270 := by exact prefixLift 6897270
  have htrace : WordTrace (prefixWord ++ tailWord_6897270) baseStart_6897270 baseEnd_6897270 := by
    simpa [prefixWord, tailWord_6897270, baseEnd_6897270] using wordTrace_append hprefix tailTrace_6897270
  have hstable : (prefixWord ++ tailWord_6897270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897270).length < 2 ^ (prefixWord ++ tailWord_6897270).sum := by decide
  have hdescent : baseEnd_6897270 < baseStart_6897270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897316 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 7]
def baseStart_6897316 : Nat := 118140960795 + 6897316 * 2 ^ 59
def prefixEnd_6897316 : Nat := 4983230072969 + 3 ^ 40 * 6897316 * 2
def baseEnd_6897316 : Nat := 393515370438493494792203

theorem tailTrace_6897316 : CollatzResearch.WordTrace tailWord_6897316 prefixEnd_6897316 393515370438493494792203 := by
  unfold tailWord_6897316
  simp only [CollatzResearch.WordTrace]
  refine ⟨125782890740104787317551901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167710520986806383090069201 125782890740104787317551901)
  ·
    refine ⟨47168584027539295244081963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125782890740104787317551901 47168584027539295244081963)
    ·
      refine ⟨70752876041308942866122945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47168584027539295244081963 70752876041308942866122945)
      ·
        refine ⟨53064657030981707149592209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70752876041308942866122945 53064657030981707149592209)
        ·
          refine ⟨39798492773236280362194157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53064657030981707149592209 39798492773236280362194157)
          ·
            refine ⟨14924434789963605135822809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39798492773236280362194157 14924434789963605135822809)
            ·
              refine ⟨11193326092472703851867107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14924434789963605135822809 11193326092472703851867107)
              ·
                refine ⟨16789989138709055777800661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193326092472703851867107 16789989138709055777800661)
                ·
                  refine ⟨393515370438493494792203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16789989138709055777800661 393515370438493494792203)
                  ·
                    rfl

theorem cell23_6897316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_6897316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897316 prefixEnd_6897316 := by exact prefixLift 6897316
  have htrace : WordTrace (prefixWord ++ tailWord_6897316) baseStart_6897316 baseEnd_6897316 := by
    simpa [prefixWord, tailWord_6897316, baseEnd_6897316] using wordTrace_append hprefix tailTrace_6897316
  have hstable : (prefixWord ++ tailWord_6897316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897316).length < 2 ^ (prefixWord ++ tailWord_6897316).sum := by decide
  have hdescent : baseEnd_6897316 < baseStart_6897316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897336 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_6897336 : Nat := 118140960795 + 6897336 * 2 ^ 59
def prefixEnd_6897336 : Nat := 4983230072969 + 3 ^ 40 * 6897336 * 2
def baseEnd_6897336 : Nat := 3541648603559531374879735

theorem tailTrace_6897336 : CollatzResearch.WordTrace tailWord_6897336 prefixEnd_6897336 3541648603559531374879735 := by
  unfold tailWord_6897336
  simp only [CollatzResearch.WordTrace]
  refine ⟨125783255470068559025415931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167711007293424745367221241 125783255470068559025415931)
  ·
    refine ⟨188674883205102838538123897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125783255470068559025415931 188674883205102838538123897)
    ·
      refine ⟨141506162403827128903592923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188674883205102838538123897 141506162403827128903592923)
      ·
        refine ⟨212259243605740693355389385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141506162403827128903592923 212259243605740693355389385)
        ·
          refine ⟨159194432704305520016542039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212259243605740693355389385 159194432704305520016542039)
          ·
            refine ⟨238791649056458280024813059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159194432704305520016542039 238791649056458280024813059)
            ·
              refine ⟨358187473584687420037219589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238791649056458280024813059 358187473584687420037219589)
              ·
                refine ⟨67160151297128891256978673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358187473584687420037219589 67160151297128891256978673)
                ·
                  refine ⟨50370113472846668442734005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67160151297128891256978673 50370113472846668442734005)
                  ·
                    refine ⟨4722198138079375166506313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50370113472846668442734005 4722198138079375166506313)
                    ·
                      refine ⟨3541648603559531374879735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722198138079375166506313 3541648603559531374879735)
                      ·
                        rfl

theorem cell23_6897336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_6897336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897336 prefixEnd_6897336 := by exact prefixLift 6897336
  have htrace : WordTrace (prefixWord ++ tailWord_6897336) baseStart_6897336 baseEnd_6897336 := by
    simpa [prefixWord, tailWord_6897336, baseEnd_6897336] using wordTrace_append hprefix tailTrace_6897336
  have hstable : (prefixWord ++ tailWord_6897336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897336).length < 2 ^ (prefixWord ++ tailWord_6897336).sum := by decide
  have hdescent : baseEnd_6897336 < baseStart_6897336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897386 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_6897386 : Nat := 118140960795 + 6897386 * 2 ^ 59
def prefixEnd_6897386 : Nat := 4983230072969 + 3 ^ 40 * 6897386 * 2
def baseEnd_6897386 : Nat := 3541674277592256179254505

theorem tailTrace_6897386 : CollatzResearch.WordTrace tailWord_6897386 prefixEnd_6897386 3541674277592256179254505 := by
  unfold tailWord_6897386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62892083647488994147538003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167712223059970651060101341 62892083647488994147538003)
  ·
    refine ⟨94338125471233491221307005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62892083647488994147538003 94338125471233491221307005)
    ·
      refine ⟨35376797051712559207990127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94338125471233491221307005 35376797051712559207990127)
      ·
        refine ⟨53065195577568838811985191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35376797051712559207990127 53065195577568838811985191)
        ·
          refine ⟨79597793366353258217977787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53065195577568838811985191 79597793366353258217977787)
          ·
            refine ⟨119396690049529887326966681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79597793366353258217977787 119396690049529887326966681)
            ·
              refine ⟨89547517537147415495225011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119396690049529887326966681 89547517537147415495225011)
              ·
                refine ⟨134321276305721123242837517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89547517537147415495225011 134321276305721123242837517)
                ·
                  refine ⟨50370478614645421216064069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134321276305721123242837517 50370478614645421216064069)
                  ·
                    refine ⟨9444464740246016478012013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50370478614645421216064069 9444464740246016478012013)
                    ·
                      refine ⟨3541674277592256179254505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444464740246016478012013 3541674277592256179254505)
                      ·
                        rfl

theorem cell23_6897386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_6897386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897386 prefixEnd_6897386 := by exact prefixLift 6897386
  have htrace : WordTrace (prefixWord ++ tailWord_6897386) baseStart_6897386 baseEnd_6897386 := by
    simpa [prefixWord, tailWord_6897386, baseEnd_6897386] using wordTrace_append hprefix tailTrace_6897386
  have hstable : (prefixWord ++ tailWord_6897386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897386).length < 2 ^ (prefixWord ++ tailWord_6897386).sum := by decide
  have hdescent : baseEnd_6897386 < baseStart_6897386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897436 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_6897436 : Nat := 118140960795 + 6897436 * 2 ^ 59
def prefixEnd_6897436 : Nat := 4983230072969 + 3 ^ 40 * 6897436 * 2
def baseEnd_6897436 : Nat := 1180566650541660327876425

theorem tailTrace_6897436 : CollatzResearch.WordTrace tailWord_6897436 prefixEnd_6897436 1180566650541660327876425 := by
  unfold tailWord_6897436
  simp only [CollatzResearch.WordTrace]
  refine ⟨125785079119887417564736081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167713438826516556752981441 125785079119887417564736081)
  ·
    refine ⟨94338809339915563173552061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125785079119887417564736081 94338809339915563173552061)
    ·
      refine ⟨35377053502468336190082023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94338809339915563173552061 35377053502468336190082023)
      ·
        refine ⟨53065580253702504285123035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35377053502468336190082023 53065580253702504285123035)
        ·
          refine ⟨79598370380553756427684553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53065580253702504285123035 79598370380553756427684553)
          ·
            refine ⟨59698777785415317320763415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79598370380553756427684553 59698777785415317320763415)
            ·
              refine ⟨89548166678122975981145123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59698777785415317320763415 89548166678122975981145123)
              ·
                refine ⟨134322250017184463971717685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89548166678122975981145123 134322250017184463971717685)
                ·
                  refine ⟨12592710939111043497348533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134322250017184463971717685 12592710939111043497348533)
                  ·
                    refine ⟨1180566650541660327876425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12592710939111043497348533 1180566650541660327876425)
                    ·
                      rfl

theorem cell23_6897436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_6897436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897436 prefixEnd_6897436 := by exact prefixLift 6897436
  have htrace : WordTrace (prefixWord ++ tailWord_6897436) baseStart_6897436 baseEnd_6897436 := by
    simpa [prefixWord, tailWord_6897436, baseEnd_6897436] using wordTrace_append hprefix tailTrace_6897436
  have hstable : (prefixWord ++ tailWord_6897436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897436).length < 2 ^ (prefixWord ++ tailWord_6897436).sum := by decide
  have hdescent : baseEnd_6897436 < baseStart_6897436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897443 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 4, 3, 2]
def baseStart_6897443 : Nat := 118140960795 + 6897443 * 2 ^ 59
def prefixEnd_6897443 : Nat := 4983230072969 + 3 ^ 40 * 6897443 * 2
def baseEnd_6897443 : Nat := 3541703545989562456241743

theorem tailTrace_6897443 : CollatzResearch.WordTrace tailWord_6897443 prefixEnd_6897443 3541703545989562456241743 := by
  unfold tailWord_6897443
  simp only [CollatzResearch.WordTrace]
  refine ⟨251570413550749475324976983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167713609033832983549984655 251570413550749475324976983)
  ·
    refine ⟨377355620326124212987465475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251570413550749475324976983 377355620326124212987465475)
    ·
      refine ⟨566033430489186319481198213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377355620326124212987465475 566033430489186319481198213)
      ·
        refine ⟨106131268216722434902724665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566033430489186319481198213 106131268216722434902724665)
        ·
          refine ⟨79598451162541826177043499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106131268216722434902724665 79598451162541826177043499)
          ·
            refine ⟨119397676743812739265565249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79598451162541826177043499 119397676743812739265565249)
            ·
              refine ⟨89548257557859554449173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119397676743812739265565249 89548257557859554449173937)
              ·
                refine ⟨67161193168394665836880453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89548257557859554449173937 67161193168394665836880453)
                ·
                  refine ⟨12592723719073999844415085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67161193168394665836880453 12592723719073999844415085)
                  ·
                    refine ⟨4722271394652749941655657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12592723719073999844415085 4722271394652749941655657)
                    ·
                      refine ⟨3541703545989562456241743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722271394652749941655657 3541703545989562456241743)
                      ·
                        rfl

theorem cell23_6897443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_6897443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897443 prefixEnd_6897443 := by exact prefixLift 6897443
  have htrace : WordTrace (prefixWord ++ tailWord_6897443) baseStart_6897443 baseEnd_6897443 := by
    simpa [prefixWord, tailWord_6897443, baseEnd_6897443] using wordTrace_append hprefix tailTrace_6897443
  have hstable : (prefixWord ++ tailWord_6897443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897443).length < 2 ^ (prefixWord ++ tailWord_6897443).sum := by decide
  have hdescent : baseEnd_6897443 < baseStart_6897443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897454 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6897454 : Nat := 118140960795 + 6897454 * 2 ^ 59
def prefixEnd_6897454 : Nat := 4983230072969 + 3 ^ 40 * 6897454 * 2
def baseEnd_6897454 : Nat := 3541709194276761913204193

theorem tailTrace_6897454 : CollatzResearch.WordTrace tailWord_6897454 prefixEnd_6897454 3541709194276761913204193 := by
  unfold tailWord_6897454
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446351844213703025453427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167713876502473082802418277 31446351844213703025453427)
  ·
    refine ⟨47169527766320554538180141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31446351844213703025453427 47169527766320554538180141)
    ·
      refine ⟨17688572912370207951817553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47169527766320554538180141 17688572912370207951817553)
      ·
        refine ⟨13266429684277655963863165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17688572912370207951817553 13266429684277655963863165)
        ·
          refine ⟨4974911131604120986448687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13266429684277655963863165 4974911131604120986448687)
          ·
            refine ⟨7462366697406181479673031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974911131604120986448687 7462366697406181479673031)
            ·
              refine ⟨11193550046109272219509547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462366697406181479673031 11193550046109272219509547)
              ·
                refine ⟨16790325069163908329264321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193550046109272219509547 16790325069163908329264321)
                ·
                  refine ⟨12592743801872931246948241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16790325069163908329264321 12592743801872931246948241)
                  ·
                    refine ⟨9444557851404698435211181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12592743801872931246948241 9444557851404698435211181)
                    ·
                      refine ⟨3541709194276761913204193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444557851404698435211181 3541709194276761913204193)
                      ·
                        rfl

theorem cell23_6897454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6897454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897454 prefixEnd_6897454 := by exact prefixLift 6897454
  have htrace : WordTrace (prefixWord ++ tailWord_6897454) baseStart_6897454 baseEnd_6897454 := by
    simpa [prefixWord, tailWord_6897454, baseEnd_6897454] using wordTrace_append hprefix tailTrace_6897454
  have hstable : (prefixWord ++ tailWord_6897454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897454).length < 2 ^ (prefixWord ++ tailWord_6897454).sum := by decide
  have hdescent : baseEnd_6897454 < baseStart_6897454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897470 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6897470 : Nat := 118140960795 + 6897470 * 2 ^ 59
def prefixEnd_6897470 : Nat := 4983230072969 + 3 ^ 40 * 6897470 * 2
def baseEnd_6897470 : Nat := 1180572469989077950201373

theorem tailTrace_6897470 : CollatzResearch.WordTrace tailWord_6897470 prefixEnd_6897470 1180572469989077950201373 := by
  unfold tailWord_6897470
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446424790206457367026233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167714265547767772624139909 31446424790206457367026233)
  ·
    refine ⟨23584818592654843025269675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31446424790206457367026233 23584818592654843025269675)
    ·
      refine ⟨35377227888982264537904513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23584818592654843025269675 35377227888982264537904513)
      ·
        refine ⟨26532920916736698403428385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35377227888982264537904513 26532920916736698403428385)
        ·
          refine ⟨19899690687552523802571289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26532920916736698403428385 19899690687552523802571289)
          ·
            refine ⟨14924768015664392851928467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19899690687552523802571289 14924768015664392851928467)
            ·
              refine ⟨22387152023496589277892701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14924768015664392851928467 22387152023496589277892701)
              ·
                refine ⟨8395182008811220979209763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22387152023496589277892701 8395182008811220979209763)
                ·
                  refine ⟨12592773013216831468814645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395182008811220979209763 12592773013216831468814645)
                  ·
                    refine ⟨1180572469989077950201373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12592773013216831468814645 1180572469989077950201373)
                    ·
                      rfl

theorem cell23_6897470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6897470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897470 prefixEnd_6897470 := by exact prefixLift 6897470
  have htrace : WordTrace (prefixWord ++ tailWord_6897470) baseStart_6897470 baseEnd_6897470 := by
    simpa [prefixWord, tailWord_6897470, baseEnd_6897470] using wordTrace_append hprefix tailTrace_6897470
  have hstable : (prefixWord ++ tailWord_6897470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897470).length < 2 ^ (prefixWord ++ tailWord_6897470).sum := by decide
  have hdescent : baseEnd_6897470 < baseStart_6897470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897486 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6897486 : Nat := 118140960795 + 6897486 * 2 ^ 59
def prefixEnd_6897486 : Nat := 4983230072969 + 3 ^ 40 * 6897486 * 2
def baseEnd_6897486 : Nat := 3541725625657705788004045

theorem tailTrace_6897486 : CollatzResearch.WordTrace tailWord_6897486 prefixEnd_6897486 3541725625657705788004045 := by
  unfold tailWord_6897486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446497736199211708599039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167714654593062462445861541 31446497736199211708599039)
  ·
    refine ⟨47169746604298817562898559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31446497736199211708599039 47169746604298817562898559)
    ·
      refine ⟨70754619906448226344347839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47169746604298817562898559 70754619906448226344347839)
      ·
        refine ⟨106131929859672339516521759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70754619906448226344347839 106131929859672339516521759)
        ·
          refine ⟨159197894789508509274782639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106131929859672339516521759 159197894789508509274782639)
          ·
            refine ⟨238796842184262763912173959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159197894789508509274782639 238796842184262763912173959)
            ·
              refine ⟨358195263276394145868260939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238796842184262763912173959 358195263276394145868260939)
              ·
                refine ⟨537292894914591218802391409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358195263276394145868260939 537292894914591218802391409)
                ·
                  refine ⟨402969671185943414101793557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537292894914591218802391409 402969671185943414101793557)
                  ·
                    refine ⟨18889203336841097536021573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 402969671185943414101793557 18889203336841097536021573)
                    ·
                      refine ⟨3541725625657705788004045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18889203336841097536021573 3541725625657705788004045)
                      ·
                        rfl

theorem cell23_6897486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6897486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897486 prefixEnd_6897486 := by exact prefixLift 6897486
  have htrace : WordTrace (prefixWord ++ tailWord_6897486) baseStart_6897486 baseEnd_6897486 := by
    simpa [prefixWord, tailWord_6897486, baseEnd_6897486] using wordTrace_append hprefix tailTrace_6897486
  have hstable : (prefixWord ++ tailWord_6897486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897486).length < 2 ^ (prefixWord ++ tailWord_6897486).sum := by decide
  have hdescent : baseEnd_6897486 < baseStart_6897486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897493 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6897493 : Nat := 118140960795 + 6897493 * 2 ^ 59
def prefixEnd_6897493 : Nat := 4983230072969 + 3 ^ 40 * 6897493 * 2
def baseEnd_6897493 : Nat := 3541729220022287260616513

theorem tailTrace_6897493 : CollatzResearch.WordTrace tailWord_6897493 prefixEnd_6897493 3541729220022287260616513 := by
  unfold tailWord_6897493
  simp only [CollatzResearch.WordTrace]
  refine ⟨251572237200568333864297133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167714824800378889242864755 251572237200568333864297133)
  ·
    refine ⟨94339588950213125199111425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251572237200568333864297133 94339588950213125199111425)
    ·
      refine ⟨70754691712659843899333569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94339588950213125199111425 70754691712659843899333569)
      ·
        refine ⟨53066018784494882924500177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70754691712659843899333569 53066018784494882924500177)
        ·
          refine ⟨39799514088371162193375133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53066018784494882924500177 39799514088371162193375133)
          ·
            refine ⟨14924817783139185822515675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39799514088371162193375133 14924817783139185822515675)
            ·
              refine ⟨22387226674708778733773513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14924817783139185822515675 22387226674708778733773513)
              ·
                refine ⟨16790420006031584050330135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22387226674708778733773513 16790420006031584050330135)
                ·
                  refine ⟨25185630009047376075495203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16790420006031584050330135 25185630009047376075495203)
                  ·
                    refine ⟨37778445013571064113242805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25185630009047376075495203 37778445013571064113242805)
                    ·
                      refine ⟨3541729220022287260616513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37778445013571064113242805 3541729220022287260616513)
                      ·
                        rfl

theorem cell23_6897493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6897493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897493 prefixEnd_6897493 := by exact prefixLift 6897493
  have htrace : WordTrace (prefixWord ++ tailWord_6897493) baseStart_6897493 baseEnd_6897493 := by
    simpa [prefixWord, tailWord_6897493, baseEnd_6897493] using wordTrace_append hprefix tailTrace_6897493
  have hstable : (prefixWord ++ tailWord_6897493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897493).length < 2 ^ (prefixWord ++ tailWord_6897493).sum := by decide
  have hdescent : baseEnd_6897493 < baseStart_6897493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897503 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_6897503 : Nat := 118140960795 + 6897503 * 2 ^ 59
def prefixEnd_6897503 : Nat := 4983230072969 + 3 ^ 40 * 6897503 * 2
def baseEnd_6897503 : Nat := 3541734354828832221491467

theorem tailTrace_6897503 : CollatzResearch.WordTrace tailWord_6897503 prefixEnd_6897503 3541734354828832221491467 := by
  unfold tailWord_6897503
  simp only [CollatzResearch.WordTrace]
  refine ⟨251572601930532105572161163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167715067953688070381440775 251572601930532105572161163)
  ·
    refine ⟨377358902895798158358241745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251572601930532105572161163 377358902895798158358241745)
    ·
      refine ⟨283019177171848618768681309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377358902895798158358241745 283019177171848618768681309)
      ·
        refine ⟨106132191439443232038255491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283019177171848618768681309 106132191439443232038255491)
        ·
          refine ⟨159198287159164848057383237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106132191439443232038255491 159198287159164848057383237)
          ·
            refine ⟨29849678842343409010759357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159198287159164848057383237 29849678842343409010759357)
            ·
              refine ⟨11193629565878778379034759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29849678842343409010759357 11193629565878778379034759)
              ·
                refine ⟨16790444348818167568552139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193629565878778379034759 16790444348818167568552139)
                ·
                  refine ⟨25185666523227251352828209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16790444348818167568552139 25185666523227251352828209)
                  ·
                    refine ⟨18889249892420438514621157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25185666523227251352828209 18889249892420438514621157)
                    ·
                      refine ⟨3541734354828832221491467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18889249892420438514621157 3541734354828832221491467)
                      ·
                        rfl

theorem cell23_6897503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_6897503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897503 prefixEnd_6897503 := by exact prefixLift 6897503
  have htrace : WordTrace (prefixWord ++ tailWord_6897503) baseStart_6897503 baseEnd_6897503 := by
    simpa [prefixWord, tailWord_6897503, baseEnd_6897503] using wordTrace_append hprefix tailTrace_6897503
  have hstable : (prefixWord ++ tailWord_6897503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897503).length < 2 ^ (prefixWord ++ tailWord_6897503).sum := by decide
  have hdescent : baseEnd_6897503 < baseStart_6897503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897536 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_6897536 : Nat := 118140960795 + 6897536 * 2 ^ 59
def prefixEnd_6897536 : Nat := 4983230072969 + 3 ^ 40 * 6897536 * 2
def baseEnd_6897536 : Nat := 3541751299690430592378815

theorem tailTrace_6897536 : CollatzResearch.WordTrace tailWord_6897536 prefixEnd_6897536 3541751299690430592378815 := by
  unfold tailWord_6897536
  simp only [CollatzResearch.WordTrace]
  refine ⟨125786902769706276104056231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167715870359608368138741641 125786902769706276104056231)
  ·
    refine ⟨188680354154559414156084347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125786902769706276104056231 188680354154559414156084347)
    ·
      refine ⟨283020531231839121234126521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188680354154559414156084347 283020531231839121234126521)
      ·
        refine ⟨212265398423879340925594891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283020531231839121234126521 212265398423879340925594891)
        ·
          refine ⟨318398097635819011388392337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212265398423879340925594891 318398097635819011388392337)
          ·
            refine ⟨238798573226864258541294253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318398097635819011388392337 238798573226864258541294253)
            ·
              refine ⟨89549464960074096952985345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238798573226864258541294253 89549464960074096952985345)
              ·
                refine ⟨67162098720055572714739009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89549464960074096952985345 67162098720055572714739009)
                ·
                  refine ⟨50371574040041679536054257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67162098720055572714739009 50371574040041679536054257)
                  ·
                    refine ⟨37778680530031259652040693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50371574040041679536054257 37778680530031259652040693)
                    ·
                      refine ⟨3541751299690430592378815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37778680530031259652040693 3541751299690430592378815)
                      ·
                        rfl

theorem cell23_6897536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_6897536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897536 prefixEnd_6897536 := by exact prefixLift 6897536
  have htrace : WordTrace (prefixWord ++ tailWord_6897536) baseStart_6897536 baseEnd_6897536 := by
    simpa [prefixWord, tailWord_6897536, baseEnd_6897536] using wordTrace_append hprefix tailTrace_6897536
  have hstable : (prefixWord ++ tailWord_6897536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897536).length < 2 ^ (prefixWord ++ tailWord_6897536).sum := by decide
  have hdescent : baseEnd_6897536 < baseStart_6897536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897540 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6897540 : Nat := 118140960795 + 6897540 * 2 ^ 59
def prefixEnd_6897540 : Nat := 4983230072969 + 3 ^ 40 * 6897540 * 2
def baseEnd_6897540 : Nat := 3541753353613048576728797

theorem tailTrace_6897540 : CollatzResearch.WordTrace tailWord_6897540 prefixEnd_6897540 3541753353613048576728797 := by
  unfold tailWord_6897540
  simp only [CollatzResearch.WordTrace]
  refine ⟨125786975715699030445629037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167715967620932040594172049 125786975715699030445629037)
  ·
    refine ⟨47170115893387136417110889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125786975715699030445629037 47170115893387136417110889)
    ·
      refine ⟨35377586920040352312833167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47170115893387136417110889 35377586920040352312833167)
      ·
        refine ⟨53066380380060528469249751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35377586920040352312833167 53066380380060528469249751)
        ·
          refine ⟨79599570570090792703874627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53066380380060528469249751 79599570570090792703874627)
          ·
            refine ⟨119399355855136189055811941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79599570570090792703874627 119399355855136189055811941)
            ·
              refine ⟨22387379222838035447964739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119399355855136189055811941 22387379222838035447964739)
              ·
                refine ⟨33581068834257053171947109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22387379222838035447964739 33581068834257053171947109)
                ·
                  refine ⟨6296450406423197469740083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33581068834257053171947109 6296450406423197469740083)
                  ·
                    refine ⟨9444675609634796204610125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6296450406423197469740083 9444675609634796204610125)
                    ·
                      refine ⟨3541753353613048576728797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444675609634796204610125 3541753353613048576728797)
                      ·
                        rfl

theorem cell23_6897540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6897540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897540 prefixEnd_6897540 := by exact prefixLift 6897540
  have htrace : WordTrace (prefixWord ++ tailWord_6897540) baseStart_6897540 baseEnd_6897540 := by
    simpa [prefixWord, tailWord_6897540, baseEnd_6897540] using wordTrace_append hprefix tailTrace_6897540
  have hstable : (prefixWord ++ tailWord_6897540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897540).length < 2 ^ (prefixWord ++ tailWord_6897540).sum := by decide
  have hdescent : baseEnd_6897540 < baseStart_6897540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897558 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6897558 : Nat := 118140960795 + 6897558 * 2 ^ 59
def prefixEnd_6897558 : Nat := 4983230072969 + 3 ^ 40 * 6897558 * 2
def baseEnd_6897558 : Nat := 3541762596264829506303715

theorem tailTrace_6897558 : CollatzResearch.WordTrace tailWord_6897558 prefixEnd_6897558 3541762596264829506303715 := by
  unfold tailWord_6897558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15723412996583303122838333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167716405296888566643608885 15723412996583303122838333)
  ·
    refine ⟨5896279873718738671064375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15723412996583303122838333 5896279873718738671064375)
    ·
      refine ⟨8844419810578108006596563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896279873718738671064375 8844419810578108006596563)
      ·
        refine ⟨13266629715867162009894845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844419810578108006596563 13266629715867162009894845)
        ·
          refine ⟨4974986143450185753710567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13266629715867162009894845 4974986143450185753710567)
          ·
            refine ⟨7462479215175278630565851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974986143450185753710567 7462479215175278630565851)
            ·
              refine ⟨11193718822762917945848777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462479215175278630565851 11193718822762917945848777)
              ·
                refine ⟨8395289117072188459386583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11193718822762917945848777 8395289117072188459386583)
                ·
                  refine ⟨12592933675608282689079875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395289117072188459386583 12592933675608282689079875)
                  ·
                    refine ⟨18889400513412424033619813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12592933675608282689079875 18889400513412424033619813)
                    ·
                      refine ⟨3541762596264829506303715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18889400513412424033619813 3541762596264829506303715)
                      ·
                        rfl

theorem cell23_6897558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6897558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897558 prefixEnd_6897558 := by exact prefixLift 6897558
  have htrace : WordTrace (prefixWord ++ tailWord_6897558) baseStart_6897558 baseEnd_6897558 := by
    simpa [prefixWord, tailWord_6897558, baseEnd_6897558] using wordTrace_append hprefix tailTrace_6897558
  have hstable : (prefixWord ++ tailWord_6897558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897558).length < 2 ^ (prefixWord ++ tailWord_6897558).sum := by decide
  have hdescent : baseEnd_6897558 < baseStart_6897558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897567 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 3, 3, 2]
def baseStart_6897567 : Nat := 118140960795 + 6897567 * 2 ^ 59
def prefixEnd_6897567 : Nat := 4983230072969 + 3 ^ 40 * 6897567 * 2
def baseEnd_6897567 : Nat := 3541767217590719971091173

theorem tailTrace_6897567 : CollatzResearch.WordTrace tailWord_6897567 prefixEnd_6897567 3541767217590719971091173 := by
  unfold tailWord_6897567
  simp only [CollatzResearch.WordTrace]
  refine ⟨251574936202300244502490955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167716624134866829668327303 251574936202300244502490955)
  ·
    refine ⟨377362404303450366753736433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251574936202300244502490955 377362404303450366753736433)
    ·
      refine ⟨283021803227587775065302325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377362404303450366753736433 283021803227587775065302325)
      ·
        refine ⟨26533294052586353912372093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283021803227587775065302325 26533294052586353912372093)
        ·
          refine ⟨9949985269719882717139535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26533294052586353912372093 9949985269719882717139535)
          ·
            refine ⟨14924977904579824075709303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949985269719882717139535 14924977904579824075709303)
            ·
              refine ⟨22387466856869736113563955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14924977904579824075709303 22387466856869736113563955)
              ·
                refine ⟨33581200285304604170345933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22387466856869736113563955 33581200285304604170345933)
                ·
                  refine ⟨12592950106989226563879725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33581200285304604170345933 12592950106989226563879725)
                  ·
                    refine ⟨4722356290120959961454897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12592950106989226563879725 4722356290120959961454897)
                    ·
                      refine ⟨3541767217590719971091173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722356290120959961454897 3541767217590719971091173)
                      ·
                        rfl

theorem cell23_6897567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_6897567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897567 prefixEnd_6897567 := by exact prefixLift 6897567
  have htrace : WordTrace (prefixWord ++ tailWord_6897567) baseStart_6897567 baseEnd_6897567 := by
    simpa [prefixWord, tailWord_6897567, baseEnd_6897567] using wordTrace_append hprefix tailTrace_6897567
  have hstable : (prefixWord ++ tailWord_6897567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897567).length < 2 ^ (prefixWord ++ tailWord_6897567).sum := by decide
  have hdescent : baseEnd_6897567 < baseStart_6897567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897593 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6897593 : Nat := 118140960795 + 6897593 * 2 ^ 59
def prefixEnd_6897593 : Nat := 4983230072969 + 3 ^ 40 * 6897593 * 2
def baseEnd_6897593 : Nat := 3541780568087736869366053

theorem tailTrace_6897593 : CollatzResearch.WordTrace tailWord_6897593 prefixEnd_6897593 3541780568087736869366053 := by
  unfold tailWord_6897593
  simp only [CollatzResearch.WordTrace]
  refine ⟨251575884500206050942937433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167717256333470700628624955 251575884500206050942937433)
  ·
    refine ⟨188681913375154538207203075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251575884500206050942937433 188681913375154538207203075)
    ·
      refine ⟨283022870062731807310804613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188681913375154538207203075 283022870062731807310804613)
      ·
        refine ⟨53066788136762213870775865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283022870062731807310804613 53066788136762213870775865)
        ·
          refine ⟨39800091102571660403081899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53066788136762213870775865 39800091102571660403081899)
          ·
            refine ⟨59700136653857490604622849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39800091102571660403081899 59700136653857490604622849)
            ·
              refine ⟨44775102490393117953467137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59700136653857490604622849 44775102490393117953467137)
              ·
                refine ⟨33581326867794838465100353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44775102490393117953467137 33581326867794838465100353)
                ·
                  refine ⟨25185995150846128848825265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33581326867794838465100353 25185995150846128848825265)
                  ·
                    refine ⟨18889496363134596636618949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25185995150846128848825265 18889496363134596636618949)
                    ·
                      refine ⟨3541780568087736869366053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18889496363134596636618949 3541780568087736869366053)
                      ·
                        rfl

theorem cell23_6897593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6897593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897593 prefixEnd_6897593 := by exact prefixLift 6897593
  have htrace : WordTrace (prefixWord ++ tailWord_6897593) baseStart_6897593 baseEnd_6897593 := by
    simpa [prefixWord, tailWord_6897593, baseEnd_6897593] using wordTrace_append hprefix tailTrace_6897593
  have hstable : (prefixWord ++ tailWord_6897593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897593).length < 2 ^ (prefixWord ++ tailWord_6897593).sum := by decide
  have hdescent : baseEnd_6897593 < baseStart_6897593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897690 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_6897690 : Nat := 118140960795 + 6897690 * 2 ^ 59
def prefixEnd_6897690 : Nat := 4983230072969 + 3 ^ 40 * 6897690 * 2
def baseEnd_6897690 : Nat := 3541830375711222989853107

theorem tailTrace_6897690 : CollatzResearch.WordTrace tailWord_6897690 prefixEnd_6897690 3541830375711222989853107 := by
  unfold tailWord_6897690
  simp only [CollatzResearch.WordTrace]
  refine ⟨62894855595213659127304631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167719614920569757672812349 62894855595213659127304631)
  ·
    refine ⟨94342283392820488690956947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62894855595213659127304631 94342283392820488690956947)
    ·
      refine ⟨141513425089230733036435421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94342283392820488690956947 141513425089230733036435421)
      ·
        refine ⟨53067534408461524888663283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141513425089230733036435421 53067534408461524888663283)
        ·
          refine ⟨79601301612692287332994925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53067534408461524888663283 79601301612692287332994925)
          ·
            refine ⟨29850488104759607749873097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79601301612692287332994925 29850488104759607749873097)
            ·
              refine ⟨22387866078569705812404823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29850488104759607749873097 22387866078569705812404823)
              ·
                refine ⟨33581799117854558718607235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22387866078569705812404823 33581799117854558718607235)
                ·
                  refine ⟨50372698676781838077910853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33581799117854558718607235 50372698676781838077910853)
                  ·
                    refine ⟨9444881001896594639608285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50372698676781838077910853 9444881001896594639608285)
                    ·
                      refine ⟨3541830375711222989853107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444881001896594639608285 3541830375711222989853107)
                      ·
                        rfl

theorem cell23_6897690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_6897690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897690 prefixEnd_6897690 := by exact prefixLift 6897690
  have htrace : WordTrace (prefixWord ++ tailWord_6897690) baseStart_6897690 baseEnd_6897690 := by
    simpa [prefixWord, tailWord_6897690, baseEnd_6897690] using wordTrace_append hprefix tailTrace_6897690
  have hstable : (prefixWord ++ tailWord_6897690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897690).length < 2 ^ (prefixWord ++ tailWord_6897690).sum := by decide
  have hdescent : baseEnd_6897690 < baseStart_6897690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897704 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6897704 : Nat := 118140960795 + 6897704 * 2 ^ 59
def prefixEnd_6897704 : Nat := 4983230072969 + 3 ^ 40 * 6897704 * 2
def baseEnd_6897704 : Nat := 3541837564440385935078043

theorem tailTrace_6897704 : CollatzResearch.WordTrace tailWord_6897704 prefixEnd_6897704 3541837564440385935078043 := by
  unfold tailWord_6897704
  simp only [CollatzResearch.WordTrace]
  refine ⟨125789966501401958450114083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167719955335202611266818777 125789966501401958450114083)
  ·
    refine ⟨188684949752102937675171125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125789966501401958450114083 188684949752102937675171125)
    ·
      refine ⟨17689214039259650407047293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188684949752102937675171125 17689214039259650407047293)
      ·
        refine ⟨6633455264722368902642735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17689214039259650407047293 6633455264722368902642735)
        ·
          refine ⟨9950182897083553353964103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633455264722368902642735 9950182897083553353964103)
          ·
            refine ⟨14925274345625330030946155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9950182897083553353964103 14925274345625330030946155)
            ·
              refine ⟨22387911518437995046419233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14925274345625330030946155 22387911518437995046419233)
              ·
                refine ⟨16790933638828496284814425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22387911518437995046419233 16790933638828496284814425)
                ·
                  refine ⟨12593200229121372213610819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16790933638828496284814425 12593200229121372213610819)
                  ·
                    refine ⟨18889800343682058320416229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12593200229121372213610819 18889800343682058320416229)
                    ·
                      refine ⟨3541837564440385935078043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18889800343682058320416229 3541837564440385935078043)
                      ·
                        rfl

theorem cell23_6897704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6897704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897704 prefixEnd_6897704 := by exact prefixLift 6897704
  have htrace : WordTrace (prefixWord ++ tailWord_6897704) baseStart_6897704 baseEnd_6897704 := by
    simpa [prefixWord, tailWord_6897704, baseEnd_6897704] using wordTrace_append hprefix tailTrace_6897704
  have hstable : (prefixWord ++ tailWord_6897704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897704).length < 2 ^ (prefixWord ++ tailWord_6897704).sum := by decide
  have hdescent : baseEnd_6897704 < baseStart_6897704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897710 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_6897710 : Nat := 118140960795 + 6897710 * 2 ^ 59
def prefixEnd_6897710 : Nat := 4983230072969 + 3 ^ 40 * 6897710 * 2
def baseEnd_6897710 : Nat := 393537849480479212400335

theorem tailTrace_6897710 : CollatzResearch.WordTrace tailWord_6897710 prefixEnd_6897710 393537849480479212400335 := by
  unfold tailWord_6897710
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447518980097772490618323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167720101227188119949964389 31447518980097772490618323)
  ·
    refine ⟨47171278470146658735927485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31447518980097772490618323 47171278470146658735927485)
    ·
      refine ⟨17689229426304997025972807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47171278470146658735927485 17689229426304997025972807)
      ·
        refine ⟨26533844139457495538959211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17689229426304997025972807 26533844139457495538959211)
        ·
          refine ⟨39800766209186243308438817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26533844139457495538959211 39800766209186243308438817)
          ·
            refine ⟨29850574656889682481329113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39800766209186243308438817 29850574656889682481329113)
            ·
              refine ⟨22387930992667261860996835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29850574656889682481329113 22387930992667261860996835)
              ·
                refine ⟨33581896489000892791495253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22387930992667261860996835 33581896489000892791495253)
                ·
                  refine ⟨393537849480479212400335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33581896489000892791495253 393537849480479212400335)
                  ·
                    rfl

theorem cell23_6897710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_6897710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897710 prefixEnd_6897710 := by exact prefixLift 6897710
  have htrace : WordTrace (prefixWord ++ tailWord_6897710) baseStart_6897710 baseEnd_6897710 := by
    simpa [prefixWord, tailWord_6897710, baseEnd_6897710] using wordTrace_append hprefix tailTrace_6897710
  have hstable : (prefixWord ++ tailWord_6897710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897710).length < 2 ^ (prefixWord ++ tailWord_6897710).sum := by decide
  have hdescent : baseEnd_6897710 < baseStart_6897710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897723 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 5, 5]
def baseStart_6897723 : Nat := 118140960795 + 6897723 * 2 ^ 59
def prefixEnd_6897723 : Nat := 4983230072969 + 3 ^ 40 * 6897723 * 2
def baseEnd_6897723 : Nat := 1180615773524273786913485

theorem tailTrace_6897723 : CollatzResearch.WordTrace tailWord_6897723 prefixEnd_6897723 1180615773524273786913485 := by
  unfold tailWord_6897723
  simp only [CollatzResearch.WordTrace]
  refine ⟨251580625989735083145169823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167720417326490055430113215 251580625989735083145169823)
  ·
    refine ⟨377370938984602624717754735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251580625989735083145169823 377370938984602624717754735)
    ·
      refine ⟨566056408476903937076632103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377370938984602624717754735 566056408476903937076632103)
      ·
        refine ⟨849084612715355905614948155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566056408476903937076632103 849084612715355905614948155)
        ·
          refine ⟨1273626919073033858422422233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849084612715355905614948155 1273626919073033858422422233)
          ·
            refine ⟨955220189304775393816816675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273626919073033858422422233 955220189304775393816816675)
            ·
              refine ⟨1432830283957163090725225013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955220189304775393816816675 1432830283957163090725225013)
              ·
                refine ⟨134327839120984039755489845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1432830283957163090725225013 134327839120984039755489845)
                ·
                  refine ⟨12593234917592253727077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134327839120984039755489845 12593234917592253727077173)
                  ·
                    refine ⟨1180615773524273786913485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12593234917592253727077173 1180615773524273786913485)
                    ·
                      rfl

theorem cell23_6897723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 5].length) (baseStart_6897723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897723 prefixEnd_6897723 := by exact prefixLift 6897723
  have htrace : WordTrace (prefixWord ++ tailWord_6897723) baseStart_6897723 baseEnd_6897723 := by
    simpa [prefixWord, tailWord_6897723, baseEnd_6897723] using wordTrace_append hprefix tailTrace_6897723
  have hstable : (prefixWord ++ tailWord_6897723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897723).length < 2 ^ (prefixWord ++ tailWord_6897723).sum := by decide
  have hdescent : baseEnd_6897723 < baseStart_6897723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897743 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_6897743 : Nat := 118140960795 + 6897743 * 2 ^ 59
def prefixEnd_6897743 : Nat := 4983230072969 + 3 ^ 40 * 6897743 * 2
def baseEnd_6897743 : Nat := 3541857590185911282490363

theorem tailTrace_6897743 : CollatzResearch.WordTrace tailWord_6897743 prefixEnd_6897743 3541857590185911282490363 := by
  unfold tailWord_6897743
  simp only [CollatzResearch.WordTrace]
  refine ⟨251581355449662626560897883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167720903633108417707265255 251581355449662626560897883)
  ·
    refine ⟨377372033174493939841346825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251581355449662626560897883 377372033174493939841346825)
    ·
      refine ⟨283029024880870454881010119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377372033174493939841346825 283029024880870454881010119)
      ·
        refine ⟨424543537321305682321515179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283029024880870454881010119 424543537321305682321515179)
        ·
          refine ⟨636815305981958523482272769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424543537321305682321515179 636815305981958523482272769)
          ·
            refine ⟨477611479486468892611704577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636815305981958523482272769 477611479486468892611704577)
            ·
              refine ⟨358208609614851669458778433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477611479486468892611704577 358208609614851669458778433)
              ·
                refine ⟨268656457211138752094083825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358208609614851669458778433 268656457211138752094083825)
                ·
                  refine ⟨201492342908354064070562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268656457211138752094083825 201492342908354064070562869)
                  ·
                    refine ⟨18889907147658193506615269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201492342908354064070562869 18889907147658193506615269)
                    ·
                      refine ⟨3541857590185911282490363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18889907147658193506615269 3541857590185911282490363)
                      ·
                        rfl

theorem cell23_6897743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_6897743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897743 prefixEnd_6897743 := by exact prefixLift 6897743
  have htrace : WordTrace (prefixWord ++ tailWord_6897743) baseStart_6897743 baseEnd_6897743 := by
    simpa [prefixWord, tailWord_6897743, baseEnd_6897743] using wordTrace_append hprefix tailTrace_6897743
  have hstable : (prefixWord ++ tailWord_6897743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897743).length < 2 ^ (prefixWord ++ tailWord_6897743).sum := by decide
  have hdescent : baseEnd_6897743 < baseStart_6897743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897754 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3]
def baseStart_6897754 : Nat := 118140960795 + 6897754 * 2 ^ 59
def prefixEnd_6897754 : Nat := 4983230072969 + 3 ^ 40 * 6897754 * 2
def baseEnd_6897754 : Nat := 3541863238473110739452813

theorem tailTrace_6897754 : CollatzResearch.WordTrace tailWord_6897754 prefixEnd_6897754 3541863238473110739452813 := by
  unfold tailWord_6897754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62895439163155693859887079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167721171101748516959698877 62895439163155693859887079)
  ·
    refine ⟨94343158744733540789830619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62895439163155693859887079 94343158744733540789830619)
    ·
      refine ⟨141514738117100311184745929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94343158744733540789830619 141514738117100311184745929)
      ·
        refine ⟨106136053587825233388559447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141514738117100311184745929 106136053587825233388559447)
        ·
          refine ⟨159204080381737850082839171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106136053587825233388559447 159204080381737850082839171)
          ·
            refine ⟨238806120572606775124258757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159204080381737850082839171 238806120572606775124258757)
            ·
              refine ⟨44776147607363770335798517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238806120572606775124258757 44776147607363770335798517)
              ·
                refine ⟨4197763838190353468981111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44776147607363770335798517 4197763838190353468981111)
                ·
                  refine ⟨6296645757285530203471667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197763838190353468981111 6296645757285530203471667)
                  ·
                    refine ⟨9444968635928295305207501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6296645757285530203471667 9444968635928295305207501)
                    ·
                      refine ⟨3541863238473110739452813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9444968635928295305207501 3541863238473110739452813)
                      ·
                        rfl

theorem cell23_6897754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_6897754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897754 prefixEnd_6897754 := by exact prefixLift 6897754
  have htrace : WordTrace (prefixWord ++ tailWord_6897754) baseStart_6897754 baseEnd_6897754 := by
    simpa [prefixWord, tailWord_6897754, baseEnd_6897754] using wordTrace_append hprefix tailTrace_6897754
  have hstable : (prefixWord ++ tailWord_6897754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897754).length < 2 ^ (prefixWord ++ tailWord_6897754).sum := by decide
  have hdescent : baseEnd_6897754 < baseStart_6897754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897797 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_6897797 : Nat := 118140960795 + 6897797 * 2 ^ 59
def prefixEnd_6897797 : Nat := 4983230072969 + 3 ^ 40 * 6897797 * 2
def baseEnd_6897797 : Nat := 3541885318141254071215115

theorem tailTrace_6897797 : CollatzResearch.WordTrace tailWord_6897797 prefixEnd_6897797 3541885318141254071215115 := by
  unfold tailWord_6897797
  simp only [CollatzResearch.WordTrace]
  refine ⟨251583324991466993783363645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167722216660977995855575763 251583324991466993783363645)
  ·
    refine ⟨94343746871800122668761367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251583324991466993783363645 94343746871800122668761367)
    ·
      refine ⟨141515620307700184003142051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94343746871800122668761367 141515620307700184003142051)
      ·
        refine ⟨212273430461550276004713077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141515620307700184003142051 212273430461550276004713077)
        ·
          refine ⟨19900634105770338375441851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212273430461550276004713077 19900634105770338375441851)
          ·
            refine ⟨29850951158655507563162777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19900634105770338375441851 29850951158655507563162777)
            ·
              refine ⟨22388213368991630672372083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29850951158655507563162777 22388213368991630672372083)
              ·
                refine ⟨33582320053487446008558125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22388213368991630672372083 33582320053487446008558125)
                ·
                  refine ⟨12593370020057792253209297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33582320053487446008558125 12593370020057792253209297)
                  ·
                    refine ⟨9445027515043344189906973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12593370020057792253209297 9445027515043344189906973)
                    ·
                      refine ⟨3541885318141254071215115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9445027515043344189906973 3541885318141254071215115)
                      ·
                        rfl

theorem cell23_6897797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_6897797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897797 prefixEnd_6897797 := by exact prefixLift 6897797
  have htrace : WordTrace (prefixWord ++ tailWord_6897797) baseStart_6897797 baseEnd_6897797 := by
    simpa [prefixWord, tailWord_6897797, baseEnd_6897797] using wordTrace_append hprefix tailTrace_6897797
  have hstable : (prefixWord ++ tailWord_6897797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897797).length < 2 ^ (prefixWord ++ tailWord_6897797).sum := by decide
  have hdescent : baseEnd_6897797 < baseStart_6897797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897838 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6897838 : Nat := 118140960795 + 6897838 * 2 ^ 59
def prefixEnd_6897838 : Nat := 4983230072969 + 3 ^ 40 * 6897838 * 2
def baseEnd_6897838 : Nat := 1180635456949362803600809

theorem tailTrace_6897838 : CollatzResearch.WordTrace tailWord_6897838 prefixEnd_6897838 1180635456949362803600809 := by
  unfold tailWord_6897838
  simp only [CollatzResearch.WordTrace]
  refine ⟨31448102548039807223200771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167723213589545638523737445 31448102548039807223200771)
  ·
    refine ⟨47172153822059710834801157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31448102548039807223200771 47172153822059710834801157)
    ·
      refine ⟨8844778841636195781525217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47172153822059710834801157 8844778841636195781525217)
      ·
        refine ⟨6633584131227146836143913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8844778841636195781525217 6633584131227146836143913)
        ·
          refine ⟨4975188098420360127107935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633584131227146836143913 4975188098420360127107935)
          ·
            refine ⟨7462782147630540190661903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975188098420360127107935 7462782147630540190661903)
            ·
              refine ⟨11194173221445810285992855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462782147630540190661903 11194173221445810285992855)
              ·
                refine ⟨16791259832168715428989283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11194173221445810285992855 16791259832168715428989283)
                ·
                  refine ⟨25186889748253073143483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16791259832168715428989283 25186889748253073143483925)
                  ·
                    refine ⟨1180635456949362803600809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25186889748253073143483925 1180635456949362803600809)
                    ·
                      rfl

theorem cell23_6897838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6897838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897838 prefixEnd_6897838 := by exact prefixLift 6897838
  have htrace : WordTrace (prefixWord ++ tailWord_6897838) baseStart_6897838 baseEnd_6897838 := by
    simpa [prefixWord, tailWord_6897838, baseEnd_6897838] using wordTrace_append hprefix tailTrace_6897838
  have hstable : (prefixWord ++ tailWord_6897838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897838).length < 2 ^ (prefixWord ++ tailWord_6897838).sum := by decide
  have hdescent : baseEnd_6897838 < baseStart_6897838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897841 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6897841 : Nat := 118140960795 + 6897841 * 2 ^ 59
def prefixEnd_6897841 : Nat := 4983230072969 + 3 ^ 40 * 6897841 * 2
def baseEnd_6897841 : Nat := 3541907911290051899064913

theorem tailTrace_6897841 : CollatzResearch.WordTrace tailWord_6897841 prefixEnd_6897841 3541907911290051899064913 := by
  unfold tailWord_6897841
  simp only [CollatzResearch.WordTrace]
  refine ⟨251584929803307589297965377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167723286535538392865310251 251584929803307589297965377)
  ·
    refine ⟨188688697352480691973474033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251584929803307589297965377 188688697352480691973474033)
    ·
      refine ⟨141516523014360518980105525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188688697352480691973474033 141516523014360518980105525)
      ·
        refine ⟨13267174032596298654384893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141516523014360518980105525 13267174032596298654384893)
        ·
          refine ⟨4975190262223611995394335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13267174032596298654384893 4975190262223611995394335)
          ·
            refine ⟨7462785393335417993091503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975190262223611995394335 7462785393335417993091503)
            ·
              refine ⟨11194178090003126989637255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462785393335417993091503 11194178090003126989637255)
              ·
                refine ⟨16791267135004690484455883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11194178090003126989637255 16791267135004690484455883)
                ·
                  refine ⟨25186900702507035726683825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16791267135004690484455883 25186900702507035726683825)
                  ·
                    refine ⟨18890175526880276795012869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25186900702507035726683825 18890175526880276795012869)
                    ·
                      refine ⟨3541907911290051899064913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18890175526880276795012869 3541907911290051899064913)
                      ·
                        rfl

theorem cell23_6897841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6897841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897841 prefixEnd_6897841 := by exact prefixLift 6897841
  have htrace : WordTrace (prefixWord ++ tailWord_6897841) baseStart_6897841 baseEnd_6897841 := by
    simpa [prefixWord, tailWord_6897841, baseEnd_6897841] using wordTrace_append hprefix tailTrace_6897841
  have hstable : (prefixWord ++ tailWord_6897841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897841).length < 2 ^ (prefixWord ++ tailWord_6897841).sum := by decide
  have hdescent : baseEnd_6897841 < baseStart_6897841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897850 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_6897850 : Nat := 118140960795 + 6897850 * 2 ^ 59
def prefixEnd_6897850 : Nat := 4983230072969 + 3 ^ 40 * 6897850 * 2
def baseEnd_6897850 : Nat := 3541912532615942363852371

theorem tailTrace_6897850 : CollatzResearch.WordTrace tailWord_6897850 prefixEnd_6897850 3541912532615942363852371 := by
  unfold tailWord_6897850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62896314515068745958760751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167723505373516655890028669 62896314515068745958760751)
  ·
    refine ⟨94344471772603118938141127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62896314515068745958760751 94344471772603118938141127)
    ·
      refine ⟨141516707658904678407211691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94344471772603118938141127 141516707658904678407211691)
      ·
        refine ⟨212275061488357017610817537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141516707658904678407211691 212275061488357017610817537)
        ·
          refine ⟨159206296116267763208113153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212275061488357017610817537 159206296116267763208113153)
          ·
            refine ⟨119404722087200822406084865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159206296116267763208113153 119404722087200822406084865)
            ·
              refine ⟨89553541565400616804563649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119404722087200822406084865 89553541565400616804563649)
              ·
                refine ⟨67165156174050462603422737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89553541565400616804563649 67165156174050462603422737)
                ·
                  refine ⟨50373867130537846952567053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67165156174050462603422737 50373867130537846952567053)
                  ·
                    refine ⟨18890200173951692607212645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50373867130537846952567053 18890200173951692607212645)
                    ·
                      refine ⟨3541912532615942363852371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18890200173951692607212645 3541912532615942363852371)
                      ·
                        rfl

theorem cell23_6897850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_6897850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897850 prefixEnd_6897850 := by exact prefixLift 6897850
  have htrace : WordTrace (prefixWord ++ tailWord_6897850) baseStart_6897850 baseEnd_6897850 := by
    simpa [prefixWord, tailWord_6897850, baseEnd_6897850] using wordTrace_append hprefix tailTrace_6897850
  have hstable : (prefixWord ++ tailWord_6897850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897850).length < 2 ^ (prefixWord ++ tailWord_6897850).sum := by decide
  have hdescent : baseEnd_6897850 < baseStart_6897850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897867 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 3, 4, 2]
def baseStart_6897867 : Nat := 118140960795 + 6897867 * 2 ^ 59
def prefixEnd_6897867 : Nat := 4983230072969 + 3 ^ 40 * 6897867 * 2
def baseEnd_6897867 : Nat := 3541921261787068797339793

theorem tailTrace_6897867 : CollatzResearch.WordTrace tailWord_6897867 prefixEnd_6897867 3541921261787068797339793 := by
  unfold tailWord_6897867
  simp only [CollatzResearch.WordTrace]
  refine ⟨251585878101213395738411855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167723918734142263825607903 251585878101213395738411855)
  ·
    refine ⟨377378817151820093607617783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251585878101213395738411855 377378817151820093607617783)
    ·
      refine ⟨566068225727730140411426675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377378817151820093607617783 566068225727730140411426675)
      ·
        refine ⟨849102338591595210617140013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566068225727730140411426675 849102338591595210617140013)
        ·
          refine ⟨318413376971848203981427505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849102338591595210617140013 318413376971848203981427505)
          ·
            refine ⟨238810032728886152986070629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318413376971848203981427505 238810032728886152986070629)
            ·
              refine ⟨44776881136666153684888243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238810032728886152986070629 44776881136666153684888243)
              ·
                refine ⟨67165321704999230527332365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44776881136666153684888243 67165321704999230527332365)
                ·
                  refine ⟨25186995639374711447749637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67165321704999230527332365 25186995639374711447749637)
                  ·
                    refine ⟨4722561682382758396453057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25186995639374711447749637 4722561682382758396453057)
                    ·
                      refine ⟨3541921261787068797339793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722561682382758396453057 3541921261787068797339793)
                      ·
                        rfl

theorem cell23_6897867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4, 2].length) (baseStart_6897867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897867 prefixEnd_6897867 := by exact prefixLift 6897867
  have htrace : WordTrace (prefixWord ++ tailWord_6897867) baseStart_6897867 baseEnd_6897867 := by
    simpa [prefixWord, tailWord_6897867, baseEnd_6897867] using wordTrace_append hprefix tailTrace_6897867
  have hstable : (prefixWord ++ tailWord_6897867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897867).length < 2 ^ (prefixWord ++ tailWord_6897867).sum := by decide
  have hdescent : baseEnd_6897867 < baseStart_6897867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897920 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_6897920 : Nat := 118140960795 + 6897920 * 2 ^ 59
def prefixEnd_6897920 : Nat := 4983230072969 + 3 ^ 40 * 6897920 * 2
def baseEnd_6897920 : Nat := 1180649492087252363325683

theorem tailTrace_6897920 : CollatzResearch.WordTrace tailWord_6897920 prefixEnd_6897920 1180649492087252363325683 := by
  unfold tailWord_6897920
  simp only [CollatzResearch.WordTrace]
  refine ⟨125793905585010692895045607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167725207446680923860060809 125793905585010692895045607)
  ·
    refine ⟨188690858377516039342568411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125793905585010692895045607 188690858377516039342568411)
    ·
      refine ⟨283036287566274059013852617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188690858377516039342568411 283036287566274059013852617)
      ·
        refine ⟨212277215674705544260389463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283036287566274059013852617 212277215674705544260389463)
        ·
          refine ⟨318415823512058316390584195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212277215674705544260389463 318415823512058316390584195)
          ·
            refine ⟨477623735268087474585876293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318415823512058316390584195 477623735268087474585876293)
            ·
              refine ⟨89554450362766401484851805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 477623735268087474585876293 89554450362766401484851805)
              ·
                refine ⟨33582918886037400556819427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89554450362766401484851805 33582918886037400556819427)
                ·
                  refine ⟨50374378329056100835229141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33582918886037400556819427 50374378329056100835229141)
                  ·
                    refine ⟨1180649492087252363325683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50374378329056100835229141 1180649492087252363325683)
                    ·
                      rfl

theorem cell23_6897920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_6897920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897920 prefixEnd_6897920 := by exact prefixLift 6897920
  have htrace : WordTrace (prefixWord ++ tailWord_6897920) baseStart_6897920 baseEnd_6897920 := by
    simpa [prefixWord, tailWord_6897920, baseEnd_6897920] using wordTrace_append hprefix tailTrace_6897920
  have hstable : (prefixWord ++ tailWord_6897920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897920).length < 2 ^ (prefixWord ++ tailWord_6897920).sum := by decide
  have hdescent : baseEnd_6897920 < baseStart_6897920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897937 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_6897937 : Nat := 118140960795 + 6897937 * 2 ^ 59
def prefixEnd_6897937 : Nat := 4983230072969 + 3 ^ 40 * 6897937 * 2
def baseEnd_6897937 : Nat := 1180652401810961174488157

theorem tailTrace_6897937 : CollatzResearch.WordTrace tailWord_6897937 prefixEnd_6897937 1180652401810961174488157 := by
  unfold tailWord_6897937
  simp only [CollatzResearch.WordTrace]
  refine ⟨251588431210959797693460065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167725620807306531795640043 251588431210959797693460065)
  ·
    refine ⟨188691323408219848270095049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251588431210959797693460065 188691323408219848270095049)
    ·
      refine ⟨141518492556164886202571287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188691323408219848270095049 141518492556164886202571287)
      ·
        refine ⟨212277738834247329303856931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141518492556164886202571287 212277738834247329303856931)
        ·
          refine ⟨318416608251370993955785397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212277738834247329303856931 318416608251370993955785397)
          ·
            refine ⟨29851557023566030683354881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318416608251370993955785397 29851557023566030683354881)
            ·
              refine ⟨22388667767674523012516161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29851557023566030683354881 22388667767674523012516161)
              ·
                refine ⟨16791500825755892259387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22388667767674523012516161 16791500825755892259387121)
                ·
                  refine ⟨12593625619316919194540341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16791500825755892259387121 12593625619316919194540341)
                  ·
                    refine ⟨1180652401810961174488157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12593625619316919194540341 1180652401810961174488157)
                    ·
                      rfl

theorem cell23_6897937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_6897937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897937 prefixEnd_6897937 := by exact prefixLift 6897937
  have htrace : WordTrace (prefixWord ++ tailWord_6897937) baseStart_6897937 baseEnd_6897937 := by
    simpa [prefixWord, tailWord_6897937, baseEnd_6897937] using wordTrace_append hprefix tailTrace_6897937
  have hstable : (prefixWord ++ tailWord_6897937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897937).length < 2 ^ (prefixWord ++ tailWord_6897937).sum := by decide
  have hdescent : baseEnd_6897937 < baseStart_6897937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6897967 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 5, 4]
def baseStart_6897967 : Nat := 118140960795 + 6897967 * 2 ^ 59
def prefixEnd_6897967 : Nat := 4983230072969 + 3 ^ 40 * 6897967 * 2
def baseEnd_6897967 : Nat := 1180657536617506135363111

theorem tailTrace_6897967 : CollatzResearch.WordTrace tailWord_6897967 prefixEnd_6897967 1180657536617506135363111 := by
  unfold tailWord_6897967
  simp only [CollatzResearch.WordTrace]
  refine ⟨251589525400851112817052155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167726350267234075211368103 251589525400851112817052155)
  ·
    refine ⟨377384288101276669225578233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251589525400851112817052155 377384288101276669225578233)
    ·
      refine ⟨283038216075957501919183675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377384288101276669225578233 283038216075957501919183675)
      ·
        refine ⟨424557324113936252878775513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283038216075957501919183675 424557324113936252878775513)
        ·
          refine ⟨318417993085452189659081635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424557324113936252878775513 318417993085452189659081635)
          ·
            refine ⟨477626989628178284488622453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318417993085452189659081635 477626989628178284488622453)
            ·
              refine ⟨44777530277641714170808355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 477626989628178284488622453 44777530277641714170808355)
              ·
                refine ⟨67166295416462571256212533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44777530277641714170808355 67166295416462571256212533)
                ·
                  refine ⟨6296840195293366055269925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67166295416462571256212533 6296840195293366055269925)
                  ·
                    refine ⟨1180657536617506135363111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296840195293366055269925 1180657536617506135363111)
                    ·
                      rfl

theorem cell23_6897967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_6897967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6897967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6897967 prefixEnd_6897967 := by exact prefixLift 6897967
  have htrace : WordTrace (prefixWord ++ tailWord_6897967) baseStart_6897967 baseEnd_6897967 := by
    simpa [prefixWord, tailWord_6897967, baseEnd_6897967] using wordTrace_append hprefix tailTrace_6897967
  have hstable : (prefixWord ++ tailWord_6897967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6897967).length < 2 ^ (prefixWord ++ tailWord_6897967).sum := by decide
  have hdescent : baseEnd_6897967 < baseStart_6897967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6897967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898001 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 1, 4]
def baseStart_6898001 : Nat := 118140960795 + 6898001 * 2 ^ 59
def prefixEnd_6898001 : Nat := 4983230072969 + 3 ^ 40 * 6898001 * 2
def baseEnd_6898001 : Nat := 1180663356064923757688059

theorem tailTrace_6898001 : CollatzResearch.WordTrace tailWord_6898001 prefixEnd_6898001 1180663356064923757688059 := by
  unfold tailWord_6898001
  simp only [CollatzResearch.WordTrace]
  refine ⟨251590765482727936623789857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167727176988485291082526571 251590765482727936623789857)
  ·
    refine ⟨188693074112045952467842393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251590765482727936623789857 188693074112045952467842393)
    ·
      refine ⟨141519805584034464350881795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188693074112045952467842393 141519805584034464350881795)
      ·
        refine ⟨212279708376051696526322693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141519805584034464350881795 212279708376051696526322693)
        ·
          refine ⟨39802445320509693098685505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212279708376051696526322693 39802445320509693098685505)
          ·
            refine ⟨29851833990382269824014129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39802445320509693098685505 29851833990382269824014129)
            ·
              refine ⟨22388875492786702368010597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29851833990382269824014129 22388875492786702368010597)
              ·
                refine ⟨4197914154897506694001987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22388875492786702368010597 4197914154897506694001987)
                ·
                  refine ⟨6296871232346260041002981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197914154897506694001987 6296871232346260041002981)
                  ·
                    refine ⟨1180663356064923757688059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296871232346260041002981 1180663356064923757688059)
                    ·
                      rfl

theorem cell23_6898001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_6898001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898001 prefixEnd_6898001 := by exact prefixLift 6898001
  have htrace : WordTrace (prefixWord ++ tailWord_6898001) baseStart_6898001 baseEnd_6898001 := by
    simpa [prefixWord, tailWord_6898001, baseEnd_6898001] using wordTrace_append hprefix tailTrace_6898001
  have hstable : (prefixWord ++ tailWord_6898001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898001).length < 2 ^ (prefixWord ++ tailWord_6898001).sum := by decide
  have hdescent : baseEnd_6898001 < baseStart_6898001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898078 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6898078 : Nat := 118140960795 + 6898078 * 2 ^ 59
def prefixEnd_6898078 : Nat := 4983230072969 + 3 ^ 40 * 6898078 * 2
def baseEnd_6898078 : Nat := 1180676535401722490600441

theorem tailTrace_6898078 : CollatzResearch.WordTrace tailWord_6898078 prefixEnd_6898078 1180676535401722490600441 := by
  unfold tailWord_6898078
  simp only [CollatzResearch.WordTrace]
  refine ⟨31449196737931122346792861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167729049268965985849561925 31449196737931122346792861)
  ·
    refine ⟨11793448776724170880047323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31449196737931122346792861 11793448776724170880047323)
    ·
      refine ⟨17690173165086256320070985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11793448776724170880047323 17690173165086256320070985)
      ·
        refine ⟨13267629873814692240053239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17690173165086256320070985 13267629873814692240053239)
        ·
          refine ⟨19901444810722038360079859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13267629873814692240053239 19901444810722038360079859)
          ·
            refine ⟨29852167216083057540119789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19901444810722038360079859 29852167216083057540119789)
            ·
              refine ⟨11194562706031146577544921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29852167216083057540119789 11194562706031146577544921)
              ·
                refine ⟨8395922029523359933158691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11194562706031146577544921 8395922029523359933158691)
                ·
                  refine ⟨12593883044285039899738037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395922029523359933158691 12593883044285039899738037)
                  ·
                    refine ⟨1180676535401722490600441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12593883044285039899738037 1180676535401722490600441)
                    ·
                      rfl

theorem cell23_6898078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6898078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898078 prefixEnd_6898078 := by exact prefixLift 6898078
  have htrace : WordTrace (prefixWord ++ tailWord_6898078) baseStart_6898078 baseEnd_6898078 := by
    simpa [prefixWord, tailWord_6898078, baseEnd_6898078] using wordTrace_append hprefix tailTrace_6898078
  have hstable : (prefixWord ++ tailWord_6898078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898078).length < 2 ^ (prefixWord ++ tailWord_6898078).sum := by decide
  have hdescent : baseEnd_6898078 < baseStart_6898078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898108 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_6898108 : Nat := 118140960795 + 6898108 * 2 ^ 59
def prefixEnd_6898108 : Nat := 4983230072969 + 3 ^ 40 * 6898108 * 2
def baseEnd_6898108 : Nat := 1180681670208267451475395

theorem tailTrace_6898108 : CollatzResearch.WordTrace tailWord_6898108 prefixEnd_6898108 1180681670208267451475395 := by
  unfold tailWord_6898108
  simp only [CollatzResearch.WordTrace]
  refine ⟨125797334046670146948967489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167729778728893529265289985 125797334046670146948967489)
  ·
    refine ⟨94348000535002610211725617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125797334046670146948967489 94348000535002610211725617)
    ·
      refine ⟨70761000401251957658794213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94348000535002610211725617 70761000401251957658794213)
      ·
        refine ⟨13267687575234742061023915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70761000401251957658794213 13267687575234742061023915)
        ·
          refine ⟨19901531362852113091535873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13267687575234742061023915 19901531362852113091535873)
          ·
            refine ⟨14926148522139084818651905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19901531362852113091535873 14926148522139084818651905)
            ·
              refine ⟨11194611391604313613988929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14926148522139084818651905 11194611391604313613988929)
              ·
                refine ⟨8395958543703235210491697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11194611391604313613988929 8395958543703235210491697)
                ·
                  refine ⟨6296968907777426407868773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8395958543703235210491697 6296968907777426407868773)
                  ·
                    refine ⟨1180681670208267451475395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296968907777426407868773 1180681670208267451475395)
                    ·
                      rfl

theorem cell23_6898108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_6898108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898108 prefixEnd_6898108 := by exact prefixLift 6898108
  have htrace : WordTrace (prefixWord ++ tailWord_6898108) baseStart_6898108 baseEnd_6898108 := by
    simpa [prefixWord, tailWord_6898108, baseEnd_6898108] using wordTrace_append hprefix tailTrace_6898108
  have hstable : (prefixWord ++ tailWord_6898108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898108).length < 2 ^ (prefixWord ++ tailWord_6898108).sum := by decide
  have hdescent : baseEnd_6898108 < baseStart_6898108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898127 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_6898127 : Nat := 118140960795 + 6898127 * 2 ^ 59
def prefixEnd_6898127 : Nat := 4983230072969 + 3 ^ 40 * 6898127 * 2
def baseEnd_6898127 : Nat := 3542054766757237780088597

theorem tailTrace_6898127 : CollatzResearch.WordTrace tailWord_6898127 prefixEnd_6898127 3542054766757237780088597 := by
  unfold tailWord_6898127
  simp only [CollatzResearch.WordTrace]
  refine ⟨251595361080271460142876635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167730240720180973428584423 251595361080271460142876635)
  ·
    refine ⟨377393041620407190214314953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251595361080271460142876635 377393041620407190214314953)
    ·
      refine ⟨283044781215305392660736215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377393041620407190214314953 283044781215305392660736215)
      ·
        refine ⟨424567171822958088991104323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283044781215305392660736215 424567171822958088991104323)
        ·
          refine ⟨636850757734437133486656485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424567171822958088991104323 636850757734437133486656485)
          ·
            refine ⟨119409517075206962528748091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 636850757734437133486656485 119409517075206962528748091)
            ·
              refine ⟨179114275612810443793122137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119409517075206962528748091 179114275612810443793122137)
              ·
                refine ⟨134335706709607832844841603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179114275612810443793122137 134335706709607832844841603)
                ·
                  refine ⟨201503560064411749267262405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134335706709607832844841603 201503560064411749267262405)
                  ·
                    refine ⟨37781917512077202987611701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201503560064411749267262405 37781917512077202987611701)
                    ·
                      refine ⟨3542054766757237780088597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37781917512077202987611701 3542054766757237780088597)
                      ·
                        rfl

theorem cell23_6898127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_6898127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898127 prefixEnd_6898127 := by exact prefixLift 6898127
  have htrace : WordTrace (prefixWord ++ tailWord_6898127) baseStart_6898127 baseEnd_6898127 := by
    simpa [prefixWord, tailWord_6898127, baseEnd_6898127] using wordTrace_append hprefix tailTrace_6898127
  have hstable : (prefixWord ++ tailWord_6898127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898127).length < 2 ^ (prefixWord ++ tailWord_6898127).sum := by decide
  have hdescent : baseEnd_6898127 < baseStart_6898127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898165 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6898165 : Nat := 118140960795 + 6898165 * 2 ^ 59
def prefixEnd_6898165 : Nat := 4983230072969 + 3 ^ 40 * 6898165 * 2
def baseEnd_6898165 : Nat := 3542074279022108631413423

theorem tailTrace_6898165 : CollatzResearch.WordTrace tailWord_6898165 prefixEnd_6898165 3542074279022108631413423 := by
  unfold tailWord_6898165
  simp only [CollatzResearch.WordTrace]
  refine ⟨251596747054133792632759949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167731164702755861755173299 251596747054133792632759949)
  ·
    refine ⟨94348780145300172237284981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251596747054133792632759949 94348780145300172237284981)
    ·
      refine ⟨8845198138621891147245467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94348780145300172237284981 8845198138621891147245467)
      ·
        refine ⟨13267797207932836720868201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845198138621891147245467 13267797207932836720868201)
        ·
          refine ⟨9950847905949627540651151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13267797207932836720868201 9950847905949627540651151)
          ·
            refine ⟨14926271858924441310976727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9950847905949627540651151 14926271858924441310976727)
            ·
              refine ⟨22389407788386661966465091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14926271858924441310976727 22389407788386661966465091)
              ·
                refine ⟨33584111682579992949697637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22389407788386661966465091 33584111682579992949697637)
                ·
                  refine ⟨6297020940483748678068307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33584111682579992949697637 6297020940483748678068307)
                  ·
                    refine ⟨9445531410725623017102461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297020940483748678068307 9445531410725623017102461)
                    ·
                      refine ⟨3542074279022108631413423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9445531410725623017102461 3542074279022108631413423)
                      ·
                        rfl

theorem cell23_6898165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6898165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898165 prefixEnd_6898165 := by exact prefixLift 6898165
  have htrace : WordTrace (prefixWord ++ tailWord_6898165) baseStart_6898165 baseEnd_6898165 := by
    simpa [prefixWord, tailWord_6898165, baseEnd_6898165] using wordTrace_append hprefix tailTrace_6898165
  have hstable : (prefixWord ++ tailWord_6898165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898165).length < 2 ^ (prefixWord ++ tailWord_6898165).sum := by decide
  have hdescent : baseEnd_6898165 < baseStart_6898165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898182 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6898182 : Nat := 118140960795 + 6898182 * 2 ^ 59
def prefixEnd_6898182 : Nat := 4983230072969 + 3 ^ 40 * 6898182 * 2
def baseEnd_6898182 : Nat := 3542083008193235064900845

theorem tailTrace_6898182 : CollatzResearch.WordTrace tailWord_6898182 prefixEnd_6898182 3542083008193235064900845 := by
  unfold tailWord_6898182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862417721721006391754025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167731578063381469690752533 7862417721721006391754025)
  ·
    refine ⟨5896813291290754793815519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7862417721721006391754025 5896813291290754793815519)
    ·
      refine ⟨8845219936936132190723279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896813291290754793815519 8845219936936132190723279)
      ·
        refine ⟨13267829905404198286084919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845219936936132190723279 13267829905404198286084919)
        ·
          refine ⟨19901744858106297429127379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13267829905404198286084919 19901744858106297429127379)
          ·
            refine ⟨29852617287159446143691069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19901744858106297429127379 29852617287159446143691069)
            ·
              refine ⟨11194731482684792303884151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29852617287159446143691069 11194731482684792303884151)
              ·
                refine ⟨16792097224027188455826227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11194731482684792303884151 16792097224027188455826227)
                ·
                  refine ⟨25188145836040782683739341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16792097224027188455826227 25188145836040782683739341)
                  ·
                    refine ⟨9445554688515293506402253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25188145836040782683739341 9445554688515293506402253)
                    ·
                      refine ⟨3542083008193235064900845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9445554688515293506402253 3542083008193235064900845)
                      ·
                        rfl

theorem cell23_6898182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6898182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898182 prefixEnd_6898182 := by exact prefixLift 6898182
  have htrace : WordTrace (prefixWord ++ tailWord_6898182) baseStart_6898182 baseEnd_6898182 := by
    simpa [prefixWord, tailWord_6898182, baseEnd_6898182] using wordTrace_append hprefix tailTrace_6898182
  have hstable : (prefixWord ++ tailWord_6898182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898182).length < 2 ^ (prefixWord ++ tailWord_6898182).sum := by decide
  have hdescent : baseEnd_6898182 < baseStart_6898182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898188 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_6898188 : Nat := 118140960795 + 6898188 * 2 ^ 59
def prefixEnd_6898188 : Nat := 4983230072969 + 3 ^ 40 * 6898188 * 2
def baseEnd_6898188 : Nat := 3542086089077162041425817

theorem tailTrace_6898188 : CollatzResearch.WordTrace tailWord_6898188 prefixEnd_6898188 3542086089077162041425817 := by
  unfold tailWord_6898188
  simp only [CollatzResearch.WordTrace]
  refine ⟨125798792966525233780423609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167731723955366978373898145 125798792966525233780423609)
  ·
    refine ⟨94349094724893925335317707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125798792966525233780423609 94349094724893925335317707)
    ·
      refine ⟨141523642087340888002976561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94349094724893925335317707 141523642087340888002976561)
      ·
        refine ⟨106142731565505666002232421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141523642087340888002976561 106142731565505666002232421)
        ·
          refine ⟨19901762168532312375418579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106142731565505666002232421 19901762168532312375418579)
          ·
            refine ⟨29852643252798468563127869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19901762168532312375418579 29852643252798468563127869)
            ·
              refine ⟨11194741219799425711172951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29852643252798468563127869 11194741219799425711172951)
              ·
                refine ⟨16792111829699138566759427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11194741219799425711172951 16792111829699138566759427)
                ·
                  refine ⟨25188167744548707850139141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16792111829699138566759427 25188167744548707850139141)
                  ·
                    refine ⟨4722781452102882721901089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25188167744548707850139141 4722781452102882721901089)
                    ·
                      refine ⟨3542086089077162041425817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722781452102882721901089 3542086089077162041425817)
                      ·
                        rfl

theorem cell23_6898188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_6898188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898188 prefixEnd_6898188 := by exact prefixLift 6898188
  have htrace : WordTrace (prefixWord ++ tailWord_6898188) baseStart_6898188 baseEnd_6898188 := by
    simpa [prefixWord, tailWord_6898188, baseEnd_6898188] using wordTrace_append hprefix tailTrace_6898188
  have hstable : (prefixWord ++ tailWord_6898188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898188).length < 2 ^ (prefixWord ++ tailWord_6898188).sum := by decide
  have hdescent : baseEnd_6898188 < baseStart_6898188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898224 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_6898224 : Nat := 118140960795 + 6898224 * 2 ^ 59
def prefixEnd_6898224 : Nat := 4983230072969 + 3 ^ 40 * 6898224 * 2
def baseEnd_6898224 : Nat := 1180701524793574633525217

theorem tailTrace_6898224 : CollatzResearch.WordTrace tailWord_6898224 prefixEnd_6898224 1180701524793574633525217 := by
  unfold tailWord_6898224
  simp only [CollatzResearch.WordTrace]
  refine ⟨125799449480460022854578863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167732599307280030472771817 125799449480460022854578863)
  ·
    refine ⟨188699174220690034281868295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125799449480460022854578863 188699174220690034281868295)
    ·
      refine ⟨283048761331035051422802443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188699174220690034281868295 283048761331035051422802443)
      ·
        refine ⟨424573141996552577134203665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283048761331035051422802443 424573141996552577134203665)
        ·
          refine ⟨318429856497414432850652749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424573141996552577134203665 318429856497414432850652749)
          ·
            refine ⟨119411196186530412318994781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318429856497414432850652749 119411196186530412318994781)
            ·
              refine ⟨44779198569948904619623043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119411196186530412318994781 44779198569948904619623043)
              ·
                refine ⟨67168797854923356929434565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44779198569948904619623043 67168797854923356929434565)
                ·
                  refine ⟨12594149597798129424268981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67168797854923356929434565 12594149597798129424268981)
                  ·
                    refine ⟨1180701524793574633525217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12594149597798129424268981 1180701524793574633525217)
                    ·
                      rfl

theorem cell23_6898224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_6898224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898224 prefixEnd_6898224 := by exact prefixLift 6898224
  have htrace : WordTrace (prefixWord ++ tailWord_6898224) baseStart_6898224 baseEnd_6898224 := by
    simpa [prefixWord, tailWord_6898224, baseEnd_6898224] using wordTrace_append hprefix tailTrace_6898224
  have hstable : (prefixWord ++ tailWord_6898224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898224).length < 2 ^ (prefixWord ++ tailWord_6898224).sum := by decide
  have hdescent : baseEnd_6898224 < baseStart_6898224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898231 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_6898231 : Nat := 118140960795 + 6898231 * 2 ^ 59
def prefixEnd_6898231 : Nat := 4983230072969 + 3 ^ 40 * 6898231 * 2
def baseEnd_6898231 : Nat := 3542108168745305373188119

theorem tailTrace_6898231 : CollatzResearch.WordTrace tailWord_6898231 prefixEnd_6898231 3542108168745305373188119 := by
  unfold tailWord_6898231
  simp only [CollatzResearch.WordTrace]
  refine ⟨251599154271894685904662547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167732769514596457269775031 251599154271894685904662547)
  ·
    refine ⟨377398731407842028856993821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251599154271894685904662547 377398731407842028856993821)
    ·
      refine ⟨141524524277940760821372683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377398731407842028856993821 141524524277940760821372683)
      ·
        refine ⟨212286786416911141232059025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141524524277940760821372683 212286786416911141232059025)
        ·
          refine ⟨159215089812683355924044269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212286786416911141232059025 159215089812683355924044269)
          ·
            refine ⟨59705658679756258471516601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159215089812683355924044269 59705658679756258471516601)
            ·
              refine ⟨44779244009817193853637451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59705658679756258471516601 44779244009817193853637451)
              ·
                refine ⟨67168866014725790780456177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44779244009817193853637451 67168866014725790780456177)
                ·
                  refine ⟨50376649511044343085342133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67168866014725790780456177 50376649511044343085342133)
                  ·
                    refine ⟨4722810891660407164250825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50376649511044343085342133 4722810891660407164250825)
                    ·
                      refine ⟨3542108168745305373188119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4722810891660407164250825 3542108168745305373188119)
                      ·
                        rfl

theorem cell23_6898231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_6898231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898231 prefixEnd_6898231 := by exact prefixLift 6898231
  have htrace : WordTrace (prefixWord ++ tailWord_6898231) baseStart_6898231 baseEnd_6898231 := by
    simpa [prefixWord, tailWord_6898231, baseEnd_6898231] using wordTrace_append hprefix tailTrace_6898231
  have hstable : (prefixWord ++ tailWord_6898231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898231).length < 2 ^ (prefixWord ++ tailWord_6898231).sum := by decide
  have hdescent : baseEnd_6898231 < baseStart_6898231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898234 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_6898234 : Nat := 118140960795 + 6898234 * 2 ^ 59
def prefixEnd_6898234 : Nat := 4983230072969 + 3 ^ 40 * 6898234 * 2
def baseEnd_6898234 : Nat := 3542109709187268861450605

theorem tailTrace_6898234 : CollatzResearch.WordTrace tailWord_6898234 prefixEnd_6898234 3542109709187268861450605 := by
  unfold tailWord_6898234
  simp only [CollatzResearch.WordTrace]
  refine ⟨62899815922720954354255439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167732842460589211611347837 62899815922720954354255439)
  ·
    refine ⟨94349723884081431531383159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62899815922720954354255439 94349723884081431531383159)
    ·
      refine ⟨141524585826122147297074739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94349723884081431531383159 141524585826122147297074739)
      ·
        refine ⟨212286878739183220945612109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141524585826122147297074739 212286878739183220945612109)
        ·
          refine ⟨79607579527193707854604541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212286878739183220945612109 79607579527193707854604541)
          ·
            refine ⟨29852842322697640445476703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79607579527193707854604541 29852842322697640445476703)
            ·
              refine ⟨44779263484046460668215055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29852842322697640445476703 44779263484046460668215055)
              ·
                refine ⟨67168895226069691002322583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44779263484046460668215055 67168895226069691002322583)
                ·
                  refine ⟨100753342839104536503483875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67168895226069691002322583 100753342839104536503483875)
                  ·
                    refine ⟨151130014258656804755225813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100753342839104536503483875 151130014258656804755225813)
                    ·
                      refine ⟨3542109709187268861450605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151130014258656804755225813 3542109709187268861450605)
                      ·
                        rfl

theorem cell23_6898234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_6898234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898234 prefixEnd_6898234 := by exact prefixLift 6898234
  have htrace : WordTrace (prefixWord ++ tailWord_6898234) baseStart_6898234 baseEnd_6898234 := by
    simpa [prefixWord, tailWord_6898234, baseEnd_6898234] using wordTrace_append hprefix tailTrace_6898234
  have hstable : (prefixWord ++ tailWord_6898234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898234).length < 2 ^ (prefixWord ++ tailWord_6898234).sum := by decide
  have hdescent : baseEnd_6898234 < baseStart_6898234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898254 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_6898254 : Nat := 118140960795 + 6898254 * 2 ^ 59
def prefixEnd_6898254 : Nat := 4983230072969 + 3 ^ 40 * 6898254 * 2
def baseEnd_6898254 : Nat := 1180706659600119594400171

theorem tailTrace_6898254 : CollatzResearch.WordTrace tailWord_6898254 prefixEnd_6898254 1180706659600119594400171 := by
  unfold tailWord_6898254
  simp only [CollatzResearch.WordTrace]
  refine ⟨31449999143851420104093727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167733328767207573888499877 31449999143851420104093727)
  ·
    refine ⟨47174998715777130156140591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31449999143851420104093727 47174998715777130156140591)
    ·
      refine ⟨70762498073665695234210887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47174998715777130156140591 70762498073665695234210887)
      ·
        refine ⟨106143747110498542851316331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70762498073665695234210887 106143747110498542851316331)
        ·
          refine ⟨159215620665747814276974497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106143747110498542851316331 159215620665747814276974497)
          ·
            refine ⟨119411715499310860707730873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159215620665747814276974497 119411715499310860707730873)
            ·
              refine ⟨89558786624483145530798155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119411715499310860707730873 89558786624483145530798155)
              ·
                refine ⟨134338179936724718296197233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89558786624483145530798155 134338179936724718296197233)
                ·
                  refine ⟨100753634952543538722147925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134338179936724718296197233 100753634952543538722147925)
                  ·
                    refine ⟨1180706659600119594400171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100753634952543538722147925 1180706659600119594400171)
                    ·
                      rfl

theorem cell23_6898254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_6898254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898254 prefixEnd_6898254 := by exact prefixLift 6898254
  have htrace : WordTrace (prefixWord ++ tailWord_6898254) baseStart_6898254 baseEnd_6898254 := by
    simpa [prefixWord, tailWord_6898254, baseEnd_6898254] using wordTrace_append hprefix tailTrace_6898254
  have hstable : (prefixWord ++ tailWord_6898254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898254).length < 2 ^ (prefixWord ++ tailWord_6898254).sum := by decide
  have hdescent : baseEnd_6898254 < baseStart_6898254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898261 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6898261 : Nat := 118140960795 + 6898261 * 2 ^ 59
def prefixEnd_6898261 : Nat := 4983230072969 + 3 ^ 40 * 6898261 * 2
def baseEnd_6898261 : Nat := 3542123573164940255812981

theorem tailTrace_6898261 : CollatzResearch.WordTrace tailWord_6898261 prefixEnd_6898261 3542123573164940255812981 := by
  unfold tailWord_6898261
  simp only [CollatzResearch.WordTrace]
  refine ⟨251600248461786001028254637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167733498974524000685503091 251600248461786001028254637)
  ·
    refine ⟨94350093173169750385595489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251600248461786001028254637 94350093173169750385595489)
    ·
      refine ⟨70762569879877312789196617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94350093173169750385595489 70762569879877312789196617)
      ·
        refine ⟨53071927409907984591897463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70762569879877312789196617 53071927409907984591897463)
        ·
          refine ⟨79607891114861976887846195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53071927409907984591897463 79607891114861976887846195)
          ·
            refine ⟨119411836672292965331769293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79607891114861976887846195 119411836672292965331769293)
            ·
              refine ⟨44779438752109861999413485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119411836672292965331769293 44779438752109861999413485)
              ·
                refine ⟨16792289532041198249780057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44779438752109861999413485 16792289532041198249780057)
                ·
                  refine ⟨12594217149030898687335043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16792289532041198249780057 12594217149030898687335043)
                  ·
                    refine ⟨18891325723546348031002565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12594217149030898687335043 18891325723546348031002565)
                    ·
                      refine ⟨3542123573164940255812981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18891325723546348031002565 3542123573164940255812981)
                      ·
                        rfl

theorem cell23_6898261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6898261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898261 prefixEnd_6898261 := by exact prefixLift 6898261
  have htrace : WordTrace (prefixWord ++ tailWord_6898261) baseStart_6898261 baseEnd_6898261 := by
    simpa [prefixWord, tailWord_6898261, baseEnd_6898261] using wordTrace_append hprefix tailTrace_6898261
  have hstable : (prefixWord ++ tailWord_6898261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898261).length < 2 ^ (prefixWord ++ tailWord_6898261).sum := by decide
  have hdescent : baseEnd_6898261 < baseStart_6898261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898284 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 8]
def baseStart_6898284 : Nat := 118140960795 + 6898284 * 2 ^ 59
def prefixEnd_6898284 : Nat := 4983230072969 + 3 ^ 40 * 6898284 * 2
def baseEnd_6898284 : Nat := 393570598135554851758375

theorem tailTrace_6898284 : CollatzResearch.WordTrace tailWord_6898284 prefixEnd_6898284 393570598135554851758375 := by
  unfold tailWord_6898284
  simp only [CollatzResearch.WordTrace]
  refine ⟨125800543670351337978170953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167734058227135117304227937 125800543670351337978170953)
  ·
    refine ⟨94350407752763503483628215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125800543670351337978170953 94350407752763503483628215)
    ·
      refine ⟨141525611629145255225442323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94350407752763503483628215 141525611629145255225442323)
      ·
        refine ⟨212288417443717882838163485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141525611629145255225442323 212288417443717882838163485)
        ·
          refine ⟨79608156541394206064311307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212288417443717882838163485 79608156541394206064311307)
          ·
            refine ⟨119412234812091309096466961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79608156541394206064311307 119412234812091309096466961)
            ·
              refine ⟨89559176109068481822350221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119412234812091309096466961 89559176109068481822350221)
              ·
                refine ⟨33584691040900680683381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89559176109068481822350221 33584691040900680683381333)
                ·
                  refine ⟨393570598135554851758375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33584691040900680683381333 393570598135554851758375)
                  ·
                    rfl

theorem cell23_6898284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_6898284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898284 prefixEnd_6898284 := by exact prefixLift 6898284
  have htrace : WordTrace (prefixWord ++ tailWord_6898284) baseStart_6898284 baseEnd_6898284 := by
    simpa [prefixWord, tailWord_6898284, baseEnd_6898284] using wordTrace_append hprefix tailTrace_6898284
  have hstable : (prefixWord ++ tailWord_6898284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898284).length < 2 ^ (prefixWord ++ tailWord_6898284).sum := by decide
  have hdescent : baseEnd_6898284 < baseStart_6898284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898322 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_6898322 : Nat := 118140960795 + 6898322 * 2 ^ 59
def prefixEnd_6898322 : Nat := 4983230072969 + 3 ^ 40 * 6898322 * 2
def baseEnd_6898322 : Nat := 1180718298494954839050067

theorem tailTrace_6898322 : CollatzResearch.WordTrace tailWord_6898322 prefixEnd_6898322 1180718298494954839050067 := by
  unfold tailWord_6898322
  simp only [CollatzResearch.WordTrace]
  refine ⟨62900618328641252111556305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167734982209710005630816813 62900618328641252111556305)
  ·
    refine ⟨47175463746480939083667229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62900618328641252111556305 47175463746480939083667229)
    ·
      refine ⟨17690798904930352156375211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47175463746480939083667229 17690798904930352156375211)
      ·
        refine ⟨26536198357395528234562817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17690798904930352156375211 26536198357395528234562817)
        ·
          refine ⟨19902148768046646175922113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26536198357395528234562817 19902148768046646175922113)
          ·
            refine ⟨14926611576034984631941585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19902148768046646175922113 14926611576034984631941585)
            ·
              refine ⟨11194958682026238473956189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14926611576034984631941585 11194958682026238473956189)
              ·
                refine ⟨4198109505759839427733571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11194958682026238473956189 4198109505759839427733571)
                ·
                  refine ⟨6297164258639759141600357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198109505759839427733571 6297164258639759141600357)
                  ·
                    refine ⟨1180718298494954839050067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297164258639759141600357 1180718298494954839050067)
                    ·
                      rfl

theorem cell23_6898322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_6898322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898322 prefixEnd_6898322 := by exact prefixLift 6898322
  have htrace : WordTrace (prefixWord ++ tailWord_6898322) baseStart_6898322 baseEnd_6898322 := by
    simpa [prefixWord, tailWord_6898322, baseEnd_6898322] using wordTrace_append hprefix tailTrace_6898322
  have hstable : (prefixWord ++ tailWord_6898322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898322).length < 2 ^ (prefixWord ++ tailWord_6898322).sum := by decide
  have hdescent : baseEnd_6898322 < baseStart_6898322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898328 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_6898328 : Nat := 118140960795 + 6898328 * 2 ^ 59
def prefixEnd_6898328 : Nat := 4983230072969 + 3 ^ 40 * 6898328 * 2
def baseEnd_6898328 : Nat := 3542157976368791493675173

theorem tailTrace_6898328 : CollatzResearch.WordTrace tailWord_6898328 prefixEnd_6898328 3542157976368791493675173 := by
  unfold tailWord_6898328
  simp only [CollatzResearch.WordTrace]
  refine ⟨125801346076271635735471819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167735128101695514313962425 125801346076271635735471819)
  ·
    refine ⟨188702019114407453603207729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125801346076271635735471819 188702019114407453603207729)
    ·
      refine ⟨141526514335805590202405797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188702019114407453603207729 141526514335805590202405797)
      ·
        refine ⟨26536221437963548162951087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141526514335805590202405797 26536221437963548162951087)
        ·
          refine ⟨39804332156945322244426631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26536221437963548162951087 39804332156945322244426631)
          ·
            refine ⟨59706498235417983366639947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39804332156945322244426631 59706498235417983366639947)
            ·
              refine ⟨89559747353126975049959921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59706498235417983366639947 89559747353126975049959921)
              ·
                refine ⟨67169810514845231287469941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89559747353126975049959921 67169810514845231287469941)
                ·
                  refine ⟨6297169735766740433200307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67169810514845231287469941 6297169735766740433200307)
                  ·
                    refine ⟨9445754603650110649800461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297169735766740433200307 9445754603650110649800461)
                    ·
                      refine ⟨3542157976368791493675173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9445754603650110649800461 3542157976368791493675173)
                      ·
                        rfl

theorem cell23_6898328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_6898328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898328 prefixEnd_6898328 := by exact prefixLift 6898328
  have htrace : WordTrace (prefixWord ++ tailWord_6898328) baseStart_6898328 baseEnd_6898328 := by
    simpa [prefixWord, tailWord_6898328, baseEnd_6898328] using wordTrace_append hprefix tailTrace_6898328
  have hstable : (prefixWord ++ tailWord_6898328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898328).length < 2 ^ (prefixWord ++ tailWord_6898328).sum := by decide
  have hdescent : baseEnd_6898328 < baseStart_6898328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898368 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_6898368 : Nat := 118140960795 + 6898368 * 2 ^ 59
def prefixEnd_6898368 : Nat := 4983230072969 + 3 ^ 40 * 6898368 * 2
def baseEnd_6898368 : Nat := 3542178515594971337174989

theorem tailTrace_6898368 : CollatzResearch.WordTrace tailWord_6898368 prefixEnd_6898368 3542178515594971337174989 := by
  unfold tailWord_6898368
  simp only [CollatzResearch.WordTrace]
  refine ⟨125802075536199179151199879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167736100714932238868266505 125802075536199179151199879)
  ·
    refine ⟨188703113304298768726799819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125802075536199179151199879 188703113304298768726799819)
    ·
      refine ⟨283054669956448153090199729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188703113304298768726799819 283054669956448153090199729)
      ·
        refine ⟨212291002467336114817649797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283054669956448153090199729 212291002467336114817649797)
        ·
          refine ⟨39804562962625521528309337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212291002467336114817649797 39804562962625521528309337)
          ·
            refine ⟨29853422221969141146232003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39804562962625521528309337 29853422221969141146232003)
            ·
              refine ⟨44780133332953711719348005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29853422221969141146232003 44780133332953711719348005)
              ·
                refine ⟨8396274999928820947377751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44780133332953711719348005 8396274999928820947377751)
                ·
                  refine ⟨12594412499893231421066627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396274999928820947377751 12594412499893231421066627)
                  ·
                    refine ⟨18891618749839847131599941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12594412499893231421066627 18891618749839847131599941)
                    ·
                      refine ⟨3542178515594971337174989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18891618749839847131599941 3542178515594971337174989)
                      ·
                        rfl

theorem cell23_6898368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_6898368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898368 prefixEnd_6898368 := by exact prefixLift 6898368
  have htrace : WordTrace (prefixWord ++ tailWord_6898368) baseStart_6898368 baseEnd_6898368 := by
    simpa [prefixWord, tailWord_6898368, baseEnd_6898368] using wordTrace_append hprefix tailTrace_6898368
  have hstable : (prefixWord ++ tailWord_6898368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898368).length < 2 ^ (prefixWord ++ tailWord_6898368).sum := by decide
  have hdescent : baseEnd_6898368 < baseStart_6898368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898378 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_6898378 : Nat := 118140960795 + 6898378 * 2 ^ 59
def prefixEnd_6898378 : Nat := 4983230072969 + 3 ^ 40 * 6898378 * 2
def baseEnd_6898378 : Nat := 1180727883467172099349981

theorem tailTrace_6898378 : CollatzResearch.WordTrace tailWord_6898378 prefixEnd_6898378 1180727883467172099349981 := by
  unfold tailWord_6898378
  simp only [CollatzResearch.WordTrace]
  refine ⟨62901128950590532502565947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167736343868241420006842525 62901128950590532502565947)
  ·
    refine ⟨94351693425885798753848921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62901128950590532502565947 94351693425885798753848921)
    ·
      refine ⟨70763770069414349065386691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94351693425885798753848921 70763770069414349065386691)
      ·
        refine ⟨106145655104121523598080037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70763770069414349065386691 106145655104121523598080037)
        ·
          refine ⟨19902310332022785674640007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106145655104121523598080037 19902310332022785674640007)
          ·
            refine ⟨29853465498034178511960011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19902310332022785674640007 29853465498034178511960011)
            ·
              refine ⟨44780198247051267767940017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29853465498034178511960011 44780198247051267767940017)
              ·
                refine ⟨33585148685288450825955013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44780198247051267767940017 33585148685288450825955013)
                ·
                  refine ⟨6297215378491584529866565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33585148685288450825955013 6297215378491584529866565)
                  ·
                    refine ⟨1180727883467172099349981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297215378491584529866565 1180727883467172099349981)
                    ·
                      rfl

theorem cell23_6898378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_6898378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898378 prefixEnd_6898378 := by exact prefixLift 6898378
  have htrace : WordTrace (prefixWord ++ tailWord_6898378) baseStart_6898378 baseEnd_6898378 := by
    simpa [prefixWord, tailWord_6898378, baseEnd_6898378] using wordTrace_append hprefix tailTrace_6898378
  have hstable : (prefixWord ++ tailWord_6898378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898378).length < 2 ^ (prefixWord ++ tailWord_6898378).sum := by decide
  have hdescent : baseEnd_6898378 < baseStart_6898378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898391 : List Nat := [1, 1, 3, 2, 1, 6, 9]
def baseStart_6898391 : Nat := 118140960795 + 6898391 * 2 ^ 59
def prefixEnd_6898391 : Nat := 4983230072969 + 3 ^ 40 * 6898391 * 2
def baseEnd_6898391 : Nat := 43730744761111416631943

theorem tailTrace_6898391 : CollatzResearch.WordTrace tailWord_6898391 prefixEnd_6898391 43730744761111416631943 := by
  unfold tailWord_6898391
  simp only [CollatzResearch.WordTrace]
  refine ⟨251604989951315033230487027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167736659967543355486991351 251604989951315033230487027)
  ·
    refine ⟨377407484926972549845730541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251604989951315033230487027 377407484926972549845730541)
    ·
      refine ⟨141527806847614706192148953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377407484926972549845730541 141527806847614706192148953)
      ·
        refine ⟨106145855135711029644111715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141527806847614706192148953 106145855135711029644111715)
        ·
          refine ⟨159218782703566544466167573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106145855135711029644111715 159218782703566544466167573)
          ·
            refine ⟨7463380439229681771851605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159218782703566544466167573 7463380439229681771851605)
            ·
              refine ⟨43730744761111416631943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7463380439229681771851605 43730744761111416631943)
              ·
                rfl

theorem cell23_6898391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 9].length) (baseStart_6898391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898391 prefixEnd_6898391 := by exact prefixLift 6898391
  have htrace : WordTrace (prefixWord ++ tailWord_6898391) baseStart_6898391 baseEnd_6898391 := by
    simpa [prefixWord, tailWord_6898391, baseEnd_6898391] using wordTrace_append hprefix tailTrace_6898391
  have hstable : (prefixWord ++ tailWord_6898391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898391).length < 2 ^ (prefixWord ++ tailWord_6898391).sum := by decide
  have hdescent : baseEnd_6898391 < baseStart_6898391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898396 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6898396 : Nat := 118140960795 + 6898396 * 2 ^ 59
def prefixEnd_6898396 : Nat := 4983230072969 + 3 ^ 40 * 6898396 * 2
def baseEnd_6898396 : Nat := 3542192893053297227624861

theorem tailTrace_6898396 : CollatzResearch.WordTrace tailWord_6898396 prefixEnd_6898396 3542192893053297227624861 := by
  unfold tailWord_6898396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125802586158148459542209521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167736781544197946056279361 125802586158148459542209521)
  ·
    refine ⟨94351939618611344656657141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125802586158148459542209521 94351939618611344656657141)
    ·
      refine ⟨8845494339244813561561607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94351939618611344656657141 8845494339244813561561607)
      ·
        refine ⟨13268241508867220342342411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845494339244813561561607 13268241508867220342342411)
        ·
          refine ⟨19902362263300830513513617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13268241508867220342342411 19902362263300830513513617)
          ·
            refine ⟨14926771697475622885135213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19902362263300830513513617 14926771697475622885135213)
            ·
              refine ⟨5597539386553358581925705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14926771697475622885135213 5597539386553358581925705)
              ·
                refine ⟨4198154539915018936444279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597539386553358581925705 4198154539915018936444279)
                ·
                  refine ⟨6297231809872528404666419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198154539915018936444279 6297231809872528404666419)
                  ·
                    refine ⟨9445847714808792606999629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297231809872528404666419 9445847714808792606999629)
                    ·
                      refine ⟨3542192893053297227624861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9445847714808792606999629 3542192893053297227624861)
                      ·
                        rfl

theorem cell23_6898396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6898396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898396 prefixEnd_6898396 := by exact prefixLift 6898396
  have htrace : WordTrace (prefixWord ++ tailWord_6898396) baseStart_6898396 baseEnd_6898396 := by
    simpa [prefixWord, tailWord_6898396, baseEnd_6898396] using wordTrace_append hprefix tailTrace_6898396
  have hstable : (prefixWord ++ tailWord_6898396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898396).length < 2 ^ (prefixWord ++ tailWord_6898396).sum := by decide
  have hdescent : baseEnd_6898396 < baseStart_6898396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898408 : List Nat := [2, 1, 4, 1, 4, 1, 2, 8]
def baseStart_6898408 : Nat := 118140960795 + 6898408 * 2 ^ 59
def prefixEnd_6898408 : Nat := 4983230072969 + 3 ^ 40 * 6898408 * 2
def baseEnd_6898408 : Nat := 131192557585968562247215

theorem tailTrace_6898408 : CollatzResearch.WordTrace tailWord_6898408 prefixEnd_6898408 131192557585968562247215 := by
  unfold tailWord_6898408
  simp only [CollatzResearch.WordTrace]
  refine ⟨125802804996126722566927939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167737073328168963422570585 125802804996126722566927939)
  ·
    refine ⟨188704207494190083850391909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125802804996126722566927939 188704207494190083850391909)
    ·
      refine ⟨35382038905160640721948483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188704207494190083850391909 35382038905160640721948483)
      ·
        refine ⟨53073058357740961082922725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35382038905160640721948483 53073058357740961082922725)
        ·
          refine ⟨9951198442076430203048011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53073058357740961082922725 9951198442076430203048011)
          ·
            refine ⟨14926797663114645304572017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951198442076430203048011 14926797663114645304572017)
            ·
              refine ⟨11195098247335983978429013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14926797663114645304572017 11195098247335983978429013)
              ·
                refine ⟨131192557585968562247215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11195098247335983978429013 131192557585968562247215)
                ·
                  rfl

theorem cell23_6898408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 8].length) (baseStart_6898408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898408 prefixEnd_6898408 := by exact prefixLift 6898408
  have htrace : WordTrace (prefixWord ++ tailWord_6898408) baseStart_6898408 baseEnd_6898408 := by
    simpa [prefixWord, tailWord_6898408, baseEnd_6898408] using wordTrace_append hprefix tailTrace_6898408
  have hstable : (prefixWord ++ tailWord_6898408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898408).length < 2 ^ (prefixWord ++ tailWord_6898408).sum := by decide
  have hdescent : baseEnd_6898408 < baseStart_6898408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898451 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 2, 6]
def baseStart_6898451 : Nat := 118140960795 + 6898451 * 2 ^ 59
def prefixEnd_6898451 : Nat := 4983230072969 + 3 ^ 40 * 6898451 * 2
def baseEnd_6898451 : Nat := 1180740378163098170812369

theorem tailTrace_6898451 : CollatzResearch.WordTrace tailWord_6898451 prefixEnd_6898451 1180740378163098170812369 := by
  unfold tailWord_6898451
  simp only [CollatzResearch.WordTrace]
  refine ⟨251607178331097663477671207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167738118887398442318447471 251607178331097663477671207)
  ·
    refine ⟨377410767496646495216506811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251607178331097663477671207 377410767496646495216506811)
    ·
      refine ⟨566116151244969742824760217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377410767496646495216506811 566116151244969742824760217)
      ·
        refine ⟨424587113433727307118570163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566116151244969742824760217 424587113433727307118570163)
        ·
          refine ⟨636880670150590960677855245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424587113433727307118570163 636880670150590960677855245)
          ·
            refine ⟨238830251306471610254195717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636880670150590960677855245 238830251306471610254195717)
            ·
              refine ⟨44780672119963426922661697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238830251306471610254195717 44780672119963426922661697)
              ·
                refine ⟨33585504089972570191996273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44780672119963426922661697 33585504089972570191996273)
                ·
                  refine ⟨25189128067479427643997205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33585504089972570191996273 25189128067479427643997205)
                  ·
                    refine ⟨1180740378163098170812369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25189128067479427643997205 1180740378163098170812369)
                    ·
                      rfl

theorem cell23_6898451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_6898451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898451 prefixEnd_6898451 := by exact prefixLift 6898451
  have htrace : WordTrace (prefixWord ++ tailWord_6898451) baseStart_6898451 baseEnd_6898451 := by
    simpa [prefixWord, tailWord_6898451, baseEnd_6898451] using wordTrace_append hprefix tailTrace_6898451
  have hstable : (prefixWord ++ tailWord_6898451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898451).length < 2 ^ (prefixWord ++ tailWord_6898451).sum := by decide
  have hdescent : baseEnd_6898451 < baseStart_6898451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898565 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_6898565 : Nat := 118140960795 + 6898565 * 2 ^ 59
def prefixEnd_6898565 : Nat := 4983230072969 + 3 ^ 40 * 6898565 * 2
def baseEnd_6898565 : Nat := 3542279671283907066411583

theorem tailTrace_6898565 : CollatzResearch.WordTrace tailWord_6898565 prefixEnd_6898565 3542279671283907066411583 := by
  unfold tailWord_6898565
  simp only [CollatzResearch.WordTrace]
  refine ⟨251611336252684660947321149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167740890835123107298214099 251611336252684660947321149)
  ·
    refine ⟨94354251094756747855245431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251611336252684660947321149 94354251094756747855245431)
    ·
      refine ⟨141531376642135121782868147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94354251094756747855245431 141531376642135121782868147)
      ·
        refine ⟨212297064963202682674302221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141531376642135121782868147 212297064963202682674302221)
        ·
          refine ⟨79611399361201006002863333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212297064963202682674302221 79611399361201006002863333)
          ·
            refine ⟨14927137380225188625536875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79611399361201006002863333 14927137380225188625536875)
            ·
              refine ⟨22390706070337782938305313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14927137380225188625536875 22390706070337782938305313)
              ·
                refine ⟨16793029552753337203728985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22390706070337782938305313 16793029552753337203728985)
                ·
                  refine ⟨12594772164565002902796739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16793029552753337203728985 12594772164565002902796739)
                  ·
                    refine ⟨18892158246847504354195109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12594772164565002902796739 18892158246847504354195109)
                    ·
                      refine ⟨3542279671283907066411583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18892158246847504354195109 3542279671283907066411583)
                      ·
                        rfl

theorem cell23_6898565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_6898565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898565 prefixEnd_6898565 := by exact prefixLift 6898565
  have htrace : WordTrace (prefixWord ++ tailWord_6898565) baseStart_6898565 baseEnd_6898565 := by
    simpa [prefixWord, tailWord_6898565, baseEnd_6898565] using wordTrace_append hprefix tailTrace_6898565
  have hstable : (prefixWord ++ tailWord_6898565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898565).length < 2 ^ (prefixWord ++ tailWord_6898565).sum := by decide
  have hdescent : baseEnd_6898565 < baseStart_6898565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898666 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_6898666 : Nat := 118140960795 + 6898666 * 2 ^ 59
def prefixEnd_6898666 : Nat := 4983230072969 + 3 ^ 40 * 6898666 * 2
def baseEnd_6898666 : Nat := 3542331532830011171248619

theorem tailTrace_6898666 : CollatzResearch.WordTrace tailWord_6898666 prefixEnd_6898666 3542331532830011171248619 := by
  unfold tailWord_6898666
  simp only [CollatzResearch.WordTrace]
  refine ⟨62903755006329688799186963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167743346683545836797831901 62903755006329688799186963)
  ·
    refine ⟨94355632509494533198780445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62903755006329688799186963 94355632509494533198780445)
    ·
      refine ⟨35383362191060449949542667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94355632509494533198780445 35383362191060449949542667)
      ·
        refine ⟨53075043286590674924314001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35383362191060449949542667 53075043286590674924314001)
        ·
          refine ⟨39806282464943006193235501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53075043286590674924314001 39806282464943006193235501)
          ·
            refine ⟨14927355924353627322463313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39806282464943006193235501 14927355924353627322463313)
            ·
              refine ⟨11195516943265220491847485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14927355924353627322463313 11195516943265220491847485)
              ·
                refine ⟨4198318853724457684442807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11195516943265220491847485 4198318853724457684442807)
                ·
                  refine ⟨6297478280586686526664211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198318853724457684442807 6297478280586686526664211)
                  ·
                    refine ⟨9446217420880029789996317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297478280586686526664211 9446217420880029789996317)
                    ·
                      refine ⟨3542331532830011171248619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446217420880029789996317 3542331532830011171248619)
                      ·
                        rfl

theorem cell23_6898666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_6898666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898666 prefixEnd_6898666 := by exact prefixLift 6898666
  have htrace : WordTrace (prefixWord ++ tailWord_6898666) baseStart_6898666 baseEnd_6898666 := by
    simpa [prefixWord, tailWord_6898666, baseEnd_6898666] using wordTrace_append hprefix tailTrace_6898666
  have hstable : (prefixWord ++ tailWord_6898666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898666).length < 2 ^ (prefixWord ++ tailWord_6898666).sum := by decide
  have hdescent : baseEnd_6898666 < baseStart_6898666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898668 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_6898668 : Nat := 118140960795 + 6898668 * 2 ^ 59
def prefixEnd_6898668 : Nat := 4983230072969 + 3 ^ 40 * 6898668 * 2
def baseEnd_6898668 : Nat := 3542332559791320163423609

theorem tailTrace_6898668 : CollatzResearch.WordTrace tailWord_6898668 prefixEnd_6898668 3542332559791320163423609 := by
  unfold tailWord_6898668
  simp only [CollatzResearch.WordTrace]
  refine ⟨125807546485655754769160329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167743395314207673025547105 125807546485655754769160329)
  ·
    refine ⟨94355659864241816076870247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125807546485655754769160329 94355659864241816076870247)
    ·
      refine ⟨141533489796362724115305371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94355659864241816076870247 141533489796362724115305371)
      ·
        refine ⟨212300234694544086172958057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141533489796362724115305371 212300234694544086172958057)
        ·
          refine ⟨159225176020908064629718543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212300234694544086172958057 159225176020908064629718543)
          ·
            refine ⟨238837764031362096944577815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159225176020908064629718543 238837764031362096944577815)
            ·
              refine ⟨358256646047043145416866723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238837764031362096944577815 358256646047043145416866723)
              ·
                refine ⟨537384969070564718125300085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358256646047043145416866723 537384969070564718125300085)
                ·
                  refine ⟨50379840850365442324246883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 537384969070564718125300085 50379840850365442324246883)
                  ·
                    refine ⟨75569761275548163486370325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50379840850365442324246883 75569761275548163486370325)
                    ·
                      refine ⟨3542332559791320163423609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75569761275548163486370325 3542332559791320163423609)
                      ·
                        rfl

theorem cell23_6898668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_6898668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898668 prefixEnd_6898668 := by exact prefixLift 6898668
  have htrace : WordTrace (prefixWord ++ tailWord_6898668) baseStart_6898668 baseEnd_6898668 := by
    simpa [prefixWord, tailWord_6898668, baseEnd_6898668] using wordTrace_append hprefix tailTrace_6898668
  have hstable : (prefixWord ++ tailWord_6898668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898668).length < 2 ^ (prefixWord ++ tailWord_6898668).sum := by decide
  have hdescent : baseEnd_6898668 < baseStart_6898668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898672 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2]
def baseStart_6898672 : Nat := 118140960795 + 6898672 * 2 ^ 59
def prefixEnd_6898672 : Nat := 4983230072969 + 3 ^ 40 * 6898672 * 2
def baseEnd_6898672 : Nat := 3542334613713938147773591

theorem tailTrace_6898672 : CollatzResearch.WordTrace tailWord_6898672 prefixEnd_6898672 3542334613713938147773591 := by
  unfold tailWord_6898672
  simp only [CollatzResearch.WordTrace]
  refine ⟨125807619431648509110733135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167743492575531345480977513 125807619431648509110733135)
  ·
    refine ⟨188711429147472763666099703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125807619431648509110733135 188711429147472763666099703)
    ·
      refine ⟨283067143721209145499149555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188711429147472763666099703 283067143721209145499149555)
      ·
        refine ⟨424600715581813718248724333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283067143721209145499149555 424600715581813718248724333)
        ·
          refine ⟨159225268343180144343271625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424600715581813718248724333 159225268343180144343271625)
          ·
            refine ⟨119418951257385108257453719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159225268343180144343271625 119418951257385108257453719)
            ·
              refine ⟨179128426886077662386180579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119418951257385108257453719 179128426886077662386180579)
              ·
                refine ⟨268692640329116493579270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179128426886077662386180579 268692640329116493579270869)
                ·
                  refine ⟨6297483757713667818264161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268692640329116493579270869 6297483757713667818264161)
                  ·
                    refine ⟨4723112818285250863698121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297483757713667818264161 4723112818285250863698121)
                    ·
                      refine ⟨3542334613713938147773591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723112818285250863698121 3542334613713938147773591)
                      ·
                        rfl

theorem cell23_6898672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2].length) (baseStart_6898672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898672 prefixEnd_6898672 := by exact prefixLift 6898672
  have htrace : WordTrace (prefixWord ++ tailWord_6898672) baseStart_6898672 baseEnd_6898672 := by
    simpa [prefixWord, tailWord_6898672, baseEnd_6898672] using wordTrace_append hprefix tailTrace_6898672
  have hstable : (prefixWord ++ tailWord_6898672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898672).length < 2 ^ (prefixWord ++ tailWord_6898672).sum := by decide
  have hdescent : baseEnd_6898672 < baseStart_6898672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898689 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_6898689 : Nat := 118140960795 + 6898689 * 2 ^ 59
def prefixEnd_6898689 : Nat := 4983230072969 + 3 ^ 40 * 6898689 * 2
def baseEnd_6898689 : Nat := 3542343342885064581261013

theorem tailTrace_6898689 : CollatzResearch.WordTrace tailWord_6898689 prefixEnd_6898689 3542343342885064581261013 := by
  unfold tailWord_6898689
  simp only [CollatzResearch.WordTrace]
  refine ⟨251615858904235430124835121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167743905936156953416556747 251615858904235430124835121)
  ·
    refine ⟨188711894178176572593626341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251615858904235430124835121 188711894178176572593626341)
    ·
      refine ⟨35383480158408107361304939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188711894178176572593626341 35383480158408107361304939)
      ·
        refine ⟨53075220237612161041957409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35383480158408107361304939 53075220237612161041957409)
        ·
          refine ⟨39806415178209120781468057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53075220237612161041957409 39806415178209120781468057)
          ·
            refine ⟨29854811383656840586101043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39806415178209120781468057 29854811383656840586101043)
            ·
              refine ⟨44782217075485260879151565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29854811383656840586101043 44782217075485260879151565)
              ·
                refine ⟨16793331403306972829681837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44782217075485260879151565 16793331403306972829681837)
                ·
                  refine ⟨6297499276240114811130689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16793331403306972829681837 6297499276240114811130689)
                  ·
                    refine ⟨4723124457180086108348017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297499276240114811130689 4723124457180086108348017)
                    ·
                      refine ⟨3542343342885064581261013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723124457180086108348017 3542343342885064581261013)
                      ·
                        rfl

theorem cell23_6898689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_6898689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898689 prefixEnd_6898689 := by exact prefixLift 6898689
  have htrace : WordTrace (prefixWord ++ tailWord_6898689) baseStart_6898689 baseEnd_6898689 := by
    simpa [prefixWord, tailWord_6898689, baseEnd_6898689] using wordTrace_append hprefix tailTrace_6898689
  have hstable : (prefixWord ++ tailWord_6898689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898689).length < 2 ^ (prefixWord ++ tailWord_6898689).sum := by decide
  have hdescent : baseEnd_6898689 < baseStart_6898689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898699 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 2, 4]
def baseStart_6898699 : Nat := 118140960795 + 6898699 * 2 ^ 59
def prefixEnd_6898699 : Nat := 4983230072969 + 3 ^ 40 * 6898699 * 2
def baseEnd_6898699 : Nat := 1180782825897203180711989

theorem tailTrace_6898699 : CollatzResearch.WordTrace tailWord_6898699 prefixEnd_6898699 1180782825897203180711989 := by
  unfold tailWord_6898699
  simp only [CollatzResearch.WordTrace]
  refine ⟨251616223634199201832699151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167744149089466134555132767 251616223634199201832699151)
  ·
    refine ⟨377424335451298802749048727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251616223634199201832699151 377424335451298802749048727)
    ·
      refine ⟨566136503176948204123573091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377424335451298802749048727 566136503176948204123573091)
      ·
        refine ⟨849204754765422306185359637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566136503176948204123573091 849204754765422306185359637)
        ·
          refine ⟨39806472879629170602438733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 849204754765422306185359637 39806472879629170602438733)
          ·
            refine ⟨14927427329860938975914525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39806472879629170602438733 14927427329860938975914525)
            ·
              refine ⟨5597785248697852115967947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14927427329860938975914525 5597785248697852115967947)
              ·
                refine ⟨8396677873046778173951921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597785248697852115967947 8396677873046778173951921)
                ·
                  refine ⟨6297508404785083630463941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8396677873046778173951921 6297508404785083630463941)
                  ·
                    refine ⟨1180782825897203180711989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297508404785083630463941 1180782825897203180711989)
                    ·
                      rfl

theorem cell23_6898699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 4].length) (baseStart_6898699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898699 prefixEnd_6898699 := by exact prefixLift 6898699
  have htrace : WordTrace (prefixWord ++ tailWord_6898699) baseStart_6898699 baseEnd_6898699 := by
    simpa [prefixWord, tailWord_6898699, baseEnd_6898699] using wordTrace_append hprefix tailTrace_6898699
  have hstable : (prefixWord ++ tailWord_6898699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898699).length < 2 ^ (prefixWord ++ tailWord_6898699).sum := by decide
  have hdescent : baseEnd_6898699 < baseStart_6898699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898702 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6898702 : Nat := 118140960795 + 6898702 * 2 ^ 59
def prefixEnd_6898702 : Nat := 4983230072969 + 3 ^ 40 * 6898702 * 2
def baseEnd_6898702 : Nat := 3542350018133573030398453

theorem tailTrace_6898702 : CollatzResearch.WordTrace tailWord_6898702 prefixEnd_6898702 3542350018133573030398453 := by
  unfold tailWord_6898702
  simp only [CollatzResearch.WordTrace]
  refine ⟨31452041631648541668132295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167744222035458888896705573 31452041631648541668132295)
  ·
    refine ⟨47178062447472812502198443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31452041631648541668132295 47178062447472812502198443)
    ·
      refine ⟨70767093671209218753297665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47178062447472812502198443 70767093671209218753297665)
      ·
        refine ⟨53075320253406914064973249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70767093671209218753297665 53075320253406914064973249)
        ·
          refine ⟨39806490190055185548729937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53075320253406914064973249 39806490190055185548729937)
          ·
            refine ⟨29854867642541389161547453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39806490190055185548729937 29854867642541389161547453)
            ·
              refine ⟨11195575365953020935580295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29854867642541389161547453 11195575365953020935580295)
              ·
                refine ⟨16793363048929531403370443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11195575365953020935580295 16793363048929531403370443)
                ·
                  refine ⟨25190044573394297105055665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16793363048929531403370443 25190044573394297105055665)
                  ·
                    refine ⟨18892533430045722828791749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25190044573394297105055665 18892533430045722828791749)
                    ·
                      refine ⟨3542350018133573030398453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18892533430045722828791749 3542350018133573030398453)
                      ·
                        rfl

theorem cell23_6898702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6898702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898702 prefixEnd_6898702 := by exact prefixLift 6898702
  have htrace : WordTrace (prefixWord ++ tailWord_6898702) baseStart_6898702 baseEnd_6898702 := by
    simpa [prefixWord, tailWord_6898702, baseEnd_6898702] using wordTrace_append hprefix tailTrace_6898702
  have hstable : (prefixWord ++ tailWord_6898702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898702).length < 2 ^ (prefixWord ++ tailWord_6898702).sum := by decide
  have hdescent : baseEnd_6898702 < baseStart_6898702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898709 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_6898709 : Nat := 118140960795 + 6898709 * 2 ^ 59
def prefixEnd_6898709 : Nat := 4983230072969 + 3 ^ 40 * 6898709 * 2
def baseEnd_6898709 : Nat := 3542353612498154503010921

theorem tailTrace_6898709 : CollatzResearch.WordTrace tailWord_6898709 prefixEnd_6898709 3542353612498154503010921 := by
  unfold tailWord_6898709
  simp only [CollatzResearch.WordTrace]
  refine ⟨251616588364162973540563181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167744392242775315693708787 251616588364162973540563181)
  ·
    refine ⟨94356220636561115077711193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251616588364162973540563181 94356220636561115077711193)
    ·
      refine ⟨70767165477420836308283395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94356220636561115077711193 70767165477420836308283395)
      ·
        refine ⟨106150748216131254462425093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70767165477420836308283395 106150748216131254462425093)
        ·
          refine ⟨19903265290524610211704705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106150748216131254462425093 19903265290524610211704705)
          ·
            refine ⟨14927448967893457658778529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903265290524610211704705 14927448967893457658778529)
            ·
              refine ⟨11195586725920093244083897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14927448967893457658778529 11195586725920093244083897)
              ·
                refine ⟨8396690044440069933062923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11195586725920093244083897 8396690044440069933062923)
                ·
                  refine ⟨12595035066660104899594385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396690044440069933062923 12595035066660104899594385)
                  ·
                    refine ⟨9446276299995078674695789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12595035066660104899594385 9446276299995078674695789)
                    ·
                      refine ⟨3542353612498154503010921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446276299995078674695789 3542353612498154503010921)
                      ·
                        rfl

theorem cell23_6898709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_6898709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898709 prefixEnd_6898709 := by exact prefixLift 6898709
  have htrace : WordTrace (prefixWord ++ tailWord_6898709) baseStart_6898709 baseEnd_6898709 := by
    simpa [prefixWord, tailWord_6898709, baseEnd_6898709] using wordTrace_append hprefix tailTrace_6898709
  have hstable : (prefixWord ++ tailWord_6898709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898709).length < 2 ^ (prefixWord ++ tailWord_6898709).sum := by decide
  have hdescent : baseEnd_6898709 < baseStart_6898709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898712 : List Nat := [2, 1, 2, 3, 2, 4, 2, 7]
def baseStart_6898712 : Nat := 118140960795 + 6898712 * 2 ^ 59
def prefixEnd_6898712 : Nat := 4983230072969 + 3 ^ 40 * 6898712 * 2
def baseEnd_6898712 : Nat := 131198338997782147824941

theorem tailTrace_6898712 : CollatzResearch.WordTrace tailWord_6898712 prefixEnd_6898712 131198338997782147824941 := by
  unfold tailWord_6898712
  simp only [CollatzResearch.WordTrace]
  refine ⟨125808348891576052526461195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167744465188768070035281593 125808348891576052526461195)
  ·
    refine ⟨188712523337364078789691793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125808348891576052526461195 188712523337364078789691793)
    ·
      refine ⟨141534392503023059092268845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188712523337364078789691793 141534392503023059092268845)
      ·
        refine ⟨53075397188633647159600817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141534392503023059092268845 53075397188633647159600817)
        ·
          refine ⟨39806547891475235369700613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53075397188633647159600817 39806547891475235369700613)
          ·
            refine ⟨7463727729651606631818865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39806547891475235369700613 7463727729651606631818865)
            ·
              refine ⟨5597795797238704973864149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7463727729651606631818865 5597795797238704973864149)
              ·
                refine ⟨131198338997782147824941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5597795797238704973864149 131198338997782147824941)
                ·
                  rfl

theorem cell23_6898712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 7].length) (baseStart_6898712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898712 prefixEnd_6898712 := by exact prefixLift 6898712
  have htrace : WordTrace (prefixWord ++ tailWord_6898712) baseStart_6898712 baseEnd_6898712 := by
    simpa [prefixWord, tailWord_6898712, baseEnd_6898712] using wordTrace_append hprefix tailTrace_6898712
  have hstable : (prefixWord ++ tailWord_6898712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898712).length < 2 ^ (prefixWord ++ tailWord_6898712).sum := by decide
  have hdescent : baseEnd_6898712 < baseStart_6898712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898723 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 1, 2, 2]
def baseStart_6898723 : Nat := 118140960795 + 6898723 * 2 ^ 59
def prefixEnd_6898723 : Nat := 4983230072969 + 3 ^ 40 * 6898723 * 2
def baseEnd_6898723 : Nat := 3542360801227317448235857

theorem tailTrace_6898723 : CollatzResearch.WordTrace tailWord_6898723 prefixEnd_6898723 3542360801227317448235857 := by
  unfold tailWord_6898723
  simp only [CollatzResearch.WordTrace]
  refine ⟨251617098986112253931572823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167744732657408169287715215 251617098986112253931572823)
  ·
    refine ⟨377425648479168380897359235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251617098986112253931572823 377425648479168380897359235)
    ·
      refine ⟨566138472718752571346038853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377425648479168380897359235 566138472718752571346038853)
      ·
        refine ⟨106150963634766107127382285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566138472718752571346038853 106150963634766107127382285)
        ·
          refine ⟨39806611363037290172768357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106150963634766107127382285 39806611363037290172768357)
          ·
            refine ⟨7463739630569491907394067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39806611363037290172768357 7463739630569491907394067)
            ·
              refine ⟨11195609445854237861091101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7463739630569491907394067 11195609445854237861091101)
              ·
                refine ⟨4198353542195339197909163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11195609445854237861091101 4198353542195339197909163)
                ·
                  refine ⟨6297530313293008796863745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198353542195339197909163 6297530313293008796863745)
                  ·
                    refine ⟨4723147734969756597647809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297530313293008796863745 4723147734969756597647809)
                    ·
                      refine ⟨3542360801227317448235857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723147734969756597647809 3542360801227317448235857)
                      ·
                        rfl

theorem cell23_6898723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_6898723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898723 prefixEnd_6898723 := by exact prefixLift 6898723
  have htrace : WordTrace (prefixWord ++ tailWord_6898723) baseStart_6898723 baseEnd_6898723 := by
    simpa [prefixWord, tailWord_6898723, baseEnd_6898723] using wordTrace_append hprefix tailTrace_6898723
  have hstable : (prefixWord ++ tailWord_6898723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898723).length < 2 ^ (prefixWord ++ tailWord_6898723).sum := by decide
  have hdescent : baseEnd_6898723 < baseStart_6898723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898775 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_6898775 : Nat := 118140960795 + 6898775 * 2 ^ 59
def prefixEnd_6898775 : Nat := 4983230072969 + 3 ^ 40 * 6898775 * 2
def baseEnd_6898775 : Nat := 3542387502221351244785617

theorem tailTrace_6898775 : CollatzResearch.WordTrace tailWord_6898775 prefixEnd_6898775 3542387502221351244785617 := by
  unfold tailWord_6898775
  simp only [CollatzResearch.WordTrace]
  refine ⟨251618995581923866812465779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167745997054615911208310519 251618995581923866812465779)
  ·
    refine ⟨377428493372885800218698669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251618995581923866812465779 377428493372885800218698669)
    ·
      refine ⟨141535685014832175082012001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377428493372885800218698669 141535685014832175082012001)
      ·
        refine ⟨106151763761124131311509001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141535685014832175082012001 106151763761124131311509001)
        ·
          refine ⟨79613822820843098483631751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106151763761124131311509001 79613822820843098483631751)
          ·
            refine ⟨119420734231264647725447627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79613822820843098483631751 119420734231264647725447627)
            ·
              refine ⟨179131101346896971588171441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119420734231264647725447627 179131101346896971588171441)
              ·
                refine ⟨134348326010172728691128581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179131101346896971588171441 134348326010172728691128581)
                ·
                  refine ⟨25190311126907386629586609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134348326010172728691128581 25190311126907386629586609)
                  ·
                    refine ⟨18892733345180539972189957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25190311126907386629586609 18892733345180539972189957)
                    ·
                      refine ⟨3542387502221351244785617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18892733345180539972189957 3542387502221351244785617)
                      ·
                        rfl

theorem cell23_6898775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_6898775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898775 prefixEnd_6898775 := by exact prefixLift 6898775
  have htrace : WordTrace (prefixWord ++ tailWord_6898775) baseStart_6898775 baseEnd_6898775 := by
    simpa [prefixWord, tailWord_6898775, baseEnd_6898775] using wordTrace_append hprefix tailTrace_6898775
  have hstable : (prefixWord ++ tailWord_6898775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898775).length < 2 ^ (prefixWord ++ tailWord_6898775).sum := by decide
  have hdescent : baseEnd_6898775 < baseStart_6898775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898795 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3]
def baseStart_6898795 : Nat := 118140960795 + 6898795 * 2 ^ 59
def prefixEnd_6898795 : Nat := 4983230072969 + 3 ^ 40 * 6898795 * 2
def baseEnd_6898795 : Nat := 3542397771834441166535525

theorem tailTrace_6898795 : CollatzResearch.WordTrace tailWord_6898795 prefixEnd_6898795 3542397771834441166535525 := by
  unfold tailWord_6898795
  simp only [CollatzResearch.WordTrace]
  refine ⟨251619725041851410228193839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167746483361234273485462559 251619725041851410228193839)
  ·
    refine ⟨377429587562777115342290759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251619725041851410228193839 377429587562777115342290759)
    ·
      refine ⟨566144381344165673013436139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377429587562777115342290759 566144381344165673013436139)
      ·
        refine ⟨849216572016248509520154209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566144381344165673013436139 849216572016248509520154209)
        ·
          refine ⟨636912429012186382140115657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849216572016248509520154209 636912429012186382140115657)
          ·
            refine ⟨477684321759139786605086743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636912429012186382140115657 477684321759139786605086743)
            ·
              refine ⟨716526482638709679907630115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477684321759139786605086743 716526482638709679907630115)
              ·
                refine ⟨1074789723958064519861445173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716526482638709679907630115 1074789723958064519861445173)
                ·
                  refine ⟨100761536621068548737010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074789723958064519861445173 100761536621068548737010485)
                  ·
                    refine ⟨9446394058225176444094733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100761536621068548737010485 9446394058225176444094733)
                    ·
                      refine ⟨3542397771834441166535525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446394058225176444094733 3542397771834441166535525)
                      ·
                        rfl

theorem cell23_6898795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3].length) (baseStart_6898795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898795 prefixEnd_6898795 := by exact prefixLift 6898795
  have htrace : WordTrace (prefixWord ++ tailWord_6898795) baseStart_6898795 baseEnd_6898795 := by
    simpa [prefixWord, tailWord_6898795, baseEnd_6898795] using wordTrace_append hprefix tailTrace_6898795
  have hstable : (prefixWord ++ tailWord_6898795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898795).length < 2 ^ (prefixWord ++ tailWord_6898795).sum := by decide
  have hdescent : baseEnd_6898795 < baseStart_6898795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898796 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_6898796 : Nat := 118140960795 + 6898796 * 2 ^ 59
def prefixEnd_6898796 : Nat := 4983230072969 + 3 ^ 40 * 6898796 * 2
def baseEnd_6898796 : Nat := 3542398285315095662623021

theorem tailTrace_6898796 : CollatzResearch.WordTrace tailWord_6898796 prefixEnd_6898796 3542398285315095662623021 := by
  unfold tailWord_6898796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125809880757423893699490121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167746507676565191599320161 125809880757423893699490121)
  ·
    refine ⟨94357410568067920274617591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125809880757423893699490121 94357410568067920274617591)
    ·
      refine ⟨141536115852101880411926387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94357410568067920274617591 141536115852101880411926387)
      ·
        refine ⟨212304173778152820617889581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141536115852101880411926387 212304173778152820617889581)
        ·
          refine ⟨79614065166807307731708593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212304173778152820617889581 79614065166807307731708593)
          ·
            refine ⟨59710548875105480798781445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79614065166807307731708593 59710548875105480798781445)
            ·
              refine ⟨11195727914082277649771521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59710548875105480798781445 11195727914082277649771521)
              ·
                refine ⟨8396795935561708237328641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11195727914082277649771521 8396795935561708237328641)
                ·
                  refine ⟨6297596951671281177996481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8396795935561708237328641 6297596951671281177996481)
                  ·
                    refine ⟨4723197713753460883497361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297596951671281177996481 4723197713753460883497361)
                    ·
                      refine ⟨3542398285315095662623021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723197713753460883497361 3542398285315095662623021)
                      ·
                        rfl

theorem cell23_6898796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_6898796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898796 prefixEnd_6898796 := by exact prefixLift 6898796
  have htrace : WordTrace (prefixWord ++ tailWord_6898796) baseStart_6898796 baseEnd_6898796 := by
    simpa [prefixWord, tailWord_6898796, baseEnd_6898796] using wordTrace_append hprefix tailTrace_6898796
  have hstable : (prefixWord ++ tailWord_6898796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898796).length < 2 ^ (prefixWord ++ tailWord_6898796).sum := by decide
  have hdescent : baseEnd_6898796 < baseStart_6898796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898812 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_6898812 : Nat := 118140960795 + 6898812 * 2 ^ 59
def prefixEnd_6898812 : Nat := 4983230072969 + 3 ^ 40 * 6898812 * 2
def baseEnd_6898812 : Nat := 3542406501005567600022947

theorem tailTrace_6898812 : CollatzResearch.WordTrace tailWord_6898812 prefixEnd_6898812 3542406501005567600022947 := by
  unfold tailWord_6898812
  simp only [CollatzResearch.WordTrace]
  refine ⟨125810172541394911065781345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167746896721859881421041793 125810172541394911065781345)
  ·
    refine ⟨94357629406046183299336009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125810172541394911065781345 94357629406046183299336009)
    ·
      refine ⟨70768222054534637474502007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94357629406046183299336009 70768222054534637474502007)
      ·
        refine ⟨106152333081801956211753011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70768222054534637474502007 106152333081801956211753011)
        ·
          refine ⟨159228499622702934317629517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106152333081801956211753011 159228499622702934317629517)
          ·
            refine ⟨59710687358513600369111069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159228499622702934317629517 59710687358513600369111069)
            ·
              refine ⟨22391507759442600138416651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59710687358513600369111069 22391507759442600138416651)
              ·
                refine ⟨33587261639163900207624977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22391507759442600138416651 33587261639163900207624977)
                ·
                  refine ⟨25190446229372925155718733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33587261639163900207624977 25190446229372925155718733)
                  ·
                    refine ⟨9446417336014846933394525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25190446229372925155718733 9446417336014846933394525)
                    ·
                      refine ⟨3542406501005567600022947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446417336014846933394525 3542406501005567600022947)
                      ·
                        rfl

theorem cell23_6898812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_6898812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898812 prefixEnd_6898812 := by exact prefixLift 6898812
  have htrace : WordTrace (prefixWord ++ tailWord_6898812) baseStart_6898812 baseEnd_6898812 := by
    simpa [prefixWord, tailWord_6898812, baseEnd_6898812] using wordTrace_append hprefix tailTrace_6898812
  have hstable : (prefixWord ++ tailWord_6898812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898812).length < 2 ^ (prefixWord ++ tailWord_6898812).sum := by decide
  have hdescent : baseEnd_6898812 < baseStart_6898812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898872 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_6898872 : Nat := 118140960795 + 6898872 * 2 ^ 59
def prefixEnd_6898872 : Nat := 4983230072969 + 3 ^ 40 * 6898872 * 2
def baseEnd_6898872 : Nat := 3542437309844837365272671

theorem tailTrace_6898872 : CollatzResearch.WordTrace tailWord_6898872 prefixEnd_6898872 3542437309844837365272671 := by
  unfold tailWord_6898872
  simp only [CollatzResearch.WordTrace]
  refine ⟨125811266731286226189373435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167748355641714968252497913 125811266731286226189373435)
  ·
    refine ⟨188716900096929339284060153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125811266731286226189373435 188716900096929339284060153)
    ·
      refine ⟨141537675072697004463045115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188716900096929339284060153 141537675072697004463045115)
      ·
        refine ⟨212306512609045506694567673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141537675072697004463045115 212306512609045506694567673)
        ·
          refine ⟨159229884456784130020925755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212306512609045506694567673 159229884456784130020925755)
          ·
            refine ⟨238844826685176195031388633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159229884456784130020925755 238844826685176195031388633)
            ·
              refine ⟨179133620013882146273541475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238844826685176195031388633 179133620013882146273541475)
              ·
                refine ⟨268700430020823219410312213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179133620013882146273541475 268700430020823219410312213)
                ·
                  refine ⟨12595332657226088409858385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268700430020823219410312213 12595332657226088409858385)
                  ·
                    refine ⟨9446499492919566307393789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12595332657226088409858385 9446499492919566307393789)
                    ·
                      refine ⟨3542437309844837365272671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446499492919566307393789 3542437309844837365272671)
                      ·
                        rfl

theorem cell23_6898872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_6898872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898872 prefixEnd_6898872 := by exact prefixLift 6898872
  have htrace : WordTrace (prefixWord ++ tailWord_6898872) baseStart_6898872 baseEnd_6898872 := by
    simpa [prefixWord, tailWord_6898872, baseEnd_6898872] using wordTrace_append hprefix tailTrace_6898872
  have hstable : (prefixWord ++ tailWord_6898872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898872).length < 2 ^ (prefixWord ++ tailWord_6898872).sum := by decide
  have hdescent : baseEnd_6898872 < baseStart_6898872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898895 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_6898895 : Nat := 118140960795 + 6898895 * 2 ^ 59
def prefixEnd_6898895 : Nat := 4983230072969 + 3 ^ 40 * 6898895 * 2
def baseEnd_6898895 : Nat := 3542449119899890775285065

theorem tailTrace_6898895 : CollatzResearch.WordTrace tailWord_6898895 prefixEnd_6898895 3542449119899890775285065 := by
  unfold tailWord_6898895
  simp only [CollatzResearch.WordTrace]
  refine ⟨251623372341489127306834139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167748914894326084871222759 251623372341489127306834139)
  ·
    refine ⟨377435058512233690960251209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251623372341489127306834139 377435058512233690960251209)
    ·
      refine ⟨283076293884175268220188407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377435058512233690960251209 283076293884175268220188407)
      ·
        refine ⟨424614440826262902330282611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283076293884175268220188407 424614440826262902330282611)
        ·
          refine ⟨636921661239394353495423917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424614440826262902330282611 636921661239394353495423917)
          ·
            refine ⟨238845622964772882560783969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636921661239394353495423917 238845622964772882560783969)
            ·
              refine ⟨179134217223579661920587977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238845622964772882560783969 179134217223579661920587977)
              ·
                refine ⟨134350662917684746440440983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179134217223579661920587977 134350662917684746440440983)
                ·
                  refine ⟨201525994376527119660661475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134350662917684746440440983 201525994376527119660661475)
                  ·
                    refine ⟨302288991564790679490992213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201525994376527119660661475 302288991564790679490992213)
                    ·
                      refine ⟨3542449119899890775285065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 302288991564790679490992213 3542449119899890775285065)
                      ·
                        rfl

theorem cell23_6898895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_6898895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898895 prefixEnd_6898895 := by exact prefixLift 6898895
  have htrace : WordTrace (prefixWord ++ tailWord_6898895) baseStart_6898895 baseEnd_6898895 := by
    simpa [prefixWord, tailWord_6898895, baseEnd_6898895] using wordTrace_append hprefix tailTrace_6898895
  have hstable : (prefixWord ++ tailWord_6898895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898895).length < 2 ^ (prefixWord ++ tailWord_6898895).sum := by decide
  have hdescent : baseEnd_6898895 < baseStart_6898895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898913 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 1, 4]
def baseStart_6898913 : Nat := 118140960795 + 6898913 * 2 ^ 59
def prefixEnd_6898913 : Nat := 4983230072969 + 3 ^ 40 * 6898913 * 2
def baseEnd_6898913 : Nat := 1180819454183890568286661

theorem tailTrace_6898913 : CollatzResearch.WordTrace tailWord_6898913 prefixEnd_6898913 1180819454183890568286661 := by
  unfold tailWord_6898913
  simp only [CollatzResearch.WordTrace]
  refine ⟨251624028855423916380989393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167749352570282610920659595 251624028855423916380989393)
  ·
    refine ⟨188718021641567937285742045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251624028855423916380989393 188718021641567937285742045)
    ·
      refine ⟨70769258115587976482153267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188718021641567937285742045 70769258115587976482153267)
      ·
        refine ⟨106153887173381964723229901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70769258115587976482153267 106153887173381964723229901)
        ·
          refine ⟨39807707690018236771211213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106153887173381964723229901 39807707690018236771211213)
          ·
            refine ⟨14927890383756838789204205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39807707690018236771211213 14927890383756838789204205)
            ·
              refine ⟨5597958893908814545951577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14927890383756838789204205 5597958893908814545951577)
              ·
                refine ⟨4198469170431610909463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597958893908814545951577 4198469170431610909463683)
                ·
                  refine ⟨6297703755647416364195525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198469170431610909463683 6297703755647416364195525)
                  ·
                    refine ⟨1180819454183890568286661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297703755647416364195525 1180819454183890568286661)
                    ·
                      rfl

theorem cell23_6898913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_6898913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898913 prefixEnd_6898913 := by exact prefixLift 6898913
  have htrace : WordTrace (prefixWord ++ tailWord_6898913) baseStart_6898913 baseEnd_6898913 := by
    simpa [prefixWord, tailWord_6898913, baseEnd_6898913] using wordTrace_append hprefix tailTrace_6898913
  have hstable : (prefixWord ++ tailWord_6898913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898913).length < 2 ^ (prefixWord ++ tailWord_6898913).sum := by decide
  have hdescent : baseEnd_6898913 < baseStart_6898913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898929 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_6898929 : Nat := 118140960795 + 6898929 * 2 ^ 59
def prefixEnd_6898929 : Nat := 4983230072969 + 3 ^ 40 * 6898929 * 2
def baseEnd_6898929 : Nat := 3542466578242143642259909

theorem tailTrace_6898929 : CollatzResearch.WordTrace tailWord_6898929 prefixEnd_6898929 3542466578242143642259909 := by
  unfold tailWord_6898929
  simp only [CollatzResearch.WordTrace]
  refine ⟨251624612423365951113571841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167749741615577300742381227 251624612423365951113571841)
  ·
    refine ⟨188718459317524463335178881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251624612423365951113571841 188718459317524463335178881)
    ·
      refine ⟨141538844488143347501384161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188718459317524463335178881 141538844488143347501384161)
      ·
        refine ⟨106154133366107510626038121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141538844488143347501384161 106154133366107510626038121)
        ·
          refine ⟨79615600024580632969528591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106154133366107510626038121 79615600024580632969528591)
          ·
            refine ⟨119423400036870949454292887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79615600024580632969528591 119423400036870949454292887)
            ·
              refine ⟨179135100055306424181439331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119423400036870949454292887 179135100055306424181439331)
              ·
                refine ⟨268702650082959636272158997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179135100055306424181439331 268702650082959636272158997)
                ·
                  refine ⟨12595436722638732950257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268702650082959636272158997 12595436722638732950257453)
                  ·
                    refine ⟨4723288770989524856346545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12595436722638732950257453 4723288770989524856346545)
                    ·
                      refine ⟨3542466578242143642259909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723288770989524856346545 3542466578242143642259909)
                      ·
                        rfl

theorem cell23_6898929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_6898929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898929 prefixEnd_6898929 := by exact prefixLift 6898929
  have htrace : WordTrace (prefixWord ++ tailWord_6898929) baseStart_6898929 baseEnd_6898929 := by
    simpa [prefixWord, tailWord_6898929, baseEnd_6898929] using wordTrace_append hprefix tailTrace_6898929
  have hstable : (prefixWord ++ tailWord_6898929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898929).length < 2 ^ (prefixWord ++ tailWord_6898929).sum := by decide
  have hdescent : baseEnd_6898929 < baseStart_6898929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898956 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_6898956 : Nat := 118140960795 + 6898956 * 2 ^ 59
def prefixEnd_6898956 : Nat := 4983230072969 + 3 ^ 40 * 6898956 * 2
def baseEnd_6898956 : Nat := 1180826814073271678874095

theorem tailTrace_6898956 : CollatzResearch.WordTrace tailWord_6898956 prefixEnd_6898956 1180826814073271678874095 := by
  unfold tailWord_6898956
  simp only [CollatzResearch.WordTrace]
  refine ⟨125812798597134067362402361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167750398129512089816536481 125812798597134067362402361)
  ·
    refine ⟨94359598947850550521801771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125812798597134067362402361 94359598947850550521801771)
    ·
      refine ⟨141539398421775825782702657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94359598947850550521801771 141539398421775825782702657)
      ·
        refine ⟨106154548816331869337026993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141539398421775825782702657 106154548816331869337026993)
        ·
          refine ⟨79615911612248902002770245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106154548816331869337026993 79615911612248902002770245)
          ·
            refine ⟨14927983427296669125519421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79615911612248902002770245 14927983427296669125519421)
            ·
              refine ⟨5597993785236250922069783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14927983427296669125519421 5597993785236250922069783)
              ·
                refine ⟨8396990677854376383104675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597993785236250922069783 8396990677854376383104675)
                ·
                  refine ⟨12595486016781564574657013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396990677854376383104675 12595486016781564574657013)
                  ·
                    refine ⟨1180826814073271678874095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12595486016781564574657013 1180826814073271678874095)
                    ·
                      rfl

theorem cell23_6898956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_6898956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898956 prefixEnd_6898956 := by exact prefixLift 6898956
  have htrace : WordTrace (prefixWord ++ tailWord_6898956) baseStart_6898956 baseEnd_6898956 := by
    simpa [prefixWord, tailWord_6898956, baseEnd_6898956] using wordTrace_append hprefix tailTrace_6898956
  have hstable : (prefixWord ++ tailWord_6898956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898956).length < 2 ^ (prefixWord ++ tailWord_6898956).sum := by decide
  have hdescent : baseEnd_6898956 < baseStart_6898956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898970 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3]
def baseStart_6898970 : Nat := 118140960795 + 6898970 * 2 ^ 59
def prefixEnd_6898970 : Nat := 4983230072969 + 3 ^ 40 * 6898970 * 2
def baseEnd_6898970 : Nat := 3542487630948977981847221

theorem tailTrace_6898970 : CollatzResearch.WordTrace tailWord_6898970 prefixEnd_6898970 3542487630948977981847221 := by
  unfold tailWord_6898970
  simp only [CollatzResearch.WordTrace]
  refine ⟨62906526954054353778953591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167750738544144943410542909 62906526954054353778953591)
  ·
    refine ⟨94359790431081530668430387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62906526954054353778953591 94359790431081530668430387)
    ·
      refine ⟨141539685646622296002645581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94359790431081530668430387 141539685646622296002645581)
      ·
        refine ⟨53077382117483361000992093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141539685646622296002645581 53077382117483361000992093)
        ·
          refine ⟨19904018294056260375372035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53077382117483361000992093 19904018294056260375372035)
          ·
            refine ⟨29856027441084390563058053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904018294056260375372035 29856027441084390563058053)
            ·
              refine ⟨5598005145203323230573385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29856027441084390563058053 5598005145203323230573385)
              ·
                refine ⟨4198503858902492422930039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598005145203323230573385 4198503858902492422930039)
                ·
                  refine ⟨6297755788353738634395059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198503858902492422930039 6297755788353738634395059)
                  ·
                    refine ⟨9446633682530607951592589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297755788353738634395059 9446633682530607951592589)
                    ·
                      refine ⟨3542487630948977981847221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446633682530607951592589 3542487630948977981847221)
                      ·
                        rfl

theorem cell23_6898970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_6898970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898970 prefixEnd_6898970 := by exact prefixLift 6898970
  have htrace : WordTrace (prefixWord ++ tailWord_6898970) baseStart_6898970 baseEnd_6898970 := by
    simpa [prefixWord, tailWord_6898970, baseEnd_6898970] using wordTrace_append hprefix tailTrace_6898970
  have hstable : (prefixWord ++ tailWord_6898970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898970).length < 2 ^ (prefixWord ++ tailWord_6898970).sum := by decide
  have hdescent : baseEnd_6898970 < baseStart_6898970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898972 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6898972 : Nat := 118140960795 + 6898972 * 2 ^ 59
def prefixEnd_6898972 : Nat := 4983230072969 + 3 ^ 40 * 6898972 * 2
def baseEnd_6898972 : Nat := 3542488657910286974022211

theorem tailTrace_6898972 : CollatzResearch.WordTrace tailWord_6898972 prefixEnd_6898972 3542488657910286974022211 := by
  unfold tailWord_6898972
  simp only [CollatzResearch.WordTrace]
  refine ⟨125813090381105084728693585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167750787174806779638258113 125813090381105084728693585)
  ·
    refine ⟨94359817785828813546520189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125813090381105084728693585 94359817785828813546520189)
    ·
      refine ⟨35384931669685805079945071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94359817785828813546520189 35384931669685805079945071)
      ·
        refine ⟨53077397504528707619917607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35384931669685805079945071 53077397504528707619917607)
        ·
          refine ⟨79616096256793061429876411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53077397504528707619917607 79616096256793061429876411)
          ·
            refine ⟨119424144385189592144814617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79616096256793061429876411 119424144385189592144814617)
            ·
              refine ⟨89568108288892194108610963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119424144385189592144814617 89568108288892194108610963)
              ·
                refine ⟨134352162433338291162916445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89568108288892194108610963 134352162433338291162916445)
                ·
                  refine ⟨50382060912501859186093667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134352162433338291162916445 50382060912501859186093667)
                  ·
                    refine ⟨75573091368752788779140501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50382060912501859186093667 75573091368752788779140501)
                    ·
                      refine ⟨3542488657910286974022211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75573091368752788779140501 3542488657910286974022211)
                      ·
                        rfl

theorem cell23_6898972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6898972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898972 prefixEnd_6898972 := by exact prefixLift 6898972
  have htrace : WordTrace (prefixWord ++ tailWord_6898972) baseStart_6898972 baseEnd_6898972 := by
    simpa [prefixWord, tailWord_6898972, baseEnd_6898972] using wordTrace_append hprefix tailTrace_6898972
  have hstable : (prefixWord ++ tailWord_6898972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898972).length < 2 ^ (prefixWord ++ tailWord_6898972).sum := by decide
  have hdescent : baseEnd_6898972 < baseStart_6898972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898979 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3]
def baseStart_6898979 : Nat := 118140960795 + 6898979 * 2 ^ 59
def prefixEnd_6898979 : Nat := 4983230072969 + 3 ^ 40 * 6898979 * 2
def baseEnd_6898979 : Nat := 3542492252274868446634679

theorem tailTrace_6898979 : CollatzResearch.WordTrace tailWord_6898979 prefixEnd_6898979 3542492252274868446634679 := by
  unfold tailWord_6898979
  simp only [CollatzResearch.WordTrace]
  refine ⟨251626436073184809652891991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167750957382123206435261327 251626436073184809652891991)
  ·
    refine ⟨377439654109777214479337987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251626436073184809652891991 377439654109777214479337987)
    ·
      refine ⟨566159481164665821719006981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377439654109777214479337987 566159481164665821719006981)
      ·
        refine ⟨106154902718374841572313809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566159481164665821719006981 106154902718374841572313809)
        ·
          refine ⟨79616177038781131179235357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106154902718374841572313809 79616177038781131179235357)
          ·
            refine ⟨29856066389542924192213259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79616177038781131179235357 29856066389542924192213259)
            ·
              refine ⟨44784099584314386288319889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29856066389542924192213259 44784099584314386288319889)
              ·
                refine ⟨33588074688235789716239917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44784099584314386288319889 33588074688235789716239917)
                ·
                  refine ⟨12595528008088421143589969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33588074688235789716239917 12595528008088421143589969)
                  ·
                    refine ⟨9446646006066315857692477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12595528008088421143589969 9446646006066315857692477)
                    ·
                      refine ⟨3542492252274868446634679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446646006066315857692477 3542492252274868446634679)
                      ·
                        rfl

theorem cell23_6898979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_6898979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898979 prefixEnd_6898979 := by exact prefixLift 6898979
  have htrace : WordTrace (prefixWord ++ tailWord_6898979) baseStart_6898979 baseEnd_6898979 := by
    simpa [prefixWord, tailWord_6898979, baseEnd_6898979] using wordTrace_append hprefix tailTrace_6898979
  have hstable : (prefixWord ++ tailWord_6898979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898979).length < 2 ^ (prefixWord ++ tailWord_6898979).sum := by decide
  have hdescent : baseEnd_6898979 < baseStart_6898979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898986 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_6898986 : Nat := 118140960795 + 6898986 * 2 ^ 59
def prefixEnd_6898986 : Nat := 4983230072969 + 3 ^ 40 * 6898986 * 2
def baseEnd_6898986 : Nat := 1180831948879816639749049

theorem tailTrace_6898986 : CollatzResearch.WordTrace tailWord_6898986 prefixEnd_6898986 1180831948879816639749049 := by
  unfold tailWord_6898986
  simp only [CollatzResearch.WordTrace]
  refine ⟨62906672846039862462099203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167751127589439633232264541 62906672846039862462099203)
  ·
    refine ⟨94360009269059793693148805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62906672846039862462099203 94360009269059793693148805)
    ·
      refine ⟨17692501737948711317465401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94360009269059793693148805 17692501737948711317465401)
      ·
        refine ⟨13269376303461533488099051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17692501737948711317465401 13269376303461533488099051)
        ·
          refine ⟨19904064455192300232148577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269376303461533488099051 19904064455192300232148577)
          ·
            refine ⟨14928048341394225174111433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19904064455192300232148577 14928048341394225174111433)
            ·
              refine ⟨11196036256045668880583575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14928048341394225174111433 11196036256045668880583575)
              ·
                refine ⟨16794054384068503320875363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196036256045668880583575 16794054384068503320875363)
                ·
                  refine ⟨25191081576102754981313045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16794054384068503320875363 25191081576102754981313045)
                  ·
                    refine ⟨1180831948879816639749049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25191081576102754981313045 1180831948879816639749049)
                    ·
                      rfl

theorem cell23_6898986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_6898986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898986 prefixEnd_6898986 := by exact prefixLift 6898986
  have htrace : WordTrace (prefixWord ++ tailWord_6898986) baseStart_6898986 baseEnd_6898986 := by
    simpa [prefixWord, tailWord_6898986, baseEnd_6898986] using wordTrace_append hprefix tailTrace_6898986
  have hstable : (prefixWord ++ tailWord_6898986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898986).length < 2 ^ (prefixWord ++ tailWord_6898986).sum := by decide
  have hdescent : baseEnd_6898986 < baseStart_6898986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898993 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_6898993 : Nat := 118140960795 + 6898993 * 2 ^ 59
def prefixEnd_6898993 : Nat := 4983230072969 + 3 ^ 40 * 6898993 * 2
def baseEnd_6898993 : Nat := 3542499441004031391859615

theorem tailTrace_6898993 : CollatzResearch.WordTrace tailWord_6898993 prefixEnd_6898993 3542499441004031391859615 := by
  unfold tailWord_6898993
  simp only [CollatzResearch.WordTrace]
  refine ⟨251626946695134090043901633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167751297796756060029267755 251626946695134090043901633)
  ·
    refine ⟨188720210021350567532926225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251626946695134090043901633 188720210021350567532926225)
    ·
      refine ⟨141540157516012925649694669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188720210021350567532926225 141540157516012925649694669)
      ·
        refine ⟨53077559068504847118635501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141540157516012925649694669 53077559068504847118635501)
        ·
          refine ⟨19904084650689317669488313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53077559068504847118635501 19904084650689317669488313)
          ·
            refine ⟨14928063488016988252116235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19904084650689317669488313 14928063488016988252116235)
            ·
              refine ⟨22392095232025482378174353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14928063488016988252116235 22392095232025482378174353)
              ·
                refine ⟨16794071424019111783630765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22392095232025482378174353 16794071424019111783630765)
                ·
                  refine ⟨6297776784007166918861537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16794071424019111783630765 6297776784007166918861537)
                  ·
                    refine ⟨4723332588005375189146153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297776784007166918861537 4723332588005375189146153)
                    ·
                      refine ⟨3542499441004031391859615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723332588005375189146153 3542499441004031391859615)
                      ·
                        rfl

theorem cell23_6898993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_6898993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898993 prefixEnd_6898993 := by exact prefixLift 6898993
  have htrace : WordTrace (prefixWord ++ tailWord_6898993) baseStart_6898993 baseEnd_6898993 := by
    simpa [prefixWord, tailWord_6898993, baseEnd_6898993] using wordTrace_append hprefix tailTrace_6898993
  have hstable : (prefixWord ++ tailWord_6898993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898993).length < 2 ^ (prefixWord ++ tailWord_6898993).sum := by decide
  have hdescent : baseEnd_6898993 < baseStart_6898993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898996 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_6898996 : Nat := 118140960795 + 6898996 * 2 ^ 59
def prefixEnd_6898996 : Nat := 4983230072969 + 3 ^ 40 * 6898996 * 2
def baseEnd_6898996 : Nat := 3542500981445994880122101

theorem tailTrace_6898996 : CollatzResearch.WordTrace tailWord_6898996 prefixEnd_6898996 3542500981445994880122101 := by
  unfold tailWord_6898996
  simp only [CollatzResearch.WordTrace]
  refine ⟨125813528057061610778130421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167751370742748814370840561 125813528057061610778130421)
  ·
    refine ⟨11795018255349526010449727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125813528057061610778130421 11795018255349526010449727)
    ·
      refine ⟨17692527383024289015674591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795018255349526010449727 17692527383024289015674591)
      ·
        refine ⟨26538791074536433523511887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17692527383024289015674591 26538791074536433523511887)
        ·
          refine ⟨39808186611804650285267831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26538791074536433523511887 39808186611804650285267831)
          ·
            refine ⟨59712279917706975427901747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39808186611804650285267831 59712279917706975427901747)
            ·
              refine ⟨89568419876560463141852621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59712279917706975427901747 89568419876560463141852621)
              ·
                refine ⟨33588157453710173678194733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89568419876560463141852621 33588157453710173678194733)
                ·
                  refine ⟨12595559045141315129323025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33588157453710173678194733 12595559045141315129323025)
                  ·
                    refine ⟨9446669283855986346992269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12595559045141315129323025 9446669283855986346992269)
                    ·
                      refine ⟨3542500981445994880122101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446669283855986346992269 3542500981445994880122101)
                      ·
                        rfl

theorem cell23_6898996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_6898996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898996 prefixEnd_6898996 := by exact prefixLift 6898996
  have htrace : WordTrace (prefixWord ++ tailWord_6898996) baseStart_6898996 baseEnd_6898996 := by
    simpa [prefixWord, tailWord_6898996, baseEnd_6898996] using wordTrace_append hprefix tailTrace_6898996
  have hstable : (prefixWord ++ tailWord_6898996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898996).length < 2 ^ (prefixWord ++ tailWord_6898996).sum := by decide
  have hdescent : baseEnd_6898996 < baseStart_6898996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899037 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6899037 : Nat := 118140960795 + 6899037 * 2 ^ 59
def prefixEnd_6899037 : Nat := 4983230072969 + 3 ^ 40 * 6899037 * 2
def baseEnd_6899037 : Nat := 1180840678050943073236471

theorem tailTrace_6899037 : CollatzResearch.WordTrace tailWord_6899037 prefixEnd_6899037 1180840678050943073236471 := by
  unfold tailWord_6899037
  simp only [CollatzResearch.WordTrace]
  refine ⟨251628551506974685558503365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167752367671316457039002243 251628551506974685558503365)
  ·
    refine ⟨47180353407557753542219381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251628551506974685558503365 47180353407557753542219381)
    ·
      refine ⟨4423158131958539394583067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47180353407557753542219381 4423158131958539394583067)
      ·
        refine ⟨6634737197937809091874601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423158131958539394583067 6634737197937809091874601)
        ·
          refine ⟨4976052898453356818905951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6634737197937809091874601 4976052898453356818905951)
          ·
            refine ⟨7464079347680035228358927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976052898453356818905951 7464079347680035228358927)
            ·
              refine ⟨11196119021520052842538391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464079347680035228358927 11196119021520052842538391)
              ·
                refine ⟨16794178532280079263807587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196119021520052842538391 16794178532280079263807587)
                ·
                  refine ⟨25191267798420118895711381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16794178532280079263807587 25191267798420118895711381)
                  ·
                    refine ⟨1180840678050943073236471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25191267798420118895711381 1180840678050943073236471)
                    ·
                      rfl

theorem cell23_6899037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6899037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899037 prefixEnd_6899037 := by exact prefixLift 6899037
  have htrace : WordTrace (prefixWord ++ tailWord_6899037) baseStart_6899037 baseEnd_6899037 := by
    simpa [prefixWord, tailWord_6899037, baseEnd_6899037] using wordTrace_append hprefix tailTrace_6899037
  have hstable : (prefixWord ++ tailWord_6899037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899037).length < 2 ^ (prefixWord ++ tailWord_6899037).sum := by decide
  have hdescent : baseEnd_6899037 < baseStart_6899037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899053 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_6899053 : Nat := 118140960795 + 6899053 * 2 ^ 59
def prefixEnd_6899053 : Nat := 4983230072969 + 3 ^ 40 * 6899053 * 2
def baseEnd_6899053 : Nat := 3542530249843301157109339

theorem tailTrace_6899053 : CollatzResearch.WordTrace tailWord_6899053 prefixEnd_6899053 3542530249843301157109339 := by
  unfold tailWord_6899053
  simp only [CollatzResearch.WordTrace]
  refine ⟨251629135074916720291085813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167752756716611146860723875 251629135074916720291085813)
  ·
    refine ⟨23590231413273442527289295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251629135074916720291085813 23590231413273442527289295)
    ·
      refine ⟨35385347119910163790933943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23590231413273442527289295 35385347119910163790933943)
      ·
        refine ⟨53078020679865245686400915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35385347119910163790933943 53078020679865245686400915)
        ·
          refine ⟨79617031019797868529601373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53078020679865245686400915 79617031019797868529601373)
          ·
            refine ⟨29856386632424200698600515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79617031019797868529601373 29856386632424200698600515)
            ·
              refine ⟨44784579948636301047900773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29856386632424200698600515 44784579948636301047900773)
              ·
                refine ⟨8397108740369306446481395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44784579948636301047900773 8397108740369306446481395)
                ·
                  refine ⟨12595663110553959669722093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8397108740369306446481395 12595663110553959669722093)
                  ·
                    refine ⟨4723373666457734876145785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12595663110553959669722093 4723373666457734876145785)
                    ·
                      refine ⟨3542530249843301157109339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723373666457734876145785 3542530249843301157109339)
                      ·
                        rfl

theorem cell23_6899053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_6899053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899053 prefixEnd_6899053 := by exact prefixLift 6899053
  have htrace : WordTrace (prefixWord ++ tailWord_6899053) baseStart_6899053 baseEnd_6899053 := by
    simpa [prefixWord, tailWord_6899053, baseEnd_6899053] using wordTrace_append hprefix tailTrace_6899053
  have hstable : (prefixWord ++ tailWord_6899053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899053).length < 2 ^ (prefixWord ++ tailWord_6899053).sum := by decide
  have hdescent : baseEnd_6899053 < baseStart_6899053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899069 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_6899069 : Nat := 118140960795 + 6899069 * 2 ^ 59
def prefixEnd_6899069 : Nat := 4983230072969 + 3 ^ 40 * 6899069 * 2
def baseEnd_6899069 : Nat := 3542538465533773094509265

theorem tailTrace_6899069 : CollatzResearch.WordTrace tailWord_6899069 prefixEnd_6899069 3542538465533773094509265 := by
  unfold tailWord_6899069
  simp only [CollatzResearch.WordTrace]
  refine ⟨251629718642858755023668261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167753145761905836682445507 251629718642858755023668261)
  ·
    refine ⟨47180572245536016566937799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251629718642858755023668261 47180572245536016566937799)
    ·
      refine ⟨70770858368304024850406699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47180572245536016566937799 70770858368304024850406699)
      ·
        refine ⟨106156287552456037275610049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70770858368304024850406699 106156287552456037275610049)
        ·
          refine ⟨79617215664342027956707537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106156287552456037275610049 79617215664342027956707537)
          ·
            refine ⟨59712911748256520967530653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79617215664342027956707537 59712911748256520967530653)
            ·
              refine ⟨22392341905596195362823995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59712911748256520967530653 22392341905596195362823995)
              ·
                refine ⟨33588512858394293044235993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22392341905596195362823995 33588512858394293044235993)
                ·
                  refine ⟨25191384643795719783176995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33588512858394293044235993 25191384643795719783176995)
                  ·
                    refine ⟨37787076965693579674765493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25191384643795719783176995 37787076965693579674765493)
                    ·
                      refine ⟨3542538465533773094509265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37787076965693579674765493 3542538465533773094509265)
                      ·
                        rfl

theorem cell23_6899069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_6899069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899069 prefixEnd_6899069 := by exact prefixLift 6899069
  have htrace : WordTrace (prefixWord ++ tailWord_6899069) baseStart_6899069 baseEnd_6899069 := by
    simpa [prefixWord, tailWord_6899069, baseEnd_6899069] using wordTrace_append hprefix tailTrace_6899069
  have hstable : (prefixWord ++ tailWord_6899069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899069).length < 2 ^ (prefixWord ++ tailWord_6899069).sum := by decide
  have hdescent : baseEnd_6899069 < baseStart_6899069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899072 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 9]
def baseStart_6899072 : Nat := 118140960795 + 6899072 * 2 ^ 59
def prefixEnd_6899072 : Nat := 4983230072969 + 3 ^ 40 * 6899072 * 2
def baseEnd_6899072 : Nat := 393615556219526286974639

theorem tailTrace_6899072 : CollatzResearch.WordTrace tailWord_6899072 prefixEnd_6899072 393615556219526286974639 := by
  unfold tailWord_6899072
  simp only [CollatzResearch.WordTrace]
  refine ⟨125814914030923943268013735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167753218707898591024018313 125814914030923943268013735)
  ·
    refine ⟨188722371046385914902020603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125814914030923943268013735 188722371046385914902020603)
    ·
      refine ⟨283083556569578872353030905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188722371046385914902020603 283083556569578872353030905)
      ·
        refine ⟨212312667427184154264773179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283083556569578872353030905 212312667427184154264773179)
        ·
          refine ⟨318469001140776231397159769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212312667427184154264773179 318469001140776231397159769)
          ·
            refine ⟨238851750855582173547869827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318469001140776231397159769 238851750855582173547869827)
            ·
              refine ⟨358277626283373260321804741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238851750855582173547869827 358277626283373260321804741)
              ·
                refine ⟨67177054928132486310338389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358277626283373260321804741 67177054928132486310338389)
                ·
                  refine ⟨393615556219526286974639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67177054928132486310338389 393615556219526286974639)
                  ·
                    rfl

theorem cell23_6899072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_6899072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899072 prefixEnd_6899072 := by exact prefixLift 6899072
  have htrace : WordTrace (prefixWord ++ tailWord_6899072) baseStart_6899072 baseEnd_6899072 := by
    simpa [prefixWord, tailWord_6899072, baseEnd_6899072] using wordTrace_append hprefix tailTrace_6899072
  have hstable : (prefixWord ++ tailWord_6899072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899072).length < 2 ^ (prefixWord ++ tailWord_6899072).sum := by decide
  have hdescent : baseEnd_6899072 < baseStart_6899072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899083 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 2, 2, 2]
def baseStart_6899083 : Nat := 118140960795 + 6899083 * 2 ^ 59
def prefixEnd_6899083 : Nat := 4983230072969 + 3 ^ 40 * 6899083 * 2
def baseEnd_6899083 : Nat := 3542545654262936039734201

theorem tailTrace_6899083 : CollatzResearch.WordTrace tailWord_6899083 prefixEnd_6899083 3542545654262936039734201 := by
  unfold tailWord_6899083
  simp only [CollatzResearch.WordTrace]
  refine ⟨251630229264808035414677903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167753486176538690276451935 251630229264808035414677903)
  ·
    refine ⟨377445343897212053122016855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251630229264808035414677903 377445343897212053122016855)
    ·
      refine ⟨566168015845818079683025283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377445343897212053122016855 566168015845818079683025283)
      ·
        refine ⟨849252023768727119524537925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566168015845818079683025283 849252023768727119524537925)
        ·
          refine ⟨159234754456636334910850861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 849252023768727119524537925 159234754456636334910850861)
          ·
            refine ⟨59713032921238625591569073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159234754456636334910850861 59713032921238625591569073)
            ·
              refine ⟨44784774690928969193676805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59713032921238625591569073 44784774690928969193676805)
              ·
                refine ⟨8397145254549181723814401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44784774690928969193676805 8397145254549181723814401)
                ·
                  refine ⟨6297858940911886292860801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8397145254549181723814401 6297858940911886292860801)
                  ·
                    refine ⟨4723394205683914719645601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297858940911886292860801 4723394205683914719645601)
                    ·
                      refine ⟨3542545654262936039734201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723394205683914719645601 3542545654262936039734201)
                      ·
                        rfl

theorem cell23_6899083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2, 2].length) (baseStart_6899083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899083 prefixEnd_6899083 := by exact prefixLift 6899083
  have htrace : WordTrace (prefixWord ++ tailWord_6899083) baseStart_6899083 baseEnd_6899083 := by
    simpa [prefixWord, tailWord_6899083, baseEnd_6899083] using wordTrace_append hprefix tailTrace_6899083
  have hstable : (prefixWord ++ tailWord_6899083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899083).length < 2 ^ (prefixWord ++ tailWord_6899083).sum := by decide
  have hdescent : baseEnd_6899083 < baseStart_6899083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899140 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 5]
def baseStart_6899140 : Nat := 118140960795 + 6899140 * 2 ^ 59
def prefixEnd_6899140 : Nat := 4983230072969 + 3 ^ 40 * 6899140 * 2
def baseEnd_6899140 : Nat := 393619435851138035191271

theorem tailTrace_6899140 : CollatzResearch.WordTrace tailWord_6899140 prefixEnd_6899140 393619435851138035191271 := by
  unfold tailWord_6899140
  simp only [CollatzResearch.WordTrace]
  refine ⟨125816154112800767074751437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167754872150401022766335249 125816154112800767074751437)
  ·
    refine ⟨47181057792300287653031789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125816154112800767074751437 47181057792300287653031789)
    ·
      refine ⟨17692896672112607869886921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47181057792300287653031789 17692896672112607869886921)
      ·
        refine ⟨13269672504084455902415191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17692896672112607869886921 13269672504084455902415191)
        ·
          refine ⟨19904508756126683853622787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269672504084455902415191 19904508756126683853622787)
          ·
            refine ⟨29856763134190025780434181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904508756126683853622787 29856763134190025780434181)
            ·
              refine ⟨5598143087660629833831409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29856763134190025780434181 5598143087660629833831409)
              ·
                refine ⟨4198607315745472375373557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598143087660629833831409 4198607315745472375373557)
                ·
                  refine ⟨393619435851138035191271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198607315745472375373557 393619435851138035191271)
                  ·
                    rfl

theorem cell23_6899140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_6899140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899140 prefixEnd_6899140 := by exact prefixLift 6899140
  have htrace : WordTrace (prefixWord ++ tailWord_6899140) baseStart_6899140 baseEnd_6899140 := by
    simpa [prefixWord, tailWord_6899140, baseEnd_6899140] using wordTrace_append hprefix tailTrace_6899140
  have hstable : (prefixWord ++ tailWord_6899140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899140).length < 2 ^ (prefixWord ++ tailWord_6899140).sum := by decide
  have hdescent : baseEnd_6899140 < baseStart_6899140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899173 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6899173 : Nat := 118140960795 + 6899173 * 2 ^ 59
def prefixEnd_6899173 : Nat := 4983230072969 + 3 ^ 40 * 6899173 * 2
def baseEnd_6899173 : Nat := 3542591867521840687608787

theorem tailTrace_6899173 : CollatzResearch.WordTrace tailWord_6899173 prefixEnd_6899173 3542591867521840687608787 := by
  unfold tailWord_6899173
  simp only [CollatzResearch.WordTrace]
  refine ⟨251633511834481980785454173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167755674556321320523636115 251633511834481980785454173)
  ·
    refine ⟨94362566937930742794545315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251633511834481980785454173 94362566937930742794545315)
    ·
      refine ⟨141543850406896114191817973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94362566937930742794545315 141543850406896114191817973)
      ·
        refine ⟨13269735975646510705482935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141543850406896114191817973 13269735975646510705482935)
        ·
          refine ⟨19904603963469766058224403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269735975646510705482935 19904603963469766058224403)
          ·
            refine ⟨29856905945204649087336605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904603963469766058224403 29856905945204649087336605)
            ·
              refine ⟨11196339729451743407751227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29856905945204649087336605 11196339729451743407751227)
              ·
                refine ⟨16794509594177615111626841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196339729451743407751227 16794509594177615111626841)
                ·
                  refine ⟨12595882195633211333720131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16794509594177615111626841 12595882195633211333720131)
                  ·
                    refine ⟨18893823293449817000580197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12595882195633211333720131 18893823293449817000580197)
                    ·
                      refine ⟨3542591867521840687608787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18893823293449817000580197 3542591867521840687608787)
                      ·
                        rfl

theorem cell23_6899173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6899173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899173 prefixEnd_6899173 := by exact prefixLift 6899173
  have htrace : WordTrace (prefixWord ++ tailWord_6899173) baseStart_6899173 baseEnd_6899173 := by
    simpa [prefixWord, tailWord_6899173, baseEnd_6899173] using wordTrace_append hprefix tailTrace_6899173
  have hstable : (prefixWord ++ tailWord_6899173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899173).length < 2 ^ (prefixWord ++ tailWord_6899173).sum := by decide
  have hdescent : baseEnd_6899173 < baseStart_6899173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899176 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6899176 : Nat := 118140960795 + 6899176 * 2 ^ 59
def prefixEnd_6899176 : Nat := 4983230072969 + 3 ^ 40 * 6899176 * 2
def baseEnd_6899176 : Nat := 3542593407963804175871273

theorem tailTrace_6899176 : CollatzResearch.WordTrace tailWord_6899176 prefixEnd_6899176 3542593407963804175871273 := by
  unfold tailWord_6899176
  simp only [CollatzResearch.WordTrace]
  refine ⟨125816810626735556148906691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167755747502314074865208921 125816810626735556148906691)
  ·
    refine ⟨188725215940103334223360037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125816810626735556148906691 188725215940103334223360037)
    ·
      refine ⟨35385977988769375166880007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188725215940103334223360037 35385977988769375166880007)
      ·
        refine ⟨53078966983154062750320011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35385977988769375166880007 53078966983154062750320011)
        ·
          refine ⟨79618450474731094125480017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53078966983154062750320011 79618450474731094125480017)
          ·
            refine ⟨59713837856048320594110013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79618450474731094125480017 59713837856048320594110013)
            ·
              refine ⟨22392689196018120222791255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59713837856048320594110013 22392689196018120222791255)
              ·
                refine ⟨33589033794027180334186883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22392689196018120222791255 33589033794027180334186883)
                ·
                  refine ⟨50383550691040770501280325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33589033794027180334186883 50383550691040770501280325)
                  ·
                    refine ⟨9446915754570144468990061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50383550691040770501280325 9446915754570144468990061)
                    ·
                      refine ⟨3542593407963804175871273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9446915754570144468990061 3542593407963804175871273)
                      ·
                        rfl

theorem cell23_6899176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6899176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899176 prefixEnd_6899176 := by exact prefixLift 6899176
  have htrace : WordTrace (prefixWord ++ tailWord_6899176) baseStart_6899176 baseEnd_6899176 := by
    simpa [prefixWord, tailWord_6899176, baseEnd_6899176] using wordTrace_append hprefix tailTrace_6899176
  have hstable : (prefixWord ++ tailWord_6899176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899176).length < 2 ^ (prefixWord ++ tailWord_6899176).sum := by decide
  have hdescent : baseEnd_6899176 < baseStart_6899176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899183 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 1, 4]
def baseStart_6899183 : Nat := 118140960795 + 6899183 * 2 ^ 59
def prefixEnd_6899183 : Nat := 4983230072969 + 3 ^ 40 * 6899183 * 2
def baseEnd_6899183 : Nat := 1180865667442795216161247

theorem tailTrace_6899183 : CollatzResearch.WordTrace tailWord_6899183 prefixEnd_6899183 1180865667442795216161247 := by
  unfold tailWord_6899183
  simp only [CollatzResearch.WordTrace]
  refine ⟨251633876564445752493318203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167755917709630501662212135 251633876564445752493318203)
  ·
    refine ⟨377450814846668628739977305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251633876564445752493318203 377450814846668628739977305)
    ·
      refine ⟨283088111135001471554982979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377450814846668628739977305 283088111135001471554982979)
      ·
        refine ⟨424632166702502207332474469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283088111135001471554982979 424632166702502207332474469)
        ·
          refine ⟨79618531256719163874838963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424632166702502207332474469 79618531256719163874838963)
          ·
            refine ⟨119427796885078745812258445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79618531256719163874838963 119427796885078745812258445)
            ·
              refine ⟨44785423831904529679596917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119427796885078745812258445 44785423831904529679596917)
              ·
                refine ⟨4198633484241049657462211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44785423831904529679596917 4198633484241049657462211)
                ·
                  refine ⟨6297950226361574486193317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198633484241049657462211 6297950226361574486193317)
                  ·
                    refine ⟨1180865667442795216161247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297950226361574486193317 1180865667442795216161247)
                    ·
                      rfl

theorem cell23_6899183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 4].length) (baseStart_6899183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899183 prefixEnd_6899183 := by exact prefixLift 6899183
  have htrace : WordTrace (prefixWord ++ tailWord_6899183) baseStart_6899183 baseEnd_6899183 := by
    simpa [prefixWord, tailWord_6899183, baseEnd_6899183] using wordTrace_append hprefix tailTrace_6899183
  have hstable : (prefixWord ++ tailWord_6899183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899183).length < 2 ^ (prefixWord ++ tailWord_6899183).sum := by decide
  have hdescent : baseEnd_6899183 < baseStart_6899183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899186 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6899186 : Nat := 118140960795 + 6899186 * 2 ^ 59
def prefixEnd_6899186 : Nat := 4983230072969 + 3 ^ 40 * 6899186 * 2
def baseEnd_6899186 : Nat := 3542598542770349136746227

theorem tailTrace_6899186 : CollatzResearch.WordTrace tailWord_6899186 prefixEnd_6899186 3542598542770349136746227 := by
  unfold tailWord_6899186
  simp only [CollatzResearch.WordTrace]
  refine ⟨62908496495858721001419353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167755990655623256003784941 62908496495858721001419353)
  ·
    refine ⟨47181372371894040751064515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62908496495858721001419353 47181372371894040751064515)
    ·
      refine ⟨70772058557841061126596773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47181372371894040751064515 70772058557841061126596773)
      ·
        refine ⟨13269760979595198961236895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70772058557841061126596773 13269760979595198961236895)
        ·
          refine ⟨19904641469392798441855343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269760979595198961236895 19904641469392798441855343)
          ·
            refine ⟨29856962204089197662783015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904641469392798441855343 29856962204089197662783015)
            ·
              refine ⟨44785443306133796494174523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29856962204089197662783015 44785443306133796494174523)
              ·
                refine ⟨67178164959200694741261785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44785443306133796494174523 67178164959200694741261785)
                ·
                  refine ⟨50383623719400521055946339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67178164959200694741261785 50383623719400521055946339)
                  ·
                    refine ⟨75575435579100781583919509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50383623719400521055946339 75575435579100781583919509)
                    ·
                      refine ⟨3542598542770349136746227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75575435579100781583919509 3542598542770349136746227)
                      ·
                        rfl

theorem cell23_6899186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6899186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899186 prefixEnd_6899186 := by exact prefixLift 6899186
  have htrace : WordTrace (prefixWord ++ tailWord_6899186) baseStart_6899186 baseEnd_6899186 := by
    simpa [prefixWord, tailWord_6899186, baseEnd_6899186] using wordTrace_append hprefix tailTrace_6899186
  have hstable : (prefixWord ++ tailWord_6899186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899186).length < 2 ^ (prefixWord ++ tailWord_6899186).sum := by decide
  have hdescent : baseEnd_6899186 < baseStart_6899186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899196 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 6]
def baseStart_6899196 : Nat := 118140960795 + 6899196 * 2 ^ 59
def prefixEnd_6899196 : Nat := 4983230072969 + 3 ^ 40 * 6899196 * 2
def baseEnd_6899196 : Nat := 393622630841877121957909

theorem tailTrace_6899196 : CollatzResearch.WordTrace tailWord_6899196 prefixEnd_6899196 393622630841877121957909 := by
  unfold tailWord_6899196
  simp only [CollatzResearch.WordTrace]
  refine ⟨125817175356699327856770721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167756233808932437142360961 125817175356699327856770721)
  ·
    refine ⟨94362881517524495892578041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125817175356699327856770721 94362881517524495892578041)
    ·
      refine ⟨70772161138143371919433531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94362881517524495892578041 70772161138143371919433531)
      ·
        refine ⟨106158241707215057879150297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70772161138143371919433531 106158241707215057879150297)
        ·
          refine ⟨79618681280411293409362723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106158241707215057879150297 79618681280411293409362723)
          ·
            refine ⟨119428021920616940114044085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79618681280411293409362723 119428021920616940114044085)
            ·
              refine ⟨11196377055057838135691633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119428021920616940114044085 11196377055057838135691633)
              ·
                refine ⟨8397282791293378601768725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11196377055057838135691633 8397282791293378601768725)
                ·
                  refine ⟨393622630841877121957909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8397282791293378601768725 393622630841877121957909)
                  ·
                    rfl

theorem cell23_6899196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_6899196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899196 prefixEnd_6899196 := by exact prefixLift 6899196
  have htrace : WordTrace (prefixWord ++ tailWord_6899196) baseStart_6899196 baseEnd_6899196 := by
    simpa [prefixWord, tailWord_6899196, baseEnd_6899196] using wordTrace_append hprefix tailTrace_6899196
  have hstable : (prefixWord ++ tailWord_6899196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899196).length < 2 ^ (prefixWord ++ tailWord_6899196).sum := by decide
  have hdescent : baseEnd_6899196 < baseStart_6899196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899233 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6899233 : Nat := 118140960795 + 6899233 * 2 ^ 59
def prefixEnd_6899233 : Nat := 4983230072969 + 3 ^ 40 * 6899233 * 2
def baseEnd_6899233 : Nat := 3542622676361110452858511

theorem tailTrace_6899233 : CollatzResearch.WordTrace tailWord_6899233 prefixEnd_6899233 3542622676361110452858511 := by
  unfold tailWord_6899233
  simp only [CollatzResearch.WordTrace]
  refine ⟨251635700214264611032638353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167757133476176407355092235 251635700214264611032638353)
  ·
    refine ⟨188726775160698458274478765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251635700214264611032638353 188726775160698458274478765)
    ·
      refine ⟨70772540685261921852929537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188726775160698458274478765 70772540685261921852929537)
      ·
        refine ⟨53079405513946441389697153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70772540685261921852929537 53079405513946441389697153)
        ·
          refine ⟨39809554135459831042272865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53079405513946441389697153 39809554135459831042272865)
          ·
            refine ⟨29857165601594873281704649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39809554135459831042272865 29857165601594873281704649)
            ·
              refine ⟨22392874201196154961278487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29857165601594873281704649 22392874201196154961278487)
              ·
                refine ⟨33589311301794232441917731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22392874201196154961278487 33589311301794232441917731)
                ·
                  refine ⟨50383966952691348662876597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33589311301794232441917731 50383966952691348662876597)
                  ·
                    refine ⟨4723496901814813937144681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50383966952691348662876597 4723496901814813937144681)
                    ·
                      refine ⟨3542622676361110452858511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723496901814813937144681 3542622676361110452858511)
                      ·
                        rfl

theorem cell23_6899233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6899233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899233 prefixEnd_6899233 := by exact prefixLift 6899233
  have htrace : WordTrace (prefixWord ++ tailWord_6899233) baseStart_6899233 baseEnd_6899233 := by
    simpa [prefixWord, tailWord_6899233, baseEnd_6899233] using wordTrace_append hprefix tailTrace_6899233
  have hstable : (prefixWord ++ tailWord_6899233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899233).length < 2 ^ (prefixWord ++ tailWord_6899233).sum := by decide
  have hdescent : baseEnd_6899233 < baseStart_6899233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899276 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6899276 : Nat := 118140960795 + 6899276 * 2 ^ 59
def prefixEnd_6899276 : Nat := 4983230072969 + 3 ^ 40 * 6899276 * 2
def baseEnd_6899276 : Nat := 3542644756029253784620813

theorem tailTrace_6899276 : CollatzResearch.WordTrace tailWord_6899276 prefixEnd_6899276 3542644756029253784620813 := by
  unfold tailWord_6899276
  simp only [CollatzResearch.WordTrace]
  refine ⟨125818634276554414688226841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167758179035405886250969121 125818634276554414688226841)
  ·
    refine ⟨94363975707415811016170131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125818634276554414688226841 94363975707415811016170131)
    ·
      refine ⟨141545963561123716524255197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94363975707415811016170131 141545963561123716524255197)
      ·
        refine ⟨53079736335421393696595699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141545963561123716524255197 53079736335421393696595699)
        ·
          refine ⟨79619604503132090544893549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53079736335421393696595699 79619604503132090544893549)
          ·
            refine ⟨29857351688674533954335081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79619604503132090544893549 29857351688674533954335081)
            ·
              refine ⟨22393013766505900465751311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29857351688674533954335081 22393013766505900465751311)
              ·
                refine ⟨33589520649758850698626967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22393013766505900465751311 33589520649758850698626967)
                ·
                  refine ⟨50384280974638276047940451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33589520649758850698626967 50384280974638276047940451)
                  ·
                    refine ⟨75576421461957414071910677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50384280974638276047940451 75576421461957414071910677)
                    ·
                      refine ⟨3542644756029253784620813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75576421461957414071910677 3542644756029253784620813)
                      ·
                        rfl

theorem cell23_6899276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6899276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899276 prefixEnd_6899276 := by exact prefixLift 6899276
  have htrace : WordTrace (prefixWord ++ tailWord_6899276) baseStart_6899276 baseEnd_6899276 := by
    simpa [prefixWord, tailWord_6899276, baseEnd_6899276] using wordTrace_append hprefix tailTrace_6899276
  have hstable : (prefixWord ++ tailWord_6899276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899276).length < 2 ^ (prefixWord ++ tailWord_6899276).sum := by decide
  have hdescent : baseEnd_6899276 < baseStart_6899276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899277 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6899277 : Nat := 118140960795 + 6899277 * 2 ^ 59
def prefixEnd_6899277 : Nat := 4983230072969 + 3 ^ 40 * 6899277 * 2
def baseEnd_6899277 : Nat := 1180881756503302760236103

theorem tailTrace_6899277 : CollatzResearch.WordTrace tailWord_6899277 prefixEnd_6899277 1180881756503302760236103 := by
  unfold tailWord_6899277
  simp only [CollatzResearch.WordTrace]
  refine ⟨251637305026105206547240085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167758203350736804364826723 251637305026105206547240085)
  ·
    refine ⟨11795498673098681556901879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 251637305026105206547240085 11795498673098681556901879)
    ·
      refine ⟨17693248009648022335352819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795498673098681556901879 17693248009648022335352819)
      ·
        refine ⟨26539872014472033503029229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17693248009648022335352819 26539872014472033503029229)
        ·
          refine ⟨9952452005427012563635961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26539872014472033503029229 9952452005427012563635961)
          ·
            refine ⟨7464339004070259422726971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9952452005427012563635961 7464339004070259422726971)
            ·
              refine ⟨11196508506105389134090457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464339004070259422726971 11196508506105389134090457)
              ·
                refine ⟨8397381379579041850567843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11196508506105389134090457 8397381379579041850567843)
                ·
                  refine ⟨12596072069368562775851765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8397381379579041850567843 12596072069368562775851765)
                  ·
                    refine ⟨1180881756503302760236103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12596072069368562775851765 1180881756503302760236103)
                    ·
                      rfl

theorem cell23_6899277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6899277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899277 prefixEnd_6899277 := by exact prefixLift 6899277
  have htrace : WordTrace (prefixWord ++ tailWord_6899277) baseStart_6899277 baseEnd_6899277 := by
    simpa [prefixWord, tailWord_6899277, baseEnd_6899277] using wordTrace_append hprefix tailTrace_6899277
  have hstable : (prefixWord ++ tailWord_6899277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899277).length < 2 ^ (prefixWord ++ tailWord_6899277).sum := by decide
  have hdescent : baseEnd_6899277 < baseStart_6899277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899297 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_6899297 : Nat := 118140960795 + 6899297 * 2 ^ 59
def prefixEnd_6899297 : Nat := 4983230072969 + 3 ^ 40 * 6899297 * 2
def baseEnd_6899297 : Nat := 3542655539122998202458217

theorem tailTrace_6899297 : CollatzResearch.WordTrace tailWord_6899297 prefixEnd_6899297 3542655539122998202458217 := by
  unfold tailWord_6899297
  simp only [CollatzResearch.WordTrace]
  refine ⟨251638034486032749962968145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167758689657355166641978763 251638034486032749962968145)
  ·
    refine ⟨188728525864524562472226109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251638034486032749962968145 188728525864524562472226109)
    ·
      refine ⟨70773197199196710927084791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188728525864524562472226109 70773197199196710927084791)
      ·
        refine ⟨106159795798795066390627187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70773197199196710927084791 106159795798795066390627187)
        ·
          refine ⟨159239693698192599585940781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106159795798795066390627187 159239693698192599585940781)
          ·
            refine ⟨59714885136822224844727793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159239693698192599585940781 59714885136822224844727793)
            ·
              refine ⟨44786163852616668633545845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59714885136822224844727793 44786163852616668633545845)
              ·
                refine ⟨4198702861182812684394923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44786163852616668633545845 4198702861182812684394923)
                ·
                  refine ⟨6298054291774219026592385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198702861182812684394923 6298054291774219026592385)
                  ·
                    refine ⟨4723540718830664269944289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298054291774219026592385 4723540718830664269944289)
                    ·
                      refine ⟨3542655539122998202458217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723540718830664269944289 3542655539122998202458217)
                      ·
                        rfl

theorem cell23_6899297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_6899297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899297 prefixEnd_6899297 := by exact prefixLift 6899297
  have htrace : WordTrace (prefixWord ++ tailWord_6899297) baseStart_6899297 baseEnd_6899297 := by
    simpa [prefixWord, tailWord_6899297, baseEnd_6899297] using wordTrace_append hprefix tailTrace_6899297
  have hstable : (prefixWord ++ tailWord_6899297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899297).length < 2 ^ (prefixWord ++ tailWord_6899297).sum := by decide
  have hdescent : baseEnd_6899297 < baseStart_6899297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899313 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_6899313 : Nat := 118140960795 + 6899313 * 2 ^ 59
def prefixEnd_6899313 : Nat := 4983230072969 + 3 ^ 40 * 6899313 * 2
def baseEnd_6899313 : Nat := 3542663754813470139858143

theorem tailTrace_6899313 : CollatzResearch.WordTrace tailWord_6899313 prefixEnd_6899313 3542663754813470139858143 := by
  unfold tailWord_6899313
  simp only [CollatzResearch.WordTrace]
  refine ⟨251638618053974784695550593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167759078702649856463700395 251638618053974784695550593)
  ·
    refine ⟨188728963540481088521662945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251638618053974784695550593 188728963540481088521662945)
    ·
      refine ⟨141546722655360816391247209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188728963540481088521662945 141546722655360816391247209)
      ·
        refine ⟨106160041991520612293435407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141546722655360816391247209 106160041991520612293435407)
        ·
          refine ⟨159240062987280918440153111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106160041991520612293435407 159240062987280918440153111)
          ·
            refine ⟨238860094480921377660229667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159240062987280918440153111 238860094480921377660229667)
            ·
              refine ⟨358290141721382066490344501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238860094480921377660229667 358290141721382066490344501)
              ·
                refine ⟨33589700786379568733469797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 358290141721382066490344501 33589700786379568733469797)
                ·
                  refine ⟨6298068897446169137525587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33589700786379568733469797 6298068897446169137525587)
                  ·
                    refine ⟨9447103346169253706288381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6298068897446169137525587 9447103346169253706288381)
                    ·
                      refine ⟨3542663754813470139858143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9447103346169253706288381 3542663754813470139858143)
                      ·
                        rfl

theorem cell23_6899313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_6899313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899313 prefixEnd_6899313 := by exact prefixLift 6899313
  have htrace : WordTrace (prefixWord ++ tailWord_6899313) baseStart_6899313 baseEnd_6899313 := by
    simpa [prefixWord, tailWord_6899313, baseEnd_6899313] using wordTrace_append hprefix tailTrace_6899313
  have hstable : (prefixWord ++ tailWord_6899313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899313).length < 2 ^ (prefixWord ++ tailWord_6899313).sum := by decide
  have hdescent : baseEnd_6899313 < baseStart_6899313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899314 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_6899314 : Nat := 118140960795 + 6899314 * 2 ^ 59
def prefixEnd_6899314 : Nat := 4983230072969 + 3 ^ 40 * 6899314 * 2
def baseEnd_6899314 : Nat := 3542664268294124635945639

theorem tailTrace_6899314 : CollatzResearch.WordTrace tailWord_6899314 prefixEnd_6899314 3542664268294124635945639 := by
  unfold tailWord_6899314
  simp only [CollatzResearch.WordTrace]
  refine ⟨62909663631742790466584249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167759103017980774577557997 62909663631742790466584249)
  ·
    refine ⟨47182247723807092849938187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62909663631742790466584249 47182247723807092849938187)
    ·
      refine ⟨70773371585710639274907281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47182247723807092849938187 70773371585710639274907281)
      ·
        refine ⟨53080028689282979456180461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70773371585710639274907281 53080028689282979456180461)
        ·
          refine ⟨19905010758481117296067673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53080028689282979456180461 19905010758481117296067673)
          ·
            refine ⟨14928758068860837972050755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19905010758481117296067673 14928758068860837972050755)
            ·
              refine ⟨22393137103291256958076133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14928758068860837972050755 22393137103291256958076133)
              ·
                refine ⟨4198713206867110679639275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22393137103291256958076133 4198713206867110679639275)
                ·
                  refine ⟨6298069810300666019458913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198713206867110679639275 6298069810300666019458913)
                  ·
                    refine ⟨4723552357725499514594185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298069810300666019458913 4723552357725499514594185)
                    ·
                      refine ⟨3542664268294124635945639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723552357725499514594185 3542664268294124635945639)
                      ·
                        rfl

theorem cell23_6899314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_6899314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899314 prefixEnd_6899314 := by exact prefixLift 6899314
  have htrace : WordTrace (prefixWord ++ tailWord_6899314) baseStart_6899314 baseEnd_6899314 := by
    simpa [prefixWord, tailWord_6899314, baseEnd_6899314] using wordTrace_append hprefix tailTrace_6899314
  have hstable : (prefixWord ++ tailWord_6899314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899314).length < 2 ^ (prefixWord ++ tailWord_6899314).sum := by decide
  have hdescent : baseEnd_6899314 < baseStart_6899314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899323 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 5, 3, 2]
def baseStart_6899323 : Nat := 118140960795 + 6899323 * 2 ^ 59
def prefixEnd_6899323 : Nat := 4983230072969 + 3 ^ 40 * 6899323 * 2
def baseEnd_6899323 : Nat := 3542668889620015100733097

theorem tailTrace_6899323 : CollatzResearch.WordTrace tailWord_6899323 prefixEnd_6899323 3542668889620015100733097 := by
  unfold tailWord_6899323
  simp only [CollatzResearch.WordTrace]
  refine ⟨251638982783938556403414623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167759321855959037602276415 251638982783938556403414623)
  ·
    refine ⟨377458474175907834605121935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251638982783938556403414623 377458474175907834605121935)
    ·
      refine ⟨566187711263861751907682903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377458474175907834605121935 566187711263861751907682903)
      ·
        refine ⟨849281566895792627861524355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566187711263861751907682903 849281566895792627861524355)
        ·
          refine ⟨1273922350343688941792286533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849281566895792627861524355 1273922350343688941792286533)
          ·
            refine ⟨238860440689441676586053725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1273922350343688941792286533 238860440689441676586053725)
            ·
              refine ⟨89572665258540628719770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238860440689441676586053725 89572665258540628719770147)
              ·
                refine ⟨134358997887810943079655221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89572665258540628719770147 134358997887810943079655221)
                ·
                  refine ⟨12596156051982275913717677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134358997887810943079655221 12596156051982275913717677)
                  ·
                    refine ⟨4723558519493353467644129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12596156051982275913717677 4723558519493353467644129)
                    ·
                      refine ⟨3542668889620015100733097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723558519493353467644129 3542668889620015100733097)
                      ·
                        rfl

theorem cell23_6899323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3, 2].length) (baseStart_6899323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899323 prefixEnd_6899323 := by exact prefixLift 6899323
  have htrace : WordTrace (prefixWord ++ tailWord_6899323) baseStart_6899323 baseEnd_6899323 := by
    simpa [prefixWord, tailWord_6899323, baseEnd_6899323] using wordTrace_append hprefix tailTrace_6899323
  have hstable : (prefixWord ++ tailWord_6899323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899323).length < 2 ^ (prefixWord ++ tailWord_6899323).sum := by decide
  have hdescent : baseEnd_6899323 < baseStart_6899323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899340 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_6899340 : Nat := 118140960795 + 6899340 * 2 ^ 59
def prefixEnd_6899340 : Nat := 4983230072969 + 3 ^ 40 * 6899340 * 2
def baseEnd_6899340 : Nat := 3542677618791141534220519

theorem tailTrace_6899340 : CollatzResearch.WordTrace tailWord_6899340 prefixEnd_6899340 3542677618791141534220519 := by
  unfold tailWord_6899340
  simp only [CollatzResearch.WordTrace]
  refine ⟨125819801412438484153391737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167759735216584645537855649 125819801412438484153391737)
  ·
    refine ⟨94364851059328863115043803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125819801412438484153391737 94364851059328863115043803)
    ·
      refine ⟨141547276588993294672565705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94364851059328863115043803 141547276588993294672565705)
      ·
        refine ⟨106160457441744971004424279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141547276588993294672565705 106160457441744971004424279)
        ·
          refine ⟨159240686162617456506636419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106160457441744971004424279 159240686162617456506636419)
          ·
            refine ⟨238861029243926184759954629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159240686162617456506636419 238861029243926184759954629)
            ·
              refine ⟨44786442983236159642491493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238861029243926184759954629 44786442983236159642491493)
              ·
                refine ⟨8397458059356779932967155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44786442983236159642491493 8397458059356779932967155)
                ·
                  refine ⟨12596187089035169899450733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8397458059356779932967155 12596187089035169899450733)
                  ·
                    refine ⟨4723570158388188712294025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12596187089035169899450733 4723570158388188712294025)
                    ·
                      refine ⟨3542677618791141534220519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723570158388188712294025 3542677618791141534220519)
                      ·
                        rfl

theorem cell23_6899340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_6899340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899340 prefixEnd_6899340 := by exact prefixLift 6899340
  have htrace : WordTrace (prefixWord ++ tailWord_6899340) baseStart_6899340 baseEnd_6899340 := by
    simpa [prefixWord, tailWord_6899340, baseEnd_6899340] using wordTrace_append hprefix tailTrace_6899340
  have hstable : (prefixWord ++ tailWord_6899340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899340).length < 2 ^ (prefixWord ++ tailWord_6899340).sum := by decide
  have hdescent : baseEnd_6899340 < baseStart_6899340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899353 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 3, 4, 2]
def baseStart_6899353 : Nat := 118140960795 + 6899353 * 2 ^ 59
def prefixEnd_6899353 : Nat := 4983230072969 + 3 ^ 40 * 6899353 * 2
def baseEnd_6899353 : Nat := 3542684294039649983357959

theorem tailTrace_6899353 : CollatzResearch.WordTrace tailWord_6899353 prefixEnd_6899353 3542684294039649983357959 := by
  unfold tailWord_6899353
  simp only [CollatzResearch.WordTrace]
  refine ⟨251640076973829871527006713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167760051315886581018004475 251640076973829871527006713)
  ·
    refine ⟨188730057730372403645255035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251640076973829871527006713 188730057730372403645255035)
    ·
      refine ⟨283095086595558605467882553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188730057730372403645255035 283095086595558605467882553)
      ·
        refine ⟨212321314946668954100911915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283095086595558605467882553 212321314946668954100911915)
        ·
          refine ⟨318481972420003431151367873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212321314946668954100911915 318481972420003431151367873)
          ·
            refine ⟨238861479315002573363525905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318481972420003431151367873 238861479315002573363525905)
            ·
              refine ⟨179146109486251930022644429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238861479315002573363525905 179146109486251930022644429)
              ·
                refine ⟨67179791057344473758491661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179146109486251930022644429 67179791057344473758491661)
                ·
                  refine ⟨25192421646504177659434373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67179791057344473758491661 25192421646504177659434373)
                  ·
                    refine ⟨4723579058719533311143945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25192421646504177659434373 4723579058719533311143945)
                    ·
                      refine ⟨3542684294039649983357959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723579058719533311143945 3542684294039649983357959)
                      ·
                        rfl

theorem cell23_6899353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_6899353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899353 prefixEnd_6899353 := by exact prefixLift 6899353
  have htrace : WordTrace (prefixWord ++ tailWord_6899353) baseStart_6899353 baseEnd_6899353 := by
    simpa [prefixWord, tailWord_6899353, baseEnd_6899353] using wordTrace_append hprefix tailTrace_6899353
  have hstable : (prefixWord ++ tailWord_6899353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899353).length < 2 ^ (prefixWord ++ tailWord_6899353).sum := by decide
  have hdescent : baseEnd_6899353 < baseStart_6899353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899376 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 7]
def baseStart_6899376 : Nat := 118140960795 + 6899376 * 2 ^ 59
def prefixEnd_6899376 : Nat := 4983230072969 + 3 ^ 40 * 6899376 * 2
def baseEnd_6899376 : Nat := 393632900454967043707817

theorem tailTrace_6899376 : CollatzResearch.WordTrace tailWord_6899376 prefixEnd_6899376 393632900454967043707817 := by
  unfold tailWord_6899376
  simp only [CollatzResearch.WordTrace]
  refine ⟨125820457926373273227546991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167760610568497697636729321 125820457926373273227546991)
  ·
    refine ⟨188730686889559909841320487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125820457926373273227546991 188730686889559909841320487)
    ·
      refine ⟨283096030334339864761980731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188730686889559909841320487 283096030334339864761980731)
      ·
        refine ⟨424644045501509797142971097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283096030334339864761980731 424644045501509797142971097)
        ·
          refine ⟨318483034126132347857228323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424644045501509797142971097 318483034126132347857228323)
          ·
            refine ⟨477724551189198521785842485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318483034126132347857228323 477724551189198521785842485)
            ·
              refine ⟨44786676673987361417422733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 477724551189198521785842485 44786676673987361417422733)
              ·
                refine ⟨16795003752745260531533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44786676673987361417422733 16795003752745260531533525)
                ·
                  refine ⟨393632900454967043707817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16795003752745260531533525 393632900454967043707817)
                  ·
                    rfl

theorem cell23_6899376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_6899376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899376 prefixEnd_6899376 := by exact prefixLift 6899376
  have htrace : WordTrace (prefixWord ++ tailWord_6899376) baseStart_6899376 baseEnd_6899376 := by
    simpa [prefixWord, tailWord_6899376, baseEnd_6899376] using wordTrace_append hprefix tailTrace_6899376
  have hstable : (prefixWord ++ tailWord_6899376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899376).length < 2 ^ (prefixWord ++ tailWord_6899376).sum := by decide
  have hdescent : baseEnd_6899376 < baseStart_6899376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899383 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_6899383 : Nat := 118140960795 + 6899383 * 2 ^ 59
def prefixEnd_6899383 : Nat := 4983230072969 + 3 ^ 40 * 6899383 * 2
def baseEnd_6899383 : Nat := 3542699698459284865982821

theorem tailTrace_6899383 : CollatzResearch.WordTrace tailWord_6899383 prefixEnd_6899383 3542699698459284865982821 := by
  unfold tailWord_6899383
  simp only [CollatzResearch.WordTrace]
  refine ⟨251641171163721186650598803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167760780775814124433732535 251641171163721186650598803)
  ·
    refine ⟨377461756745581779975898205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251641171163721186650598803 377461756745581779975898205)
    ·
      refine ⟨141548158779593167490961827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377461756745581779975898205 141548158779593167490961827)
      ·
        refine ⟨212322238169389751236442741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141548158779593167490961827 212322238169389751236442741)
        ·
          refine ⟨19905209828380289178416507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212322238169389751236442741 19905209828380289178416507)
          ·
            refine ⟨29857814742570433767624761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19905209828380289178416507 29857814742570433767624761)
            ·
              refine ⟨22393361056927825325718571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29857814742570433767624761 22393361056927825325718571)
              ·
                refine ⟨33590041585391737988577857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22393361056927825325718571 33590041585391737988577857)
                ·
                  refine ⟨25192531189043803491433393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33590041585391737988577857 25192531189043803491433393)
                  ·
                    refine ⟨18894398391782852618575045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25192531189043803491433393 18894398391782852618575045)
                    ·
                      refine ⟨3542699698459284865982821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18894398391782852618575045 3542699698459284865982821)
                      ·
                        rfl

theorem cell23_6899383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_6899383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899383 prefixEnd_6899383 := by exact prefixLift 6899383
  have htrace : WordTrace (prefixWord ++ tailWord_6899383) baseStart_6899383 baseEnd_6899383 := by
    simpa [prefixWord, tailWord_6899383, baseEnd_6899383] using wordTrace_append hprefix tailTrace_6899383
  have hstable : (prefixWord ++ tailWord_6899383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899383).length < 2 ^ (prefixWord ++ tailWord_6899383).sum := by decide
  have hdescent : baseEnd_6899383 < baseStart_6899383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899423 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 2, 5]
def baseStart_6899423 : Nat := 118140960795 + 6899423 * 2 ^ 59
def prefixEnd_6899423 : Nat := 4983230072969 + 3 ^ 40 * 6899423 * 2
def baseEnd_6899423 : Nat := 1180906745895154903160879

theorem tailTrace_6899423 : CollatzResearch.WordTrace tailWord_6899423 prefixEnd_6899423 1180906745895154903160879 := by
  unfold tailWord_6899423
  simp only [CollatzResearch.WordTrace]
  refine ⟨251642630083576273482054923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167761753389050848988036615 251642630083576273482054923)
  ·
    refine ⟨377463945125364410223082385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251642630083576273482054923 377463945125364410223082385)
    ·
      refine ⟨283097958844023307667311789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377463945125364410223082385 283097958844023307667311789)
      ·
        refine ⟨106161734566508740375241921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283097958844023307667311789 106161734566508740375241921)
        ·
          refine ⟨79621300924881555281431441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106161734566508740375241921 79621300924881555281431441)
          ·
            refine ⟨59715975693661166461073581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79621300924881555281431441 59715975693661166461073581)
            ·
              refine ⟨22393490885122937422902593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59715975693661166461073581 22393490885122937422902593)
              ·
                refine ⟨16795118163842203067176945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22393490885122937422902593 16795118163842203067176945)
                ·
                  refine ⟨12596338622881652300382709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16795118163842203067176945 12596338622881652300382709)
                  ·
                    refine ⟨1180906745895154903160879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12596338622881652300382709 1180906745895154903160879)
                    ·
                      rfl

theorem cell23_6899423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_6899423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899423 prefixEnd_6899423 := by exact prefixLift 6899423
  have htrace : WordTrace (prefixWord ++ tailWord_6899423) baseStart_6899423 baseEnd_6899423 := by
    simpa [prefixWord, tailWord_6899423, baseEnd_6899423] using wordTrace_append hprefix tailTrace_6899423
  have hstable : (prefixWord ++ tailWord_6899423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899423).length < 2 ^ (prefixWord ++ tailWord_6899423).sum := by decide
  have hdescent : baseEnd_6899423 < baseStart_6899423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899427 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 7]
def baseStart_6899427 : Nat := 118140960795 + 6899427 * 2 ^ 59
def prefixEnd_6899427 : Nat := 4983230072969 + 3 ^ 40 * 6899427 * 2
def baseEnd_6899427 : Nat := 393635810178675854870291

theorem tailTrace_6899427 : CollatzResearch.WordTrace tailWord_6899427 prefixEnd_6899427 393635810178675854870291 := by
  unfold tailWord_6899427
  simp only [CollatzResearch.WordTrace]
  refine ⟨251642775975561782165200535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167761850650374521443467023 251642775975561782165200535)
  ·
    refine ⟨377464163963342673247800803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251642775975561782165200535 377464163963342673247800803)
    ·
      refine ⟨566196245945014009871701205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377464163963342673247800803 566196245945014009871701205)
      ·
        refine ⟨13270224514336265856367997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 566196245945014009871701205 13270224514336265856367997)
        ·
          refine ⟨4976334192876099696137999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13270224514336265856367997 4976334192876099696137999)
          ·
            refine ⟨7464501289314149544206999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976334192876099696137999 7464501289314149544206999)
            ·
              refine ⟨11196751933971224316310499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464501289314149544206999 11196751933971224316310499)
              ·
                refine ⟨16795127900956836474465749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196751933971224316310499 16795127900956836474465749)
                ·
                  refine ⟨393635810178675854870291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16795127900956836474465749 393635810178675854870291)
                  ·
                    rfl

theorem cell23_6899427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 7].length) (baseStart_6899427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899427 prefixEnd_6899427 := by exact prefixLift 6899427
  have htrace : WordTrace (prefixWord ++ tailWord_6899427) baseStart_6899427 baseEnd_6899427 := by
    simpa [prefixWord, tailWord_6899427, baseEnd_6899427] using wordTrace_append hprefix tailTrace_6899427
  have hstable : (prefixWord ++ tailWord_6899427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899427).length < 2 ^ (prefixWord ++ tailWord_6899427).sum := by decide
  have hdescent : baseEnd_6899427 < baseStart_6899427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899460 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6899460 : Nat := 118140960795 + 6899460 * 2 ^ 59
def prefixEnd_6899460 : Nat := 4983230072969 + 3 ^ 40 * 6899460 * 2
def baseEnd_6899460 : Nat := 3542739236469681064719967

theorem tailTrace_6899460 : CollatzResearch.WordTrace tailWord_6899460 prefixEnd_6899460 3542739236469681064719967 := by
  unfold tailWord_6899460
  simp only [CollatzResearch.WordTrace]
  refine ⟨125821989792221114400575917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167762653056294819200767889 125821989792221114400575917)
  ·
    refine ⟨47183246172082917900215969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125821989792221114400575917 47183246172082917900215969)
    ·
      refine ⟨35387434629062188425161977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47183246172082917900215969 35387434629062188425161977)
      ·
        refine ⟨26540575971796641318871483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35387434629062188425161977 26540575971796641318871483)
        ·
          refine ⟨39810863957694961978307225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26540575971796641318871483 39810863957694961978307225)
          ·
            refine ⟨29858147968271221483730419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39810863957694961978307225 29858147968271221483730419)
            ·
              refine ⟨44787221952406832225595629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29858147968271221483730419 44787221952406832225595629)
              ·
                refine ⟨16795208232152562084598361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44787221952406832225595629 16795208232152562084598361)
                ·
                  refine ⟨12596406174114421563448771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16795208232152562084598361 12596406174114421563448771)
                  ·
                    refine ⟨18894609261171632345173157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12596406174114421563448771 18894609261171632345173157)
                    ·
                      refine ⟨3542739236469681064719967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18894609261171632345173157 3542739236469681064719967)
                      ·
                        rfl

theorem cell23_6899460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6899460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899460 prefixEnd_6899460 := by exact prefixLift 6899460
  have htrace : WordTrace (prefixWord ++ tailWord_6899460) baseStart_6899460 baseEnd_6899460 := by
    simpa [prefixWord, tailWord_6899460, baseEnd_6899460] using wordTrace_append hprefix tailTrace_6899460
  have hstable : (prefixWord ++ tailWord_6899460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899460).length < 2 ^ (prefixWord ++ tailWord_6899460).sum := by decide
  have hdescent : baseEnd_6899460 < baseStart_6899460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899480 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_6899480 : Nat := 118140960795 + 6899480 * 2 ^ 59
def prefixEnd_6899480 : Nat := 4983230072969 + 3 ^ 40 * 6899480 * 2
def baseEnd_6899480 : Nat := 3542749506082770986469875

theorem tailTrace_6899480 : CollatzResearch.WordTrace tailWord_6899480 prefixEnd_6899480 3542749506082770986469875 := by
  unfold tailWord_6899480
  simp only [CollatzResearch.WordTrace]
  refine ⟨125822354522184886108439947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167763139362913181477919929 125822354522184886108439947)
  ·
    refine ⟨188733531783277329162659921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125822354522184886108439947 188733531783277329162659921)
    ·
      refine ⟨141550148837457996871994941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188733531783277329162659921 141550148837457996871994941)
      ·
        refine ⟨53081305814046748826998103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141550148837457996871994941 53081305814046748826998103)
        ·
          refine ⟨79621958721070123240497155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53081305814046748826998103 79621958721070123240497155)
          ·
            refine ⟨119432938081605184860745733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79621958721070123240497155 119432938081605184860745733)
            ·
              refine ⟨22393675890300972161389825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119432938081605184860745733 22393675890300972161389825)
              ·
                refine ⟨16795256917725729121042369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22393675890300972161389825 16795256917725729121042369)
                ·
                  refine ⟨12596442688294296840781777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16795256917725729121042369 12596442688294296840781777)
                  ·
                    refine ⟨9447332016220722630586333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12596442688294296840781777 9447332016220722630586333)
                    ·
                      refine ⟨3542749506082770986469875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9447332016220722630586333 3542749506082770986469875)
                      ·
                        rfl

theorem cell23_6899480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_6899480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899480 prefixEnd_6899480 := by exact prefixLift 6899480
  have htrace : WordTrace (prefixWord ++ tailWord_6899480) baseStart_6899480 baseEnd_6899480 := by
    simpa [prefixWord, tailWord_6899480, baseEnd_6899480] using wordTrace_append hprefix tailTrace_6899480
  have hstable : (prefixWord ++ tailWord_6899480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899480).length < 2 ^ (prefixWord ++ tailWord_6899480).sum := by decide
  have hdescent : baseEnd_6899480 < baseStart_6899480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899487 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 1, 4]
def baseStart_6899487 : Nat := 118140960795 + 6899487 * 2 ^ 59
def prefixEnd_6899487 : Nat := 4983230072969 + 3 ^ 40 * 6899487 * 2
def baseEnd_6899487 : Nat := 1180917700149117486360781

theorem tailTrace_6899487 : CollatzResearch.WordTrace tailWord_6899487 prefixEnd_6899487 1180917700149117486360781 := by
  unfold tailWord_6899487
  simp only [CollatzResearch.WordTrace]
  refine ⟨251644964355344412412384715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167763309570229608274923143 251644964355344412412384715)
  ·
    refine ⟨377467446533016618618577073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251644964355344412412384715 377467446533016618618577073)
    ·
      refine ⟨283100584899762463963932805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377467446533016618618577073 283100584899762463963932805)
      ·
        refine ⟨53081359668705461993237401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283100584899762463963932805 53081359668705461993237401)
        ·
          refine ⟨39811019751529096494928051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53081359668705461993237401 39811019751529096494928051)
          ·
            refine ⟨59716529627293644742392077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39811019751529096494928051 59716529627293644742392077)
            ·
              refine ⟨22393698610235116778397029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59716529627293644742392077 22393698610235116778397029)
              ·
                refine ⟨4198818489419084395949443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22393698610235116778397029 4198818489419084395949443)
                ·
                  refine ⟨6298227734128626593924165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198818489419084395949443 6298227734128626593924165)
                  ·
                    refine ⟨1180917700149117486360781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6298227734128626593924165 1180917700149117486360781)
                    ·
                      rfl

theorem cell23_6899487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 4].length) (baseStart_6899487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899487 prefixEnd_6899487 := by exact prefixLift 6899487
  have htrace : WordTrace (prefixWord ++ tailWord_6899487) baseStart_6899487 baseEnd_6899487 := by
    simpa [prefixWord, tailWord_6899487, baseEnd_6899487] using wordTrace_append hprefix tailTrace_6899487
  have hstable : (prefixWord ++ tailWord_6899487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899487).length < 2 ^ (prefixWord ++ tailWord_6899487).sum := by decide
  have hdescent : baseEnd_6899487 < baseStart_6899487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899530 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_6899530 : Nat := 118140960795 + 6899530 * 2 ^ 59
def prefixEnd_6899530 : Nat := 4983230072969 + 3 ^ 40 * 6899530 * 2
def baseEnd_6899530 : Nat := 1180925060038498596948215

theorem tailTrace_6899530 : CollatzResearch.WordTrace tailWord_6899530 prefixEnd_6899530 1180925060038498596948215 := by
  unfold tailWord_6899530
  simp only [CollatzResearch.WordTrace]
  refine ⟨62911633173547157689050011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167764355129459087170800029 62911633173547157689050011)
  ·
    refine ⟨94367449760320736533575017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62911633173547157689050011 94367449760320736533575017)
    ·
      refine ⟨70775587320240552400181263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94367449760320736533575017 70775587320240552400181263)
      ·
        refine ⟨106163380980360828600271895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70775587320240552400181263 106163380980360828600271895)
        ·
          refine ⟨159245071470541242900407843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106163380980360828600271895 159245071470541242900407843)
          ·
            refine ⟨238867607205811864350611765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159245071470541242900407843 238867607205811864350611765)
            ·
              refine ⟨22393838175544862282869853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238867607205811864350611765 22393838175544862282869853)
              ·
                refine ⟨8397689315829323356076195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22393838175544862282869853 8397689315829323356076195)
                ·
                  refine ⟨12596533973743985034114293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8397689315829323356076195 12596533973743985034114293)
                  ·
                    refine ⟨1180925060038498596948215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12596533973743985034114293 1180925060038498596948215)
                    ·
                      rfl

theorem cell23_6899530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_6899530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899530 prefixEnd_6899530 := by exact prefixLift 6899530
  have htrace : WordTrace (prefixWord ++ tailWord_6899530) baseStart_6899530 baseEnd_6899530 := by
    simpa [prefixWord, tailWord_6899530, baseEnd_6899530] using wordTrace_append hprefix tailTrace_6899530
  have hstable : (prefixWord ++ tailWord_6899530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899530).length < 2 ^ (prefixWord ++ tailWord_6899530).sum := by decide
  have hdescent : baseEnd_6899530 < baseStart_6899530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899587 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 3]
def baseStart_6899587 : Nat := 118140960795 + 6899587 * 2 ^ 59
def prefixEnd_6899587 : Nat := 4983230072969 + 3 ^ 40 * 6899587 * 2
def baseEnd_6899587 : Nat := 3542804448512802067831883

theorem tailTrace_6899587 : CollatzResearch.WordTrace tailWord_6899587 prefixEnd_6899587 3542804448512802067831883 := by
  unfold tailWord_6899587
  simp only [CollatzResearch.WordTrace]
  refine ⟨251648611654982129491025015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167765741103321419660683343 251648611654982129491025015)
  ·
    refine ⟨377472917482473194236537523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251648611654982129491025015 377472917482473194236537523)
    ·
      refine ⟨566209376223709791354806285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377472917482473194236537523 566209376223709791354806285)
      ·
        refine ⟨212328516083891171758052357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566209376223709791354806285 212328516083891171758052357)
        ·
          refine ⟨39811596765729594704634817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212328516083891171758052357 39811596765729594704634817)
          ·
            refine ⟨29858697574297196028476113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39811596765729594704634817 29858697574297196028476113)
            ·
              refine ⟨22394023180722897021357085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29858697574297196028476113 22394023180722897021357085)
              ·
                refine ⟨8397758692771086383008907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22394023180722897021357085 8397758692771086383008907)
                ·
                  refine ⟨12596638039156629574513361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8397758692771086383008907 12596638039156629574513361)
                  ·
                    refine ⟨9447478529367472180885021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12596638039156629574513361 9447478529367472180885021)
                    ·
                      refine ⟨3542804448512802067831883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9447478529367472180885021 3542804448512802067831883)
                      ·
                        rfl

theorem cell23_6899587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_6899587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899587 prefixEnd_6899587 := by exact prefixLift 6899587
  have htrace : WordTrace (prefixWord ++ tailWord_6899587) baseStart_6899587 baseEnd_6899587 := by
    simpa [prefixWord, tailWord_6899587, baseEnd_6899587] using wordTrace_append hprefix tailTrace_6899587
  have hstable : (prefixWord ++ tailWord_6899587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899587).length < 2 ^ (prefixWord ++ tailWord_6899587).sum := by decide
  have hdescent : baseEnd_6899587 < baseStart_6899587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899720 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6899720 : Nat := 118140960795 + 6899720 * 2 ^ 59
def prefixEnd_6899720 : Nat := 4983230072969 + 3 ^ 40 * 6899720 * 2
def baseEnd_6899720 : Nat := 3542872741439850047468771

theorem tailTrace_6899720 : CollatzResearch.WordTrace tailWord_6899720 prefixEnd_6899720 3542872741439850047468771 := by
  unfold tailWord_6899720
  simp only [CollatzResearch.WordTrace]
  refine ⟨125826731281750146602808307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167768975042333528803744409 125826731281750146602808307)
  ·
    refine ⟨188740096922625219904212461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125826731281750146602808307 188740096922625219904212461)
    ·
      refine ⟨70777536345984457464079673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188740096922625219904212461 70777536345984457464079673)
      ·
        refine ⟨53083152259488343098059755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70777536345984457464079673 53083152259488343098059755)
        ·
          refine ⟨79624728389232514647089633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53083152259488343098059755 79624728389232514647089633)
          ·
            refine ⟨59718546291924385985317225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79624728389232514647089633 59718546291924385985317225)
            ·
              refine ⟨44788909718943289488987919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59718546291924385985317225 44788909718943289488987919)
              ·
                refine ⟨67183364578414934233481879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44788909718943289488987919 67183364578414934233481879)
                ·
                  refine ⟨100775046867622401350222819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67183364578414934233481879 100775046867622401350222819)
                  ·
                    refine ⟨151162570301433602025334229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100775046867622401350222819 151162570301433602025334229)
                    ·
                      refine ⟨3542872741439850047468771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151162570301433602025334229 3542872741439850047468771)
                      ·
                        rfl

theorem cell23_6899720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6899720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899720 prefixEnd_6899720 := by exact prefixLift 6899720
  have htrace : WordTrace (prefixWord ++ tailWord_6899720) baseStart_6899720 baseEnd_6899720 := by
    simpa [prefixWord, tailWord_6899720, baseEnd_6899720] using wordTrace_append hprefix tailTrace_6899720
  have hstable : (prefixWord ++ tailWord_6899720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899720).length < 2 ^ (prefixWord ++ tailWord_6899720).sum := by decide
  have hdescent : baseEnd_6899720 < baseStart_6899720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899747 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4]
def baseStart_6899747 : Nat := 118140960795 + 6899747 * 2 ^ 59
def prefixEnd_6899747 : Nat := 4983230072969 + 3 ^ 40 * 6899747 * 2
def baseEnd_6899747 : Nat := 3542886605417521441831147

theorem tailTrace_6899747 : CollatzResearch.WordTrace tailWord_6899747 prefixEnd_6899747 3542886605417521441831147 := by
  unfold tailWord_6899747
  simp only [CollatzResearch.WordTrace]
  refine ⟨251654447334402476816849495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167769631556268317877899663 251654447334402476816849495)
  ·
    refine ⟨377481671001603715225274243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251654447334402476816849495 377481671001603715225274243)
    ·
      refine ⟨566222506502405572837911365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377481671001603715225274243 566222506502405572837911365)
      ·
        refine ⟨106166719969201044907108381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566222506502405572837911365 106166719969201044907108381)
        ·
          refine ⟨39812519988450391840165643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106166719969201044907108381 39812519988450391840165643)
          ·
            refine ⟨59718779982675587760248465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39812519988450391840165643 59718779982675587760248465)
            ·
              refine ⟨44789084987006690820186349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59718779982675587760248465 44789084987006690820186349)
              ·
                refine ⟨16795906870127509057569881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44789084987006690820186349 16795906870127509057569881)
                ·
                  refine ⟨12596930152595631793177411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16795906870127509057569881 12596930152595631793177411)
                  ·
                    refine ⟨18895395228893447689766117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12596930152595631793177411 18895395228893447689766117)
                    ·
                      refine ⟨3542886605417521441831147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18895395228893447689766117 3542886605417521441831147)
                      ·
                        rfl

theorem cell23_6899747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_6899747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899747 prefixEnd_6899747 := by exact prefixLift 6899747
  have htrace : WordTrace (prefixWord ++ tailWord_6899747) baseStart_6899747 baseEnd_6899747 := by
    simpa [prefixWord, tailWord_6899747, baseEnd_6899747] using wordTrace_append hprefix tailTrace_6899747
  have hstable : (prefixWord ++ tailWord_6899747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899747).length < 2 ^ (prefixWord ++ tailWord_6899747).sum := by decide
  have hdescent : baseEnd_6899747 < baseStart_6899747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899748 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 5]
def baseStart_6899748 : Nat := 118140960795 + 6899748 * 2 ^ 59
def prefixEnd_6899748 : Nat := 4983230072969 + 3 ^ 40 * 6899748 * 2
def baseEnd_6899748 : Nat := 393654124322019548657627

theorem tailTrace_6899748 : CollatzResearch.WordTrace tailWord_6899748 prefixEnd_6899748 393654124322019548657627 := by
  unfold tailWord_6899748
  simp only [CollatzResearch.WordTrace]
  refine ⟨125827241903699426993817949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167769655871599235991757265 125827241903699426993817949)
  ·
    refine ⟨47185215713887285122681731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125827241903699426993817949 47185215713887285122681731)
    ·
      refine ⟨70777823570830927684022597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47185215713887285122681731 70777823570830927684022597)
      ·
        refine ⟨13270841919530798940754237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70777823570830927684022597 13270841919530798940754237)
        ·
          refine ⟨4976565719824049602782839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13270841919530798940754237 4976565719824049602782839)
          ·
            refine ⟨7464848579736074404174259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976565719824049602782839 7464848579736074404174259)
            ·
              refine ⟨11197272869604111606261389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464848579736074404174259 11197272869604111606261389)
              ·
                refine ⟨4198977326101541852348021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11197272869604111606261389 4198977326101541852348021)
                ·
                  refine ⟨393654124322019548657627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198977326101541852348021 393654124322019548657627)
                  ·
                    rfl

theorem cell23_6899748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_6899748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899748 prefixEnd_6899748 := by exact prefixLift 6899748
  have htrace : WordTrace (prefixWord ++ tailWord_6899748) baseStart_6899748 baseEnd_6899748 := by
    simpa [prefixWord, tailWord_6899748, baseEnd_6899748] using wordTrace_append hprefix tailTrace_6899748
  have hstable : (prefixWord ++ tailWord_6899748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899748).length < 2 ^ (prefixWord ++ tailWord_6899748).sum := by decide
  have hdescent : baseEnd_6899748 < baseStart_6899748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899767 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_6899767 : Nat := 118140960795 + 6899767 * 2 ^ 59
def prefixEnd_6899767 : Nat := 4983230072969 + 3 ^ 40 * 6899767 * 2
def baseEnd_6899767 : Nat := 3542896875030611363581055

theorem tailTrace_6899767 : CollatzResearch.WordTrace tailWord_6899767 prefixEnd_6899767 3542896875030611363581055 := by
  unfold tailWord_6899767
  simp only [CollatzResearch.WordTrace]
  refine ⟨251655176794330020232577555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167770117862886680155051703 251655176794330020232577555)
  ·
    refine ⟨377482765191495030348866333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251655176794330020232577555 377482765191495030348866333)
    ·
      refine ⟨141556036946810636380824875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377482765191495030348866333 141556036946810636380824875)
      ·
        refine ⟨212334055420215954571237313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141556036946810636380824875 212334055420215954571237313)
        ·
          refine ⟨159250541565161965928427985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212334055420215954571237313 159250541565161965928427985)
          ·
            refine ⟨119437906173871474446320989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159250541565161965928427985 119437906173871474446320989)
            ·
              refine ⟨44789214815201802917370371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119437906173871474446320989 44789214815201802917370371)
              ·
                refine ⟨67183822222802704376055557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44789214815201802917370371 67183822222802704376055557)
                ·
                  refine ⟨12596966666775507070510417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67183822222802704376055557 12596966666775507070510417)
                  ·
                    refine ⟨9447725000081630302882813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12596966666775507070510417 9447725000081630302882813)
                    ·
                      refine ⟨3542896875030611363581055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9447725000081630302882813 3542896875030611363581055)
                      ·
                        rfl

theorem cell23_6899767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_6899767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899767 prefixEnd_6899767 := by exact prefixLift 6899767
  have htrace : WordTrace (prefixWord ++ tailWord_6899767) baseStart_6899767 baseEnd_6899767 := by
    simpa [prefixWord, tailWord_6899767, baseEnd_6899767] using wordTrace_append hprefix tailTrace_6899767
  have hstable : (prefixWord ++ tailWord_6899767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899767).length < 2 ^ (prefixWord ++ tailWord_6899767).sum := by decide
  have hdescent : baseEnd_6899767 < baseStart_6899767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899798 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6899798 : Nat := 118140960795 + 6899798 * 2 ^ 59
def prefixEnd_6899798 : Nat := 4983230072969 + 3 ^ 40 * 6899798 * 2
def baseEnd_6899798 : Nat := 3542912792930900742293413

theorem tailTrace_6899798 : CollatzResearch.WordTrace tailWord_6899798 prefixEnd_6899798 3542912792930900742293413 := by
  unfold tailWord_6899798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728519216076107032934753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167770871638145141684637365 15728519216076107032934753)
  ·
    refine ⟨11796389412057080274701065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15728519216076107032934753 11796389412057080274701065)
    ·
      refine ⟨8847292059042810206025799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11796389412057080274701065 8847292059042810206025799)
      ·
        refine ⟨13270938088564215309038699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8847292059042810206025799 13270938088564215309038699)
        ·
          refine ⟨19906407132846322963558049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13270938088564215309038699 19906407132846322963558049)
          ·
            refine ⟨14929805349634742222668537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19906407132846322963558049 14929805349634742222668537)
            ·
              refine ⟨11197354012226056667001403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14929805349634742222668537 11197354012226056667001403)
              ·
                refine ⟨16796031018339085000502105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197354012226056667001403 16796031018339085000502105)
                ·
                  refine ⟨12597023263754313750376579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16796031018339085000502105 12597023263754313750376579)
                  ·
                    refine ⟨18895534895631470625564869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12597023263754313750376579 18895534895631470625564869)
                    ·
                      refine ⟨3542912792930900742293413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18895534895631470625564869 3542912792930900742293413)
                      ·
                        rfl

theorem cell23_6899798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6899798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899798 prefixEnd_6899798 := by exact prefixLift 6899798
  have htrace : WordTrace (prefixWord ++ tailWord_6899798) baseStart_6899798 baseEnd_6899798 := by
    simpa [prefixWord, tailWord_6899798, baseEnd_6899798] using wordTrace_append hprefix tailTrace_6899798
  have hstable : (prefixWord ++ tailWord_6899798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899798).length < 2 ^ (prefixWord ++ tailWord_6899798).sum := by decide
  have hdescent : baseEnd_6899798 < baseStart_6899798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899847 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 1, 6]
def baseStart_6899847 : Nat := 118140960795 + 6899847 * 2 ^ 59
def prefixEnd_6899847 : Nat := 4983230072969 + 3 ^ 40 * 6899847 * 2
def baseEnd_6899847 : Nat := 1180979317827657016860229

theorem tailTrace_6899847 : CollatzResearch.WordTrace tailWord_6899847 prefixEnd_6899847 1180979317827657016860229 := by
  unfold tailWord_6899847
  simp only [CollatzResearch.WordTrace]
  refine ⟨251658094634040193895489795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167772063089360129263659863 251658094634040193895489795)
  ·
    refine ⟨377487141951060290843234693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251658094634040193895489795 377487141951060290843234693)
    ·
      refine ⟨70778839115823804533106505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377487141951060290843234693 70778839115823804533106505)
      ·
        refine ⟨53084129336867853399829879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70778839115823804533106505 53084129336867853399829879)
        ·
          refine ⟨79626194005301780099744819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53084129336867853399829879 79626194005301780099744819)
          ·
            refine ⟨119439291007952670149617229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79626194005301780099744819 119439291007952670149617229)
            ·
              refine ⟨44789734127982251306106461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119439291007952670149617229 44789734127982251306106461)
              ·
                refine ⟨16796150297993344239789923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44789734127982251306106461 16796150297993344239789923)
                ·
                  refine ⟨25194225446990016359684885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16796150297993344239789923 25194225446990016359684885)
                  ·
                    refine ⟨1180979317827657016860229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25194225446990016359684885 1180979317827657016860229)
                    ·
                      rfl

theorem cell23_6899847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_6899847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899847 prefixEnd_6899847 := by exact prefixLift 6899847
  have htrace : WordTrace (prefixWord ++ tailWord_6899847) baseStart_6899847 baseEnd_6899847 := by
    simpa [prefixWord, tailWord_6899847, baseEnd_6899847] using wordTrace_append hprefix tailTrace_6899847
  have hstable : (prefixWord ++ tailWord_6899847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899847).length < 2 ^ (prefixWord ++ tailWord_6899847).sum := by decide
  have hdescent : baseEnd_6899847 < baseStart_6899847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899867 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4]
def baseStart_6899867 : Nat := 118140960795 + 6899867 * 2 ^ 59
def prefixEnd_6899867 : Nat := 4983230072969 + 3 ^ 40 * 6899867 * 2
def baseEnd_6899867 : Nat := 3542948223096060972330595

theorem tailTrace_6899867 : CollatzResearch.WordTrace tailWord_6899867 prefixEnd_6899867 3542948223096060972330595 := by
  unfold tailWord_6899867
  simp only [CollatzResearch.WordTrace]
  refine ⟨251658824093967737311217855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167772549395978491540811903 251658824093967737311217855)
  ·
    refine ⟨377488236140951605966826783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251658824093967737311217855 377488236140951605966826783)
    ·
      refine ⟨566232354211427408950240175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377488236140951605966826783 566232354211427408950240175)
      ·
        refine ⟨849348531317141113425360263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566232354211427408950240175 849348531317141113425360263)
        ·
          refine ⟨1274022796975711670138040395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849348531317141113425360263 1274022796975711670138040395)
          ·
            refine ⟨1911034195463567505207060593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274022796975711670138040395 1911034195463567505207060593)
            ·
              refine ⟨1433275646597675628905295445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911034195463567505207060593 1433275646597675628905295445)
              ·
                refine ⟨16796198983566511276233931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1433275646597675628905295445 16796198983566511276233931)
                ·
                  refine ⟨25194298475349766914350897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16796198983566511276233931 25194298475349766914350897)
                  ·
                    refine ⟨18895723856512325185763173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25194298475349766914350897 18895723856512325185763173)
                    ·
                      refine ⟨3542948223096060972330595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18895723856512325185763173 3542948223096060972330595)
                      ·
                        rfl

theorem cell23_6899867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_6899867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899867 prefixEnd_6899867 := by exact prefixLift 6899867
  have htrace : WordTrace (prefixWord ++ tailWord_6899867) baseStart_6899867 baseEnd_6899867 := by
    simpa [prefixWord, tailWord_6899867, baseEnd_6899867] using wordTrace_append hprefix tailTrace_6899867
  have hstable : (prefixWord ++ tailWord_6899867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899867).length < 2 ^ (prefixWord ++ tailWord_6899867).sum := by decide
  have hdescent : baseEnd_6899867 < baseStart_6899867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899871 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6899871 : Nat := 118140960795 + 6899871 * 2 ^ 59
def prefixEnd_6899871 : Nat := 4983230072969 + 3 ^ 40 * 6899871 * 2
def baseEnd_6899871 : Nat := 3542950277018678956680577

theorem tailTrace_6899871 : CollatzResearch.WordTrace tailWord_6899871 prefixEnd_6899871 3542950277018678956680577 := by
  unfold tailWord_6899871
  simp only [CollatzResearch.WordTrace]
  refine ⟨251658969985953245994363467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167772646657302163996242311 251658969985953245994363467)
  ·
    refine ⟨377488454978929868991545201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251658969985953245994363467 377488454978929868991545201)
    ·
      refine ⟨283116341234197401743658901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377488454978929868991545201 283116341234197401743658901)
      ·
        refine ⟨13271078495353003206734011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 283116341234197401743658901 13271078495353003206734011)
        ·
          refine ⟨19906617743029504810101017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13271078495353003206734011 19906617743029504810101017)
          ·
            refine ⟨14929963307272128607575763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19906617743029504810101017 14929963307272128607575763)
            ·
              refine ⟨22394944960908192911363645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14929963307272128607575763 22394944960908192911363645)
              ·
                refine ⟨8398104360340572341761367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22394944960908192911363645 8398104360340572341761367)
                ·
                  refine ⟨12597156540510858512642051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398104360340572341761367 12597156540510858512642051)
                  ·
                    refine ⟨18895734810766287768963077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12597156540510858512642051 18895734810766287768963077)
                    ·
                      refine ⟨3542950277018678956680577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18895734810766287768963077 3542950277018678956680577)
                      ·
                        rfl

theorem cell23_6899871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6899871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899871 prefixEnd_6899871 := by exact prefixLift 6899871
  have htrace : WordTrace (prefixWord ++ tailWord_6899871) baseStart_6899871 baseEnd_6899871 := by
    simpa [prefixWord, tailWord_6899871, baseEnd_6899871] using wordTrace_append hprefix tailTrace_6899871
  have hstable : (prefixWord ++ tailWord_6899871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899871).length < 2 ^ (prefixWord ++ tailWord_6899871).sum := by decide
  have hdescent : baseEnd_6899871 < baseStart_6899871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899908 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_6899908 : Nat := 118140960795 + 6899908 * 2 ^ 59
def prefixEnd_6899908 : Nat := 4983230072969 + 3 ^ 40 * 6899908 * 2
def baseEnd_6899908 : Nat := 3542969275802895311917907

theorem tailTrace_6899908 : CollatzResearch.WordTrace tailWord_6899908 prefixEnd_6899908 3542969275802895311917907 := by
  unfold tailWord_6899908
  simp only [CollatzResearch.WordTrace]
  refine ⟨125830159743409600656730189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167773546324546134208973585 125830159743409600656730189)
  ·
    refine ⟨47186309903778600246273821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125830159743409600656730189 47186309903778600246273821)
    ·
      refine ⟨17694866213916975092352683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47186309903778600246273821 17694866213916975092352683)
      ·
        refine ⟨26542299320875462638529025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17694866213916975092352683 26542299320875462638529025)
        ·
          refine ⟨19906724490656596978896769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26542299320875462638529025 19906724490656596978896769)
          ·
            refine ⟨14930043367992447734172577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19906724490656596978896769 14930043367992447734172577)
            ·
              refine ⟨11197532525994335800629433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14930043367992447734172577 11197532525994335800629433)
              ·
                refine ⟨8398149394495751850472075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11197532525994335800629433 8398149394495751850472075)
                ·
                  refine ⟨12597224091743627775708113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398149394495751850472075 12597224091743627775708113)
                  ·
                    refine ⟨9447918068807720831781085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12597224091743627775708113 9447918068807720831781085)
                    ·
                      refine ⟨3542969275802895311917907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9447918068807720831781085 3542969275802895311917907)
                      ·
                        rfl

theorem cell23_6899908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_6899908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899908 prefixEnd_6899908 := by exact prefixLift 6899908
  have htrace : WordTrace (prefixWord ++ tailWord_6899908) baseStart_6899908 baseEnd_6899908 := by
    simpa [prefixWord, tailWord_6899908, baseEnd_6899908] using wordTrace_append hprefix tailTrace_6899908
  have hstable : (prefixWord ++ tailWord_6899908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899908).length < 2 ^ (prefixWord ++ tailWord_6899908).sum := by decide
  have hdescent : baseEnd_6899908 < baseStart_6899908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899922 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_6899922 : Nat := 118140960795 + 6899922 * 2 ^ 59
def prefixEnd_6899922 : Nat := 4983230072969 + 3 ^ 40 * 6899922 * 2
def baseEnd_6899922 : Nat := 3542976464532058257142843

theorem tailTrace_6899922 : CollatzResearch.WordTrace tailWord_6899922 prefixEnd_6899922 3542976464532058257142843 := by
  unfold tailWord_6899922
  simp only [CollatzResearch.WordTrace]
  refine ⟨62915207527192120426117505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167773886739178987802980013 62915207527192120426117505)
  ·
    refine ⟨47186405645394090319588129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62915207527192120426117505 47186405645394090319588129)
    ·
      refine ⟨35389804234045567739691097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47186405645394090319588129 35389804234045567739691097)
      ·
        refine ⟨26542353175534175804768323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35389804234045567739691097 26542353175534175804768323)
        ·
          refine ⟨39813529763301263707152485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26542353175534175804768323 39813529763301263707152485)
          ·
            refine ⟨7465036830618986945091091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39813529763301263707152485 7465036830618986945091091)
            ·
              refine ⟨11197555245928480417636637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465036830618986945091091 11197555245928480417636637)
              ·
                refine ⟨4199083217223180156613739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11197555245928480417636637 4199083217223180156613739)
                ·
                  refine ⟨6298624825834770234920609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199083217223180156613739 6298624825834770234920609)
                  ·
                    refine ⟨4723968619376077676190457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298624825834770234920609 4723968619376077676190457)
                    ·
                      refine ⟨3542976464532058257142843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723968619376077676190457 3542976464532058257142843)
                      ·
                        rfl

theorem cell23_6899922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_6899922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899922 prefixEnd_6899922 := by exact prefixLift 6899922
  have htrace : WordTrace (prefixWord ++ tailWord_6899922) baseStart_6899922 baseEnd_6899922 := by
    simpa [prefixWord, tailWord_6899922, baseEnd_6899922] using wordTrace_append hprefix tailTrace_6899922
  have hstable : (prefixWord ++ tailWord_6899922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899922).length < 2 ^ (prefixWord ++ tailWord_6899922).sum := by decide
  have hdescent : baseEnd_6899922 < baseStart_6899922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899927 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_6899927 : Nat := 118140960795 + 6899927 * 2 ^ 59
def prefixEnd_6899927 : Nat := 4983230072969 + 3 ^ 40 * 6899927 * 2
def baseEnd_6899927 : Nat := 3542979031935330737580319

theorem tailTrace_6899927 : CollatzResearch.WordTrace tailWord_6899927 prefixEnd_6899927 3542979031935330737580319 := by
  unfold tailWord_6899927
  simp only [CollatzResearch.WordTrace]
  refine ⟨251661012473750367558402035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167774008315833578372268023 251661012473750367558402035)
  ·
    refine ⟨377491518710625551337603053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251661012473750367558402035 377491518710625551337603053)
    ·
      refine ⟨141559319516484581751601145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377491518710625551337603053 141559319516484581751601145)
      ·
        refine ⟨106169489637363436313700859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141559319516484581751601145 106169489637363436313700859)
        ·
          refine ⟨159254234456045154470551289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106169489637363436313700859 159254234456045154470551289)
          ·
            refine ⟨119440675842033865852913467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159254234456045154470551289 119440675842033865852913467)
            ·
              refine ⟨179161013763050798779370201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119440675842033865852913467 179161013763050798779370201)
              ·
                refine ⟨134370760322288099084527651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179161013763050798779370201 134370760322288099084527651)
                ·
                  refine ⟨201556140483432148626791477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134370760322288099084527651 201556140483432148626791477)
                  ·
                    refine ⟨18895888170321763933761701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201556140483432148626791477 18895888170321763933761701)
                    ·
                      refine ⟨3542979031935330737580319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18895888170321763933761701 3542979031935330737580319)
                      ·
                        rfl

theorem cell23_6899927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_6899927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899927 prefixEnd_6899927 := by exact prefixLift 6899927
  have htrace : WordTrace (prefixWord ++ tailWord_6899927) baseStart_6899927 baseEnd_6899927 := by
    simpa [prefixWord, tailWord_6899927, baseEnd_6899927] using wordTrace_append hprefix tailTrace_6899927
  have hstable : (prefixWord ++ tailWord_6899927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899927).length < 2 ^ (prefixWord ++ tailWord_6899927).sum := by decide
  have hdescent : baseEnd_6899927 < baseStart_6899927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899939 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6899939 : Nat := 118140960795 + 6899939 * 2 ^ 59
def prefixEnd_6899939 : Nat := 4983230072969 + 3 ^ 40 * 6899939 * 2
def baseEnd_6899939 : Nat := 3542985193703184690630265

theorem tailTrace_6899939 : CollatzResearch.WordTrace tailWord_6899939 prefixEnd_6899939 3542985193703184690630265 := by
  unfold tailWord_6899939
  simp only [CollatzResearch.WordTrace]
  refine ⟨251661450149706893607838871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167774300099804595738559247 251661450149706893607838871)
  ·
    refine ⟨377492175224560340411758307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251661450149706893607838871 377492175224560340411758307)
    ·
      refine ⟨566238262836840510617637461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377492175224560340411758307 566238262836840510617637461)
      ·
        refine ⟨6635604642619224733800439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 566238262836840510617637461 6635604642619224733800439)
        ·
          refine ⟨9953406963928837100700659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635604642619224733800439 9953406963928837100700659)
          ·
            refine ⟨14930110445893255651050989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9953406963928837100700659 14930110445893255651050989)
            ·
              refine ⟨5598791417209970869144121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14930110445893255651050989 5598791417209970869144121)
              ·
                refine ⟨4199093562907478151858091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598791417209970869144121 4199093562907478151858091)
                ·
                  refine ⟨6298640344361217227787137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199093562907478151858091 6298640344361217227787137)
                  ·
                    refine ⟨4723980258270912920840353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298640344361217227787137 4723980258270912920840353)
                    ·
                      refine ⟨3542985193703184690630265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723980258270912920840353 3542985193703184690630265)
                      ·
                        rfl

theorem cell23_6899939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6899939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899939 prefixEnd_6899939 := by exact prefixLift 6899939
  have htrace : WordTrace (prefixWord ++ tailWord_6899939) baseStart_6899939 baseEnd_6899939 := by
    simpa [prefixWord, tailWord_6899939, baseEnd_6899939] using wordTrace_append hprefix tailTrace_6899939
  have hstable : (prefixWord ++ tailWord_6899939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899939).length < 2 ^ (prefixWord ++ tailWord_6899939).sum := by decide
  have hdescent : baseEnd_6899939 < baseStart_6899939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899947 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_6899947 : Nat := 118140960795 + 6899947 * 2 ^ 59
def prefixEnd_6899947 : Nat := 4983230072969 + 3 ^ 40 * 6899947 * 2
def baseEnd_6899947 : Nat := 3542989301548420659330227

theorem tailTrace_6899947 : CollatzResearch.WordTrace tailWord_6899947 prefixEnd_6899947 3542989301548420659330227 := by
  unfold tailWord_6899947
  simp only [CollatzResearch.WordTrace]
  refine ⟨251661741933677910974130095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167774494622451940649420063 251661741933677910974130095)
  ·
    refine ⟨377492612900516866461195143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251661741933677910974130095 377492612900516866461195143)
    ·
      refine ⟨566238919350775299691792715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377492612900516866461195143 566238919350775299691792715)
      ·
        refine ⟨849358379026162949537689073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566238919350775299691792715 849358379026162949537689073)
        ·
          refine ⟨637018784269622212153266805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849358379026162949537689073 637018784269622212153266805)
          ·
            refine ⟨59720511025277082389368763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 637018784269622212153266805 59720511025277082389368763)
            ·
              refine ⟨89580766537915623584053145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59720511025277082389368763 89580766537915623584053145)
              ·
                refine ⟨67185574903436717688039859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89580766537915623584053145 67185574903436717688039859)
                ·
                  refine ⟨100778362355155076532059789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67185574903436717688039859 100778362355155076532059789)
                  ·
                    refine ⟨37791885883183153699522421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100778362355155076532059789 37791885883183153699522421)
                    ·
                      refine ⟨3542989301548420659330227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37791885883183153699522421 3542989301548420659330227)
                      ·
                        rfl

theorem cell23_6899947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_6899947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899947 prefixEnd_6899947 := by exact prefixLift 6899947
  have htrace : WordTrace (prefixWord ++ tailWord_6899947) baseStart_6899947 baseEnd_6899947 := by
    simpa [prefixWord, tailWord_6899947, baseEnd_6899947] using wordTrace_append hprefix tailTrace_6899947
  have hstable : (prefixWord ++ tailWord_6899947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899947).length < 2 ^ (prefixWord ++ tailWord_6899947).sum := by decide
  have hdescent : baseEnd_6899947 < baseStart_6899947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899961 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 6, 2, 2]
def baseStart_6899961 : Nat := 118140960795 + 6899961 * 2 ^ 59
def prefixEnd_6899961 : Nat := 4983230072969 + 3 ^ 40 * 6899961 * 2
def baseEnd_6899961 : Nat := 3542996490277583604555163

theorem tailTrace_6899961 : CollatzResearch.WordTrace tailWord_6899961 prefixEnd_6899961 3542996490277583604555163 := by
  unfold tailWord_6899961
  simp only [CollatzResearch.WordTrace]
  refine ⟨251662252555627191365139737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167774835037084794243426491 251662252555627191365139737)
  ·
    refine ⟨188746689416720393523854803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251662252555627191365139737 188746689416720393523854803)
    ·
      refine ⟨283120034125080590285782205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188746689416720393523854803 283120034125080590285782205)
      ·
        refine ⟨106170012796905221357168327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283120034125080590285782205 106170012796905221357168327)
        ·
          refine ⟨159255019195357832035752491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106170012796905221357168327 159255019195357832035752491)
          ·
            refine ⟨238882528793036748053628737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159255019195357832035752491 238882528793036748053628737)
            ·
              refine ⟨179161896594777561040221553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238882528793036748053628737 179161896594777561040221553)
              ·
                refine ⟨134371422446083170780166165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179161896594777561040221553 134371422446083170780166165)
                ·
                  refine ⟨6298660427160148630320289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134371422446083170780166165 6298660427160148630320289)
                  ·
                    refine ⟨4723995320370111472740217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298660427160148630320289 4723995320370111472740217)
                    ·
                      refine ⟨3542996490277583604555163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4723995320370111472740217 3542996490277583604555163)
                      ·
                        rfl

theorem cell23_6899961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_6899961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899961 prefixEnd_6899961 := by exact prefixLift 6899961
  have htrace : WordTrace (prefixWord ++ tailWord_6899961) baseStart_6899961 baseEnd_6899961 := by
    simpa [prefixWord, tailWord_6899961, baseEnd_6899961] using wordTrace_append hprefix tailTrace_6899961
  have hstable : (prefixWord ++ tailWord_6899961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899961).length < 2 ^ (prefixWord ++ tailWord_6899961).sum := by decide
  have hdescent : baseEnd_6899961 < baseStart_6899961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899964 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_6899964 : Nat := 118140960795 + 6899964 * 2 ^ 59
def prefixEnd_6899964 : Nat := 4983230072969 + 3 ^ 40 * 6899964 * 2
def baseEnd_6899964 : Nat := 3542998030719547092817649

theorem tailTrace_6899964 : CollatzResearch.WordTrace tailWord_6899964 prefixEnd_6899964 3542998030719547092817649 := by
  unfold tailWord_6899964
  simp only [CollatzResearch.WordTrace]
  refine ⟨125831180987308161438749473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167774907983077548584999297 125831180987308161438749473)
  ·
    refine ⟨94373385740481121079062105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125831180987308161438749473 94373385740481121079062105)
    ·
      refine ⟨70780039305360840809296579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94373385740481121079062105 70780039305360840809296579)
      ·
        refine ⟨106170058958041261213944869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70780039305360840809296579 106170058958041261213944869)
        ·
          refine ⟨19906886054632736477614663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106170058958041261213944869 19906886054632736477614663)
          ·
            refine ⟨29860329081949104716421995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19906886054632736477614663 29860329081949104716421995)
            ·
              refine ⟨44790493622923657074632993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29860329081949104716421995 44790493622923657074632993)
              ·
                refine ⟨33592870217192742805974745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44790493622923657074632993 33592870217192742805974745)
                ·
                  refine ⟨25194652662894557104481059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33592870217192742805974745 25194652662894557104481059)
                  ·
                    refine ⟨37791978994341835656721589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25194652662894557104481059 37791978994341835656721589)
                    ·
                      refine ⟨3542998030719547092817649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37791978994341835656721589 3542998030719547092817649)
                      ·
                        rfl

theorem cell23_6899964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_6899964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899964 prefixEnd_6899964 := by exact prefixLift 6899964
  have htrace : WordTrace (prefixWord ++ tailWord_6899964) baseStart_6899964 baseEnd_6899964 := by
    simpa [prefixWord, tailWord_6899964, baseEnd_6899964] using wordTrace_append hprefix tailTrace_6899964
  have hstable : (prefixWord ++ tailWord_6899964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899964).length < 2 ^ (prefixWord ++ tailWord_6899964).sum := by decide
  have hdescent : baseEnd_6899964 < baseStart_6899964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899967 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 9]
def baseStart_6899967 : Nat := 118140960795 + 6899967 * 2 ^ 59
def prefixEnd_6899967 : Nat := 4983230072969 + 3 ^ 40 * 6899967 * 2
def baseEnd_6899967 : Nat := 393666619017945620120015

theorem tailTrace_6899967 : CollatzResearch.WordTrace tailWord_6899967 prefixEnd_6899967 393666619017945620120015 := by
  unfold tailWord_6899967
  simp only [CollatzResearch.WordTrace]
  refine ⟨251662471393605454389858155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167774980929070302926572103 251662471393605454389858155)
  ·
    refine ⟨377493707090408181584787233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251662471393605454389858155 377493707090408181584787233)
    ·
      refine ⟨283120280317806136188590425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377493707090408181584787233 283120280317806136188590425)
      ·
        refine ⟨212340210238354602141442819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283120280317806136188590425 212340210238354602141442819)
        ·
          refine ⟨318510315357531903212164229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212340210238354602141442819 318510315357531903212164229)
          ·
            refine ⟨59720684129537231852280793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318510315357531903212164229 59720684129537231852280793)
            ·
              refine ⟨44790513097152923889210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59720684129537231852280793 44790513097152923889210595)
              ·
                refine ⟨67185769645729385833815893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44790513097152923889210595 67185769645729385833815893)
                ·
                  refine ⟨393666619017945620120015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67185769645729385833815893 393666619017945620120015)
                  ·
                    rfl

theorem cell23_6899967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 9].length) (baseStart_6899967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899967 prefixEnd_6899967 := by exact prefixLift 6899967
  have htrace : WordTrace (prefixWord ++ tailWord_6899967) baseStart_6899967 baseEnd_6899967 := by
    simpa [prefixWord, tailWord_6899967, baseEnd_6899967] using wordTrace_append hprefix tailTrace_6899967
  have hstable : (prefixWord ++ tailWord_6899967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899967).length < 2 ^ (prefixWord ++ tailWord_6899967).sum := by decide
  have hdescent : baseEnd_6899967 < baseStart_6899967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6899998 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6899998 : Nat := 118140960795 + 6899998 * 2 ^ 59
def prefixEnd_6899998 : Nat := 4983230072969 + 3 ^ 40 * 6899998 * 2
def baseEnd_6899998 : Nat := 3543015489061799959792493

theorem tailTrace_6899998 : CollatzResearch.WordTrace tailWord_6899998 prefixEnd_6899998 3543015489061799959792493 := by
  unfold tailWord_6899998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457950257061643335529581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167775734704328764456157765 31457950257061643335529581)
  ·
    refine ⟨11796731346398116250823593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31457950257061643335529581 11796731346398116250823593)
    ·
      refine ⟨8847548509798587188117695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11796731346398116250823593 8847548509798587188117695)
      ·
        refine ⟨13271322764697880782176543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8847548509798587188117695 13271322764697880782176543)
        ·
          refine ⟨19906984147046821173264815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13271322764697880782176543 19906984147046821173264815)
          ·
            refine ⟨29860476220570231759897223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19906984147046821173264815 29860476220570231759897223)
            ·
              refine ⟨44790714330855347639845835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29860476220570231759897223 44790714330855347639845835)
              ·
                refine ⟨67186071496283021459768753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44790714330855347639845835 67186071496283021459768753)
                ·
                  refine ⟨50389553622212266094826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67186071496283021459768753 50389553622212266094826565)
                  ·
                    refine ⟨9448041304164799892779981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50389553622212266094826565 9448041304164799892779981)
                    ·
                      refine ⟨3543015489061799959792493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448041304164799892779981 3543015489061799959792493)
                      ·
                        rfl

theorem cell23_6899998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6899998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6899998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6899998 prefixEnd_6899998 := by exact prefixLift 6899998
  have htrace : WordTrace (prefixWord ++ tailWord_6899998) baseStart_6899998 baseEnd_6899998 := by
    simpa [prefixWord, tailWord_6899998, baseEnd_6899998] using wordTrace_append hprefix tailTrace_6899998
  have hstable : (prefixWord ++ tailWord_6899998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6899998).length < 2 ^ (prefixWord ++ tailWord_6899998).sum := by decide
  have hdescent : baseEnd_6899998 < baseStart_6899998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6899998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900021 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_6900021 : Nat := 118140960795 + 6900021 * 2 ^ 59
def prefixEnd_6900021 : Nat := 4983230072969 + 3 ^ 40 * 6900021 * 2
def baseEnd_6900021 : Nat := 3543027299116853369804887

theorem tailTrace_6900021 : CollatzResearch.WordTrace tailWord_6900021 prefixEnd_6900021 3543027299116853369804887 := by
  unfold tailWord_6900021
  simp only [CollatzResearch.WordTrace]
  refine ⟨251664440935409821612323917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167776293956939881074882611 251664440935409821612323917)
  ·
    refine ⟨94374165350778683104621469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251664440935409821612323917 94374165350778683104621469)
    ·
      refine ⟨35390312006542006164233051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94374165350778683104621469 35390312006542006164233051)
      ·
        refine ⟨53085468009813009246349577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35390312006542006164233051 53085468009813009246349577)
        ·
          refine ⟨39814101007359756934762183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53085468009813009246349577 39814101007359756934762183)
          ·
            refine ⟨59721151511039635402143275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39814101007359756934762183 59721151511039635402143275)
            ·
              refine ⟨89581727266559453103214913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59721151511039635402143275 89581727266559453103214913)
              ·
                refine ⟨67186295449919589827411185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89581727266559453103214913 67186295449919589827411185)
                ·
                  refine ⟨50389721587439692370558389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67186295449919589827411185 50389721587439692370558389)
                  ·
                    refine ⟨4724036398822471159739849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50389721587439692370558389 4724036398822471159739849)
                    ·
                      refine ⟨3543027299116853369804887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724036398822471159739849 3543027299116853369804887)
                      ·
                        rfl

theorem cell23_6900021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_6900021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900021 prefixEnd_6900021 := by exact prefixLift 6900021
  have htrace : WordTrace (prefixWord ++ tailWord_6900021) baseStart_6900021 baseEnd_6900021 := by
    simpa [prefixWord, tailWord_6900021, baseEnd_6900021] using wordTrace_append hprefix tailTrace_6900021
  have hstable : (prefixWord ++ tailWord_6900021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900021).length < 2 ^ (prefixWord ++ tailWord_6900021).sum := by decide
  have hdescent : baseEnd_6900021 < baseStart_6900021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900071 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_6900071 : Nat := 118140960795 + 6900071 * 2 ^ 59
def prefixEnd_6900071 : Nat := 4983230072969 + 3 ^ 40 * 6900071 * 2
def baseEnd_6900071 : Nat := 3543052973149578174179657

theorem tailTrace_6900071 : CollatzResearch.WordTrace tailWord_6900071 prefixEnd_6900071 3543052973149578174179657 := by
  unfold tailWord_6900071
  simp only [CollatzResearch.WordTrace]
  refine ⟨251666264585228680151644067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167777509723485786767762711 251666264585228680151644067)
  ·
    refine ⟨377499396877843020227466101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251666264585228680151644067 377499396877843020227466101)
    ·
      refine ⟨35390568457297783146324947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 377499396877843020227466101 35390568457297783146324947)
      ·
        refine ⟨53085852685946674719487421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35390568457297783146324947 53085852685946674719487421)
        ·
          refine ⟨19907194757230003019807783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53085852685946674719487421 19907194757230003019807783)
          ·
            refine ⟨29860792135845004529711675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19907194757230003019807783 29860792135845004529711675)
            ·
              refine ⟨44791188203767506794567513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29860792135845004529711675 44791188203767506794567513)
              ·
                refine ⟨33593391152825630095925635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44791188203767506794567513 33593391152825630095925635)
                ·
                  refine ⟨50390086729238445143888453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33593391152825630095925635 50390086729238445143888453)
                  ·
                    refine ⟨9448141261732208464479085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50390086729238445143888453 9448141261732208464479085)
                    ·
                      refine ⟨3543052973149578174179657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448141261732208464479085 3543052973149578174179657)
                      ·
                        rfl

theorem cell23_6900071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_6900071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900071 prefixEnd_6900071 := by exact prefixLift 6900071
  have htrace : WordTrace (prefixWord ++ tailWord_6900071) baseStart_6900071 baseEnd_6900071 := by
    simpa [prefixWord, tailWord_6900071, baseEnd_6900071] using wordTrace_append hprefix tailTrace_6900071
  have hstable : (prefixWord ++ tailWord_6900071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900071).length < 2 ^ (prefixWord ++ tailWord_6900071).sum := by decide
  have hdescent : baseEnd_6900071 < baseStart_6900071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900125 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 6]
def baseStart_6900125 : Nat := 118140960795 + 6900125 * 2 ^ 59
def prefixEnd_6900125 : Nat := 4983230072969 + 3 ^ 40 * 6900125 * 2
def baseEnd_6900125 : Nat := 393675633456102329211601

theorem tailTrace_6900125 : CollatzResearch.WordTrace tailWord_6900125 prefixEnd_6900125 393675633456102329211601 := by
  unfold tailWord_6900125
  simp only [CollatzResearch.WordTrace]
  refine ⟨251668234127033047374109829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167778822751355364916073219 251668234127033047374109829)
  ·
    refine ⟨47187793898818696382645593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251668234127033047374109829 47187793898818696382645593)
    ·
      refine ⟨35390845424114022286984195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47187793898818696382645593 35390845424114022286984195)
      ·
        refine ⟨53086268136171033430476293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35390845424114022286984195 53086268136171033430476293)
        ·
          refine ⟨9953675275532068768214305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53086268136171033430476293 9953675275532068768214305)
          ·
            refine ⟨7465256456649051576160729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9953675275532068768214305 7465256456649051576160729)
            ·
              refine ⟨5598942342486788682120547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465256456649051576160729 5598942342486788682120547)
              ·
                refine ⟨8398413513730183023180821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598942342486788682120547 8398413513730183023180821)
                ·
                  refine ⟨393675633456102329211601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8398413513730183023180821 393675633456102329211601)
                  ·
                    rfl

theorem cell23_6900125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_6900125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900125 prefixEnd_6900125 := by exact prefixLift 6900125
  have htrace : WordTrace (prefixWord ++ tailWord_6900125) baseStart_6900125 baseEnd_6900125 := by
    simpa [prefixWord, tailWord_6900125, baseEnd_6900125] using wordTrace_append hprefix tailTrace_6900125
  have hstable : (prefixWord ++ tailWord_6900125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900125).length < 2 ^ (prefixWord ++ tailWord_6900125).sum := by decide
  have hdescent : baseEnd_6900125 < baseStart_6900125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900145 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_6900145 : Nat := 118140960795 + 6900145 * 2 ^ 59
def prefixEnd_6900145 : Nat := 4983230072969 + 3 ^ 40 * 6900145 * 2
def baseEnd_6900145 : Nat := 3543090970718010884654317

theorem tailTrace_6900145 : CollatzResearch.WordTrace tailWord_6900145 prefixEnd_6900145 3543090970718010884654317 := by
  unfold tailWord_6900145
  simp only [CollatzResearch.WordTrace]
  refine ⟨251668963586960590789837889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167779309057973727193225259 251668963586960590789837889)
  ·
    refine ⟨188751722690220443092378417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251668963586960590789837889 188751722690220443092378417)
    ·
      refine ⟨141563792017665332319283813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188751722690220443092378417 141563792017665332319283813)
      ·
        refine ⟨26543211003312249809865715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141563792017665332319283813 26543211003312249809865715)
        ·
          refine ⟨39814816504968374714798573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26543211003312249809865715 39814816504968374714798573)
          ·
            refine ⟨14930556189363140518049465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39814816504968374714798573 14930556189363140518049465)
            ·
              refine ⟨11197917142022355388537099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14930556189363140518049465 11197917142022355388537099)
              ·
                refine ⟨16796875713033533082805649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197917142022355388537099 16796875713033533082805649)
                ·
                  refine ⟨12597656784775149812104237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16796875713033533082805649 12597656784775149812104237)
                  ·
                    refine ⟨4724121294290681179539089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12597656784775149812104237 4724121294290681179539089)
                    ·
                      refine ⟨3543090970718010884654317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724121294290681179539089 3543090970718010884654317)
                      ·
                        rfl

theorem cell23_6900145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_6900145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900145 prefixEnd_6900145 := by exact prefixLift 6900145
  have htrace : WordTrace (prefixWord ++ tailWord_6900145) baseStart_6900145 baseEnd_6900145 := by
    simpa [prefixWord, tailWord_6900145, baseEnd_6900145] using wordTrace_append hprefix tailTrace_6900145
  have hstable : (prefixWord ++ tailWord_6900145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900145).length < 2 ^ (prefixWord ++ tailWord_6900145).sum := by decide
  have hdescent : baseEnd_6900145 < baseStart_6900145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900151 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 1, 6]
def baseStart_6900151 : Nat := 118140960795 + 6900151 * 2 ^ 59
def prefixEnd_6900151 : Nat := 4983230072969 + 3 ^ 40 * 6900151 * 2
def baseEnd_6900151 : Nat := 1181031350533979287059763

theorem tailTrace_6900151 : CollatzResearch.WordTrace tailWord_6900151 prefixEnd_6900151 1181031350533979287059763 := by
  unfold tailWord_6900151
  simp only [CollatzResearch.WordTrace]
  refine ⟨251669182424938853814556307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167779454949959235876370871 251669182424938853814556307)
  ·
    refine ⟨377503773637408280721834461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251669182424938853814556307 377503773637408280721834461)
    ·
      refine ⟨141563915114028105270687923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377503773637408280721834461 141563915114028105270687923)
      ·
        refine ⟨212345872671042157906031885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141563915114028105270687923 212345872671042157906031885)
        ·
          refine ⟨79629702251640809214761957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212345872671042157906031885 79629702251640809214761957)
          ·
            refine ⟨14930569172182651727767867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79629702251640809214761957 14930569172182651727767867)
            ·
              refine ⟨22395853758273977591651801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14930569172182651727767867 22395853758273977591651801)
              ·
                refine ⟨16796890318705483193738851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22395853758273977591651801 16796890318705483193738851)
                ·
                  refine ⟨25195335478058224790608277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16796890318705483193738851 25195335478058224790608277)
                  ·
                    refine ⟨1181031350533979287059763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25195335478058224790608277 1181031350533979287059763)
                    ·
                      rfl

theorem cell23_6900151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_6900151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900151 prefixEnd_6900151 := by exact prefixLift 6900151
  have htrace : WordTrace (prefixWord ++ tailWord_6900151) baseStart_6900151 baseEnd_6900151 := by
    simpa [prefixWord, tailWord_6900151, baseEnd_6900151] using wordTrace_append hprefix tailTrace_6900151
  have hstable : (prefixWord ++ tailWord_6900151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900151).length < 2 ^ (prefixWord ++ tailWord_6900151).sum := by decide
  have hdescent : baseEnd_6900151 < baseStart_6900151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900158 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_6900158 : Nat := 118140960795 + 6900158 * 2 ^ 59
def prefixEnd_6900158 : Nat := 4983230072969 + 3 ^ 40 * 6900158 * 2
def baseEnd_6900158 : Nat := 3543097645966519333791757

theorem tailTrace_6900158 : CollatzResearch.WordTrace tailWord_6900158 prefixEnd_6900158 3543097645966519333791757 := by
  unfold tailWord_6900158
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458679716989186751257641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167779625157275662673374085 31458679716989186751257641)
  ·
    refine ⟨23594009787741890063443231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31458679716989186751257641 23594009787741890063443231)
    ·
      refine ⟨35391014681612835095164847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23594009787741890063443231 35391014681612835095164847)
      ·
        refine ⟨53086522022419252642747271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35391014681612835095164847 53086522022419252642747271)
        ·
          refine ⟨79629783033628878964120907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53086522022419252642747271 79629783033628878964120907)
          ·
            refine ⟨119444674550443318446181361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79629783033628878964120907 119444674550443318446181361)
            ·
              refine ⟨89583505912832488834636021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119444674550443318446181361 89583505912832488834636021)
              ·
                refine ⟨8398453679328045828247127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89583505912832488834636021 8398453679328045828247127)
                ·
                  refine ⟨12597680518992068742370691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398453679328045828247127 12597680518992068742370691)
                  ·
                    refine ⟨18896520778488103113556037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12597680518992068742370691 18896520778488103113556037)
                    ·
                      refine ⟨3543097645966519333791757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18896520778488103113556037 3543097645966519333791757)
                      ·
                        rfl

theorem cell23_6900158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_6900158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900158 prefixEnd_6900158 := by exact prefixLift 6900158
  have htrace : WordTrace (prefixWord ++ tailWord_6900158) baseStart_6900158 baseEnd_6900158 := by
    simpa [prefixWord, tailWord_6900158, baseEnd_6900158] using wordTrace_append hprefix tailTrace_6900158
  have hstable : (prefixWord ++ tailWord_6900158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900158).length < 2 ^ (prefixWord ++ tailWord_6900158).sum := by decide
  have hdescent : baseEnd_6900158 < baseStart_6900158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900168 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_6900168 : Nat := 118140960795 + 6900168 * 2 ^ 59
def prefixEnd_6900168 : Nat := 4983230072969 + 3 ^ 40 * 6900168 * 2
def baseEnd_6900168 : Nat := 1181034260257688098222237

theorem tailTrace_6900168 : CollatzResearch.WordTrace tailWord_6900168 prefixEnd_6900168 1181034260257688098222237 := by
  unfold tailWord_6900168
  simp only [CollatzResearch.WordTrace]
  refine ⟨125834901232938632858962579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167779868310584843811950105 125834901232938632858962579)
  ·
    refine ⟨188752351849407949288443869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125834901232938632858962579 188752351849407949288443869)
    ·
      refine ⟨70782131943527980983166451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188752351849407949288443869 70782131943527980983166451)
      ·
        refine ⟨106173197915291971474749677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70782131943527980983166451 106173197915291971474749677)
        ·
          refine ⟨39814949218234489303031129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106173197915291971474749677 39814949218234489303031129)
          ·
            refine ⟨29861211913675866977273347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39814949218234489303031129 29861211913675866977273347)
            ·
              refine ⟨44791817870513800465910021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29861211913675866977273347 44791817870513800465910021)
              ·
                refine ⟨8398465850721337587358129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44791817870513800465910021 8398465850721337587358129)
                ·
                  refine ⟨6298849388041003190518597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8398465850721337587358129 6298849388041003190518597)
                  ·
                    refine ⟨1181034260257688098222237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6298849388041003190518597 1181034260257688098222237)
                    ·
                      rfl

theorem cell23_6900168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_6900168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900168 prefixEnd_6900168 := by exact prefixLift 6900168
  have htrace : WordTrace (prefixWord ++ tailWord_6900168) baseStart_6900168 baseEnd_6900168 := by
    simpa [prefixWord, tailWord_6900168, baseEnd_6900168] using wordTrace_append hprefix tailTrace_6900168
  have hstable : (prefixWord ++ tailWord_6900168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900168).length < 2 ^ (prefixWord ++ tailWord_6900168).sum := by decide
  have hdescent : baseEnd_6900168 < baseStart_6900168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900181 : List Nat := [1, 3, 2, 3, 1, 2, 3, 8]
def baseStart_6900181 : Nat := 118140960795 + 6900181 * 2 ^ 59
def prefixEnd_6900181 : Nat := 4983230072969 + 3 ^ 40 * 6900181 * 2
def baseEnd_6900181 : Nat := 131226276148947138659413

theorem tailTrace_6900181 : CollatzResearch.WordTrace tailWord_6900181 prefixEnd_6900181 131226276148947138659413 := by
  unfold tailWord_6900181
  simp only [CollatzResearch.WordTrace]
  refine ⟨251670276614830168938148397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167780184409886779292098931 251670276614830168938148397)
  ·
    refine ⟨94376353730561313351805649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251670276614830168938148397 94376353730561313351805649)
    ·
      refine ⟨70782265297920985013854237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94376353730561313351805649 70782265297920985013854237)
      ·
        refine ⟨26543349486720369380195339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70782265297920985013854237 26543349486720369380195339)
        ·
          refine ⟨39815024230080554070293009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26543349486720369380195339 39815024230080554070293009)
          ·
            refine ⟨29861268172560415552719757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39815024230080554070293009 29861268172560415552719757)
            ·
              refine ⟨11197975564710155832269909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29861268172560415552719757 11197975564710155832269909)
              ·
                refine ⟨131226276148947138659413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11197975564710155832269909 131226276148947138659413)
                ·
                  rfl

theorem cell23_6900181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 8].length) (baseStart_6900181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900181 prefixEnd_6900181 := by exact prefixLift 6900181
  have htrace : WordTrace (prefixWord ++ tailWord_6900181) baseStart_6900181 baseEnd_6900181 := by
    simpa [prefixWord, tailWord_6900181, baseEnd_6900181] using wordTrace_append hprefix tailTrace_6900181
  have hstable : (prefixWord ++ tailWord_6900181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900181).length < 2 ^ (prefixWord ++ tailWord_6900181).sum := by decide
  have hdescent : baseEnd_6900181 < baseStart_6900181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900208 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3]
def baseStart_6900208 : Nat := 118140960795 + 6900208 * 2 ^ 59
def prefixEnd_6900208 : Nat := 4983230072969 + 3 ^ 40 * 6900208 * 2
def baseEnd_6900208 : Nat := 3543123319999244138166527

theorem tailTrace_6900208 : CollatzResearch.WordTrace tailWord_6900208 prefixEnd_6900208 3543123319999244138166527 := by
  unfold tailWord_6900208
  simp only [CollatzResearch.WordTrace]
  refine ⟨125835630692866176274690639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167780840923821568366254185 125835630692866176274690639)
  ·
    refine ⟨188753446039299264412035959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125835630692866176274690639 188753446039299264412035959)
    ·
      refine ⟨283130169058948896618053939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188753446039299264412035959 283130169058948896618053939)
      ·
        refine ⟨424695253588423344927080909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283130169058948896618053939 424695253588423344927080909)
        ·
          refine ⟨159260720095658754347655341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424695253588423344927080909 159260720095658754347655341)
          ·
            refine ⟨59722770035872032880370753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159260720095658754347655341 59722770035872032880370753)
            ·
              refine ⟨44792077526904024660278065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59722770035872032880370753 44792077526904024660278065)
              ·
                refine ⟨33594058145178018495208549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44792077526904024660278065 33594058145178018495208549)
                ·
                  refine ⟨6298885902220878467851603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33594058145178018495208549 6298885902220878467851603)
                  ·
                    refine ⟨9448328853331317701777405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6298885902220878467851603 9448328853331317701777405)
                    ·
                      refine ⟨3543123319999244138166527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448328853331317701777405 3543123319999244138166527)
                      ·
                        rfl

theorem cell23_6900208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_6900208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900208 prefixEnd_6900208 := by exact prefixLift 6900208
  have htrace : WordTrace (prefixWord ++ tailWord_6900208) baseStart_6900208 baseEnd_6900208 := by
    simpa [prefixWord, tailWord_6900208, baseEnd_6900208] using wordTrace_append hprefix tailTrace_6900208
  have hstable : (prefixWord ++ tailWord_6900208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900208).length < 2 ^ (prefixWord ++ tailWord_6900208).sum := by decide
  have hdescent : baseEnd_6900208 < baseStart_6900208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900218 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_6900218 : Nat := 118140960795 + 6900218 * 2 ^ 59
def prefixEnd_6900218 : Nat := 4983230072969 + 3 ^ 40 * 6900218 * 2
def baseEnd_6900218 : Nat := 3543128454805789099041481

theorem tailTrace_6900218 : CollatzResearch.WordTrace tailWord_6900218 prefixEnd_6900218 3543128454805789099041481 := by
  unfold tailWord_6900218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62917906528924031064311327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167781084077130749504830205 62917906528924031064311327)
  ·
    refine ⟨94376859793386046596466991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62917906528924031064311327 94376859793386046596466991)
    ·
      refine ⟨141565289690079069894700487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94376859793386046596466991 141565289690079069894700487)
      ·
        refine ⟨212347934535118604842050731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141565289690079069894700487 212347934535118604842050731)
        ·
          refine ⟨318521901802677907263076097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212347934535118604842050731 318521901802677907263076097)
          ·
            refine ⟨238891426352008430447307073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318521901802677907263076097 238891426352008430447307073)
            ·
              refine ⟨179168569764006322835480305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238891426352008430447307073 179168569764006322835480305)
              ·
                refine ⟨134376427323004742126610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179168569764006322835480305 134376427323004742126610229)
                ·
                  refine ⟨12597790061531694574369709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134376427323004742126610229 12597790061531694574369709)
                  ·
                    refine ⟨4724171273074385465388641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12597790061531694574369709 4724171273074385465388641)
                    ·
                      refine ⟨3543128454805789099041481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724171273074385465388641 3543128454805789099041481)
                      ·
                        rfl

theorem cell23_6900218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_6900218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900218 prefixEnd_6900218 := by exact prefixLift 6900218
  have htrace : WordTrace (prefixWord ++ tailWord_6900218) baseStart_6900218 baseEnd_6900218 := by
    simpa [prefixWord, tailWord_6900218, baseEnd_6900218] using wordTrace_append hprefix tailTrace_6900218
  have hstable : (prefixWord ++ tailWord_6900218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900218).length < 2 ^ (prefixWord ++ tailWord_6900218).sum := by decide
  have hdescent : baseEnd_6900218 < baseStart_6900218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900225 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_6900225 : Nat := 118140960795 + 6900225 * 2 ^ 59
def prefixEnd_6900225 : Nat := 4983230072969 + 3 ^ 40 * 6900225 * 2
def baseEnd_6900225 : Nat := 3543132049170370571653949

theorem tailTrace_6900225 : CollatzResearch.WordTrace tailWord_6900225 prefixEnd_6900225 3543132049170370571653949 := by
  unfold tailWord_6900225
  simp only [CollatzResearch.WordTrace]
  refine ⟨251671881426670764452750129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167781254284447176301833419 251671881426670764452750129)
  ·
    refine ⟨188753911070003073339562597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251671881426670764452750129 188753911070003073339562597)
    ·
      refine ⟨35391358325625576251167987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188753911070003073339562597 35391358325625576251167987)
      ·
        refine ⟨53087037488438364376751981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35391358325625576251167987 53087037488438364376751981)
        ·
          refine ⟨19907639058164386641281993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53087037488438364376751981 19907639058164386641281993)
          ·
            refine ⟨14930729293623289980961495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19907639058164386641281993 14930729293623289980961495)
            ·
              refine ⟨22396093940434934971442243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14930729293623289980961495 22396093940434934971442243)
              ·
                refine ⟨33594140910652402457163365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22396093940434934971442243 33594140910652402457163365)
                ·
                  refine ⟨6298901420747325460718131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33594140910652402457163365 6298901420747325460718131)
                  ·
                    refine ⟨9448352131120988191077197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6298901420747325460718131 9448352131120988191077197)
                    ·
                      refine ⟨3543132049170370571653949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448352131120988191077197 3543132049170370571653949)
                      ·
                        rfl

theorem cell23_6900225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_6900225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900225 prefixEnd_6900225 := by exact prefixLift 6900225
  have htrace : WordTrace (prefixWord ++ tailWord_6900225) baseStart_6900225 baseEnd_6900225 := by
    simpa [prefixWord, tailWord_6900225, baseEnd_6900225] using wordTrace_append hprefix tailTrace_6900225
  have hstable : (prefixWord ++ tailWord_6900225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900225).length < 2 ^ (prefixWord ++ tailWord_6900225).sum := by decide
  have hdescent : baseEnd_6900225 < baseStart_6900225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900252 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6900252 : Nat := 118140960795 + 6900252 * 2 ^ 59
def prefixEnd_6900252 : Nat := 4983230072969 + 3 ^ 40 * 6900252 * 2
def baseEnd_6900252 : Nat := 3543145913148041966016325

theorem tailTrace_6900252 : CollatzResearch.WordTrace tailWord_6900252 prefixEnd_6900252 3543145913148041966016325 := by
  unfold tailWord_6900252
  simp only [CollatzResearch.WordTrace]
  refine ⟨125836433098786474031991505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167781910798381965375988673 125836433098786474031991505)
  ·
    refine ⟨94377324824089855523993629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125836433098786474031991505 94377324824089855523993629)
    ·
      refine ⟨35391496809033695821497611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94377324824089855523993629 35391496809033695821497611)
      ·
        refine ⟨53087245213550543732246417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35391496809033695821497611 53087245213550543732246417)
        ·
          refine ⟨39815433910162907799184813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53087245213550543732246417 39815433910162907799184813)
          ·
            refine ⟨14930787716311090424694305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39815433910162907799184813 14930787716311090424694305)
            ·
              refine ⟨11198090787233317818520729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14930787716311090424694305 11198090787233317818520729)
              ·
                refine ⟨8398568090424988363890547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198090787233317818520729 8398568090424988363890547)
                ·
                  refine ⟨12597852135637482545835821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398568090424988363890547 12597852135637482545835821)
                  ·
                    refine ⟨4724194550864055954688433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12597852135637482545835821 4724194550864055954688433)
                    ·
                      refine ⟨3543145913148041966016325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724194550864055954688433 3543145913148041966016325)
                      ·
                        rfl

theorem cell23_6900252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6900252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900252 prefixEnd_6900252 := by exact prefixLift 6900252
  have htrace : WordTrace (prefixWord ++ tailWord_6900252) baseStart_6900252 baseEnd_6900252 := by
    simpa [prefixWord, tailWord_6900252, baseEnd_6900252] using wordTrace_append hprefix tailTrace_6900252
  have hstable : (prefixWord ++ tailWord_6900252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900252).length < 2 ^ (prefixWord ++ tailWord_6900252).sum := by decide
  have hdescent : baseEnd_6900252 < baseStart_6900252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900261 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_6900261 : Nat := 118140960795 + 6900261 * 2 ^ 59
def prefixEnd_6900261 : Nat := 4983230072969 + 3 ^ 40 * 6900261 * 2
def baseEnd_6900261 : Nat := 3543150534473932430803783

theorem tailTrace_6900261 : CollatzResearch.WordTrace tailWord_6900261 prefixEnd_6900261 3543150534473932430803783 := by
  unfold tailWord_6900261
  simp only [CollatzResearch.WordTrace]
  refine ⟨251673194454540342601060637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167782129636360228400707091 251673194454540342601060637)
  ·
    refine ⟨94377447920452628475397739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251673194454540342601060637 94377447920452628475397739)
    ·
      refine ⟨141566171880678942713096609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94377447920452628475397739 141566171880678942713096609)
      ·
        refine ⟨106174628910509207034822457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141566171880678942713096609 106174628910509207034822457)
        ·
          refine ⟨79630971682881905276116843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106174628910509207034822457 79630971682881905276116843)
          ·
            refine ⟨119446457524322857914175265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79630971682881905276116843 119446457524322857914175265)
            ·
              refine ⟨89584843143242143435631449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119446457524322857914175265 89584843143242143435631449)
              ·
                refine ⟨67188632357431607576723587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89584843143242143435631449 67188632357431607576723587)
                ·
                  refine ⟨100782948536147411365085381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67188632357431607576723587 100782948536147411365085381)
                  ·
                    refine ⟨18896802850527639630953509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100782948536147411365085381 18896802850527639630953509)
                    ·
                      refine ⟨3543150534473932430803783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18896802850527639630953509 3543150534473932430803783)
                      ·
                        rfl

theorem cell23_6900261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_6900261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900261 prefixEnd_6900261 := by exact prefixLift 6900261
  have htrace : WordTrace (prefixWord ++ tailWord_6900261) baseStart_6900261 baseEnd_6900261 := by
    simpa [prefixWord, tailWord_6900261, baseEnd_6900261] using wordTrace_append hprefix tailTrace_6900261
  have hstable : (prefixWord ++ tailWord_6900261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900261).length < 2 ^ (prefixWord ++ tailWord_6900261).sum := by decide
  have hdescent : baseEnd_6900261 < baseStart_6900261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900281 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6900281 : Nat := 118140960795 + 6900281 * 2 ^ 59
def prefixEnd_6900281 : Nat := 4983230072969 + 3 ^ 40 * 6900281 * 2
def baseEnd_6900281 : Nat := 3543160804087022352553691

theorem tailTrace_6900281 : CollatzResearch.WordTrace tailWord_6900281 prefixEnd_6900281 3543160804087022352553691 := by
  unfold tailWord_6900281
  simp only [CollatzResearch.WordTrace]
  refine ⟨251673923914467886016788697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167782615942978590677859131 251673923914467886016788697)
  ·
    refine ⟨188755442935850914512591523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251673923914467886016788697 188755442935850914512591523)
    ·
      refine ⟨283133164403776371768887285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188755442935850914512591523 283133164403776371768887285)
      ·
        refine ⟨26543734162854034853333183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283133164403776371768887285 26543734162854034853333183)
        ·
          refine ⟨39815601244281052279999775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26543734162854034853333183 39815601244281052279999775)
          ·
            refine ⟨59723401866421578419999663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39815601244281052279999775 59723401866421578419999663)
            ·
              refine ⟨89585102799632367629999495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59723401866421578419999663 89585102799632367629999495)
              ·
                refine ⟨134377654199448551444999243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89585102799632367629999495 134377654199448551444999243)
                ·
                  refine ⟨201566481299172827167498865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134377654199448551444999243 201566481299172827167498865)
                  ·
                    refine ⟨151174860974379620375624149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201566481299172827167498865 151174860974379620375624149)
                    ·
                      refine ⟨3543160804087022352553691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151174860974379620375624149 3543160804087022352553691)
                      ·
                        rfl

theorem cell23_6900281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6900281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900281 prefixEnd_6900281 := by exact prefixLift 6900281
  have htrace : WordTrace (prefixWord ++ tailWord_6900281) baseStart_6900281 baseEnd_6900281 := by
    simpa [prefixWord, tailWord_6900281, baseEnd_6900281] using wordTrace_append hprefix tailTrace_6900281
  have hstable : (prefixWord ++ tailWord_6900281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900281).length < 2 ^ (prefixWord ++ tailWord_6900281).sum := by decide
  have hdescent : baseEnd_6900281 < baseStart_6900281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900288 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 5]
def baseStart_6900288 : Nat := 118140960795 + 6900288 * 2 ^ 59
def prefixEnd_6900288 : Nat := 4983230072969 + 3 ^ 40 * 6900288 * 2
def baseEnd_6900288 : Nat := 393684933161289313907351

theorem tailTrace_6900288 : CollatzResearch.WordTrace tailWord_6900288 prefixEnd_6900288 393684933161289313907351 := by
  unfold tailWord_6900288
  simp only [CollatzResearch.WordTrace]
  refine ⟨125837089612721263106146759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167782786150295017474862345 125837089612721263106146759)
  ·
    refine ⟨188755634419081894659220139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125837089612721263106146759 188755634419081894659220139)
    ·
      refine ⟨283133451628622841988830209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188755634419081894659220139 283133451628622841988830209)
      ·
        refine ⟨212350088721467131491622657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283133451628622841988830209 212350088721467131491622657)
        ·
          refine ⟨159262566541100348618716993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212350088721467131491622657 159262566541100348618716993)
          ·
            refine ⟨119446924905825261464037745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159262566541100348618716993 119446924905825261464037745)
            ·
              refine ⟨89585193679368946098028309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119446924905825261464037745 89585193679368946098028309)
              ·
                refine ⟨4199305953720419348345077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89585193679368946098028309 4199305953720419348345077)
                ·
                  refine ⟨393684933161289313907351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4199305953720419348345077 393684933161289313907351)
                  ·
                    rfl

theorem cell23_6900288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 5].length) (baseStart_6900288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900288 prefixEnd_6900288 := by exact prefixLift 6900288
  have htrace : WordTrace (prefixWord ++ tailWord_6900288) baseStart_6900288 baseEnd_6900288 := by
    simpa [prefixWord, tailWord_6900288, baseEnd_6900288] using wordTrace_append hprefix tailTrace_6900288
  have hstable : (prefixWord ++ tailWord_6900288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900288).length < 2 ^ (prefixWord ++ tailWord_6900288).sum := by decide
  have hdescent : baseEnd_6900288 < baseStart_6900288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900311 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_6900311 : Nat := 118140960795 + 6900311 * 2 ^ 59
def prefixEnd_6900311 : Nat := 4983230072969 + 3 ^ 40 * 6900311 * 2
def baseEnd_6900311 : Nat := 3543176208506657235178553

theorem tailTrace_6900311 : CollatzResearch.WordTrace tailWord_6900311 prefixEnd_6900311 3543176208506657235178553 := by
  unfold tailWord_6900311
  simp only [CollatzResearch.WordTrace]
  refine ⟨251675018104359201140380787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167783345402906134093587191 251675018104359201140380787)
  ·
    refine ⟨377512527156538801710571181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251675018104359201140380787 377512527156538801710571181)
    ·
      refine ⟨141567197683702050641464193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377512527156538801710571181 141567197683702050641464193)
      ·
        refine ⟨106175398262776537981098145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141567197683702050641464193 106175398262776537981098145)
        ·
          refine ⟨79631548697082403485823609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106175398262776537981098145 79631548697082403485823609)
          ·
            refine ⟨59723661522811802614367707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79631548697082403485823609 59723661522811802614367707)
            ·
              refine ⟨89585492284217703921551561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59723661522811802614367707 89585492284217703921551561)
              ·
                refine ⟨67189119213163277941163671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89585492284217703921551561 67189119213163277941163671)
                ·
                  refine ⟨100783678819744916911745507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67189119213163277941163671 100783678819744916911745507)
                  ·
                    refine ⟨151175518229617375367618261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100783678819744916911745507 151175518229617375367618261)
                    ·
                      refine ⟨3543176208506657235178553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151175518229617375367618261 3543176208506657235178553)
                      ·
                        rfl

theorem cell23_6900311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_6900311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900311 prefixEnd_6900311 := by exact prefixLift 6900311
  have htrace : WordTrace (prefixWord ++ tailWord_6900311) baseStart_6900311 baseEnd_6900311 := by
    simpa [prefixWord, tailWord_6900311, baseEnd_6900311] using wordTrace_append hprefix tailTrace_6900311
  have hstable : (prefixWord ++ tailWord_6900311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900311).length < 2 ^ (prefixWord ++ tailWord_6900311).sum := by decide
  have hdescent : baseEnd_6900311 < baseStart_6900311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900351 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_6900351 : Nat := 118140960795 + 6900351 * 2 ^ 59
def prefixEnd_6900351 : Nat := 4983230072969 + 3 ^ 40 * 6900351 * 2
def baseEnd_6900351 : Nat := 3543196747732837078678369

theorem tailTrace_6900351 : CollatzResearch.WordTrace tailWord_6900351 prefixEnd_6900351 3543196747732837078678369 := by
  unfold tailWord_6900351
  simp only [CollatzResearch.WordTrace]
  refine ⟨251676477024214287971836907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167784318016142858647891271 251676477024214287971836907)
  ·
    refine ⟨377514715536321431957755361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251676477024214287971836907 377514715536321431957755361)
    ·
      refine ⟨283136036652241073968316521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377514715536321431957755361 283136036652241073968316521)
      ·
        refine ⟨212352027489180805476237391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283136036652241073968316521 212352027489180805476237391)
        ·
          refine ⟨318528041233771208214356087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212352027489180805476237391 318528041233771208214356087)
          ·
            refine ⟨477792061850656812321534131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318528041233771208214356087 477792061850656812321534131)
            ·
              refine ⟨716688092775985218482301197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477792061850656812321534131 716688092775985218482301197)
              ·
                refine ⟨268758034790994456930862949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716688092775985218482301197 268758034790994456930862949)
                ·
                  refine ⟨50392131523311460674536803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268758034790994456930862949 50392131523311460674536803)
                  ·
                    refine ⟨75588197284967191011805205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50392131523311460674536803 75588197284967191011805205)
                    ·
                      refine ⟨3543196747732837078678369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75588197284967191011805205 3543196747732837078678369)
                      ·
                        rfl

theorem cell23_6900351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_6900351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900351 prefixEnd_6900351 := by exact prefixLift 6900351
  have htrace : WordTrace (prefixWord ++ tailWord_6900351) baseStart_6900351 baseEnd_6900351 := by
    simpa [prefixWord, tailWord_6900351, baseEnd_6900351] using wordTrace_append hprefix tailTrace_6900351
  have hstable : (prefixWord ++ tailWord_6900351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900351).length < 2 ^ (prefixWord ++ tailWord_6900351).sum := by decide
  have hdescent : baseEnd_6900351 < baseStart_6900351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900361 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 10]
def baseStart_6900361 : Nat := 118140960795 + 6900361 * 2 ^ 59
def prefixEnd_6900361 : Nat := 4983230072969 + 3 ^ 40 * 6900361 * 2
def baseEnd_6900361 : Nat := 393689098059931337728147

theorem tailTrace_6900361 : CollatzResearch.WordTrace tailWord_6900361 prefixEnd_6900361 393689098059931337728147 := by
  unfold tailWord_6900361
  simp only [CollatzResearch.WordTrace]
  refine ⟨251676841754178059679700937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167784561169452039786467291 251676841754178059679700937)
  ·
    refine ⟨188757631315633544759775703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251676841754178059679700937 188757631315633544759775703)
    ·
      refine ⟨283136446973450317139663555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188757631315633544759775703 283136446973450317139663555)
      ·
        refine ⟨424704670460175475709495333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283136446973450317139663555 424704670460175475709495333)
        ·
          refine ⟨79632125711282901695530375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424704670460175475709495333 79632125711282901695530375)
          ·
            refine ⟨119448188566924352543295563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79632125711282901695530375 119448188566924352543295563)
            ·
              refine ⟨179172282850386528814943345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119448188566924352543295563 179172282850386528814943345)
              ·
                refine ⟨134379212137789896611207509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179172282850386528814943345 134379212137789896611207509)
                ·
                  refine ⟨393689098059931337728147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134379212137789896611207509 393689098059931337728147)
                  ·
                    rfl

theorem cell23_6900361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_6900361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900361 prefixEnd_6900361 := by exact prefixLift 6900361
  have htrace : WordTrace (prefixWord ++ tailWord_6900361) baseStart_6900361 baseEnd_6900361 := by
    simpa [prefixWord, tailWord_6900361, baseEnd_6900361] using wordTrace_append hprefix tailTrace_6900361
  have hstable : (prefixWord ++ tailWord_6900361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900361).length < 2 ^ (prefixWord ++ tailWord_6900361).sum := by decide
  have hdescent : baseEnd_6900361 < baseStart_6900361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900372 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6900372 : Nat := 118140960795 + 6900372 * 2 ^ 59
def prefixEnd_6900372 : Nat := 4983230072969 + 3 ^ 40 * 6900372 * 2
def baseEnd_6900372 : Nat := 3543207530826581496515773

theorem tailTrace_6900372 : CollatzResearch.WordTrace tailWord_6900372 prefixEnd_6900372 3543207530826581496515773 := by
  unfold tailWord_6900372
  simp only [CollatzResearch.WordTrace]
  refine ⟨125838621478569104279175685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167784828638092139038900913 125838621478569104279175685)
  ·
    refine ⟨23594741527231707052345441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125838621478569104279175685 23594741527231707052345441)
    ·
      refine ⟨17696056145423780289259081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23594741527231707052345441 17696056145423780289259081)
      ·
        refine ⟨13272042109067835216944311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17696056145423780289259081 13272042109067835216944311)
        ·
          refine ⟨19908063163601752825416467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13272042109067835216944311 19908063163601752825416467)
          ·
            refine ⟨29862094745402629238124701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19908063163601752825416467 29862094745402629238124701)
            ·
              refine ⟨11198285529525985964296763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29862094745402629238124701 11198285529525985964296763)
              ·
                refine ⟨16797428294288978946445145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198285529525985964296763 16797428294288978946445145)
                ·
                  refine ⟨12598071220716734209833859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16797428294288978946445145 12598071220716734209833859)
                  ·
                    refine ⟨18897106831075101314750789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12598071220716734209833859 18897106831075101314750789)
                    ·
                      refine ⟨3543207530826581496515773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18897106831075101314750789 3543207530826581496515773)
                      ·
                        rfl

theorem cell23_6900372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6900372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900372 prefixEnd_6900372 := by exact prefixLift 6900372
  have htrace : WordTrace (prefixWord ++ tailWord_6900372) baseStart_6900372 baseEnd_6900372 := by
    simpa [prefixWord, tailWord_6900372, baseEnd_6900372] using wordTrace_append hprefix tailTrace_6900372
  have hstable : (prefixWord ++ tailWord_6900372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900372).length < 2 ^ (prefixWord ++ tailWord_6900372).sum := by decide
  have hdescent : baseEnd_6900372 < baseStart_6900372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900415 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 5, 2]
def baseStart_6900415 : Nat := 118140960795 + 6900415 * 2 ^ 59
def prefixEnd_6900415 : Nat := 4983230072969 + 3 ^ 40 * 6900415 * 2
def baseEnd_6900415 : Nat := 3543229610494724828278075

theorem tailTrace_6900415 : CollatzResearch.WordTrace tailWord_6900415 prefixEnd_6900415 3543229610494724828278075 := by
  unfold tailWord_6900415
  simp only [CollatzResearch.WordTrace]
  refine ⟨251678811295982426902166699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167785874197321617934777799 251678811295982426902166699)
  ·
    refine ⟨377518216943973640353250049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251678811295982426902166699 377518216943973640353250049)
    ·
      refine ⟨283138662707980230264937537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377518216943973640353250049 283138662707980230264937537)
      ·
        refine ⟨212353997030985172698703153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283138662707980230264937537 212353997030985172698703153)
        ·
          refine ⟨159265497773238879524027365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212353997030985172698703153 159265497773238879524027365)
          ·
            refine ⟨29862280832482289910755131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159265497773238879524027365 29862280832482289910755131)
            ·
              refine ⟨44793421248723434866132697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29862280832482289910755131 44793421248723434866132697)
              ·
                refine ⟨33595065936542576149599523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44793421248723434866132697 33595065936542576149599523)
                ·
                  refine ⟨50392598904813864224399285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33595065936542576149599523 50392598904813864224399285)
                  ·
                    refine ⟨4724306147326299771037433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50392598904813864224399285 4724306147326299771037433)
                    ·
                      refine ⟨3543229610494724828278075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724306147326299771037433 3543229610494724828278075)
                      ·
                        rfl

theorem cell23_6900415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_6900415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900415 prefixEnd_6900415 := by exact prefixLift 6900415
  have htrace : WordTrace (prefixWord ++ tailWord_6900415) baseStart_6900415 baseEnd_6900415 := by
    simpa [prefixWord, tailWord_6900415, baseEnd_6900415] using wordTrace_append hprefix tailTrace_6900415
  have hstable : (prefixWord ++ tailWord_6900415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900415).length < 2 ^ (prefixWord ++ tailWord_6900415).sum := by decide
  have hdescent : baseEnd_6900415 < baseStart_6900415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900439 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 1, 1, 3]
def baseStart_6900439 : Nat := 118140960795 + 6900439 * 2 ^ 59
def prefixEnd_6900439 : Nat := 4983230072969 + 3 ^ 40 * 6900439 * 2
def baseEnd_6900439 : Nat := 3543241934030432734377965

theorem tailTrace_6900439 : CollatzResearch.WordTrace tailWord_6900439 prefixEnd_6900439 3543241934030432734377965 := by
  unfold tailWord_6900439
  simp only [CollatzResearch.WordTrace]
  refine ⟨251679686647895479001040371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167786457765263652667360247 251679686647895479001040371)
  ·
    refine ⟨377519529971843218501560557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251679686647895479001040371 377519529971843218501560557)
    ·
      refine ⟨141569823739441206938085209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377519529971843218501560557 141569823739441206938085209)
      ·
        refine ⟨106177367804580905203563907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141569823739441206938085209 106177367804580905203563907)
        ·
          refine ⟨159266051706871357805345861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106177367804580905203563907 159266051706871357805345861)
          ·
            refine ⟨29862384695038379588502349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159266051706871357805345861 29862384695038379588502349)
            ·
              refine ⟨11198394260639392345688381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29862384695038379588502349 11198394260639392345688381)
              ·
                refine ⟨4199397847739772129633143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11198394260639392345688381 4199397847739772129633143)
                ·
                  refine ⟨6299096771609658194449715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199397847739772129633143 6299096771609658194449715)
                  ·
                    refine ⟨9448645157414487291674573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6299096771609658194449715 9448645157414487291674573)
                    ·
                      refine ⟨3543241934030432734377965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448645157414487291674573 3543241934030432734377965)
                      ·
                        rfl

theorem cell23_6900439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_6900439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900439 prefixEnd_6900439 := by exact prefixLift 6900439
  have htrace : WordTrace (prefixWord ++ tailWord_6900439) baseStart_6900439 baseEnd_6900439 := by
    simpa [prefixWord, tailWord_6900439, baseEnd_6900439] using wordTrace_append hprefix tailTrace_6900439
  have hstable : (prefixWord ++ tailWord_6900439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900439).length < 2 ^ (prefixWord ++ tailWord_6900439).sum := by decide
  have hdescent : baseEnd_6900439 < baseStart_6900439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900456 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6900456 : Nat := 118140960795 + 6900456 * 2 ^ 59
def prefixEnd_6900456 : Nat := 4983230072969 + 3 ^ 40 * 6900456 * 2
def baseEnd_6900456 : Nat := 3543250663201559167865387

theorem tailTrace_6900456 : CollatzResearch.WordTrace tailWord_6900456 prefixEnd_6900456 3543250663201559167865387 := by
  unfold tailWord_6900456
  simp only [CollatzResearch.WordTrace]
  refine ⟨125840153344416945452204611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167786871125889260602939481 125840153344416945452204611)
  ·
    refine ⟨188760230016625418178306917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125840153344416945452204611 188760230016625418178306917)
    ·
      refine ⟨35392543128117265908432547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188760230016625418178306917 35392543128117265908432547)
      ·
        refine ⟨53088814692175898862648821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35392543128117265908432547 53088814692175898862648821)
        ·
          refine ⟨4977076377391490518373327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53088814692175898862648821 4977076377391490518373327)
          ·
            refine ⟨7465614566087235777559991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977076377391490518373327 7465614566087235777559991)
            ·
              refine ⟨11198421849130853666339987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465614566087235777559991 11198421849130853666339987)
              ·
                refine ⟨16797632773696280499509981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198421849130853666339987 16797632773696280499509981)
                ·
                  refine ⟨6299112290136105187316243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16797632773696280499509981 6299112290136105187316243)
                  ·
                    refine ⟨9448668435204157780974365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6299112290136105187316243 9448668435204157780974365)
                    ·
                      refine ⟨3543250663201559167865387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448668435204157780974365 3543250663201559167865387)
                      ·
                        rfl

theorem cell23_6900456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6900456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900456 prefixEnd_6900456 := by exact prefixLift 6900456
  have htrace : WordTrace (prefixWord ++ tailWord_6900456) baseStart_6900456 baseEnd_6900456 := by
    simpa [prefixWord, tailWord_6900456, baseEnd_6900456] using wordTrace_append hprefix tailTrace_6900456
  have hstable : (prefixWord ++ tailWord_6900456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900456).length < 2 ^ (prefixWord ++ tailWord_6900456).sum := by decide
  have hdescent : baseEnd_6900456 < baseStart_6900456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900465 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_6900465 : Nat := 118140960795 + 6900465 * 2 ^ 59
def prefixEnd_6900465 : Nat := 4983230072969 + 3 ^ 40 * 6900465 * 2
def baseEnd_6900465 : Nat := 3543255284527449632652845

theorem tailTrace_6900465 : CollatzResearch.WordTrace tailWord_6900465 prefixEnd_6900465 3543255284527449632652845 := by
  unfold tailWord_6900465
  simp only [CollatzResearch.WordTrace]
  refine ⟨251680634945801285441486849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167787089963867523627657899 251680634945801285441486849)
  ·
    refine ⟨188760476209350964081115137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251680634945801285441486849 188760476209350964081115137)
    ·
      refine ⟨141570357157013223060836353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188760476209350964081115137 141570357157013223060836353)
      ·
        refine ⟨106177767867759917295627265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141570357157013223060836353 106177767867759917295627265)
        ·
          refine ⟨79633325900819937971720449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106177767867759917295627265 79633325900819937971720449)
          ·
            refine ⟨59724994425614953478790337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79633325900819937971720449 59724994425614953478790337)
            ·
              refine ⟨44793745819211215109092753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59724994425614953478790337 44793745819211215109092753)
              ·
                refine ⟨33595309364408411331819565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44793745819211215109092753 33595309364408411331819565)
                ·
                  refine ⟨12598241011653154249432337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33595309364408411331819565 12598241011653154249432337)
                  ·
                    refine ⟨9448680758739865687074253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12598241011653154249432337 9448680758739865687074253)
                    ·
                      refine ⟨3543255284527449632652845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448680758739865687074253 3543255284527449632652845)
                      ·
                        rfl

theorem cell23_6900465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_6900465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900465 prefixEnd_6900465 := by exact prefixLift 6900465
  have htrace : WordTrace (prefixWord ++ tailWord_6900465) baseStart_6900465 baseEnd_6900465 := by
    simpa [prefixWord, tailWord_6900465, baseEnd_6900465] using wordTrace_append hprefix tailTrace_6900465
  have hstable : (prefixWord ++ tailWord_6900465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900465).length < 2 ^ (prefixWord ++ tailWord_6900465).sum := by decide
  have hdescent : baseEnd_6900465 < baseStart_6900465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900495 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_6900495 : Nat := 118140960795 + 6900495 * 2 ^ 59
def prefixEnd_6900495 : Nat := 4983230072969 + 3 ^ 40 * 6900495 * 2
def baseEnd_6900495 : Nat := 3543270688947084515277707

theorem tailTrace_6900495 : CollatzResearch.WordTrace tailWord_6900495 prefixEnd_6900495 3543270688947084515277707 := by
  unfold tailWord_6900495
  simp only [CollatzResearch.WordTrace]
  refine ⟨251681729135692600565078939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167787819423795067043385959 251681729135692600565078939)
  ·
    refine ⟨377522593703538900847618409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251681729135692600565078939 377522593703538900847618409)
    ·
      refine ⟨283141945277654175635713807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377522593703538900847618409 283141945277654175635713807)
      ·
        refine ⟨424712917916481263453570711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283141945277654175635713807 424712917916481263453570711)
        ·
          refine ⟨637069376874721895180356067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424712917916481263453570711 637069376874721895180356067)
          ·
            refine ⟨955604065312082842770534101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637069376874721895180356067 955604065312082842770534101)
            ·
              refine ⟨22396970280751941627434393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 955604065312082842770534101 22396970280751941627434393)
              ·
                refine ⟨16797727710563956220575795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22396970280751941627434393 16797727710563956220575795)
                ·
                  refine ⟨25196591565845934330863693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16797727710563956220575795 25196591565845934330863693)
                  ·
                    refine ⟨9448721837192225374073885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25196591565845934330863693 9448721837192225374073885)
                    ·
                      refine ⟨3543270688947084515277707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448721837192225374073885 3543270688947084515277707)
                      ·
                        rfl

theorem cell23_6900495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_6900495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900495 prefixEnd_6900495 := by exact prefixLift 6900495
  have htrace : WordTrace (prefixWord ++ tailWord_6900495) baseStart_6900495 baseEnd_6900495 := by
    simpa [prefixWord, tailWord_6900495, baseEnd_6900495] using wordTrace_append hprefix tailTrace_6900495
  have hstable : (prefixWord ++ tailWord_6900495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900495).length < 2 ^ (prefixWord ++ tailWord_6900495).sum := by decide
  have hdescent : baseEnd_6900495 < baseStart_6900495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900550 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6900550 : Nat := 118140960795 + 6900550 * 2 ^ 59
def prefixEnd_6900550 : Nat := 4983230072969 + 3 ^ 40 * 6900550 * 2
def baseEnd_6900550 : Nat := 3543298930383081800089955

theorem tailTrace_6900550 : CollatzResearch.WordTrace tailWord_6900550 prefixEnd_6900550 3543298930383081800089955 := by
  unfold tailWord_6900550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865116723452917029947847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167789156766995563305554069 7865116723452917029947847)
  ·
    refine ⟨11797675085179375544921771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7865116723452917029947847 11797675085179375544921771)
    ·
      refine ⟨17696512627769063317382657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11797675085179375544921771 17696512627769063317382657)
      ·
        refine ⟨13272384470826797488036993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17696512627769063317382657 13272384470826797488036993)
        ·
          refine ⟨9954288353120098116027745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13272384470826797488036993 9954288353120098116027745)
          ·
            refine ⟨7465716264840073587020809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9954288353120098116027745 7465716264840073587020809)
            ·
              refine ⟨5599287198630055190265607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465716264840073587020809 5599287198630055190265607)
              ·
                refine ⟨8398930797945082785398411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599287198630055190265607 8398930797945082785398411)
                ·
                  refine ⟨12598396196917624178097617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398930797945082785398411 12598396196917624178097617)
                  ·
                    refine ⟨9448797147688218133573213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12598396196917624178097617 9448797147688218133573213)
                    ·
                      refine ⟨3543298930383081800089955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9448797147688218133573213 3543298930383081800089955)
                      ·
                        rfl

theorem cell23_6900550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6900550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900550 prefixEnd_6900550 := by exact prefixLift 6900550
  have htrace : WordTrace (prefixWord ++ tailWord_6900550) baseStart_6900550 baseEnd_6900550 := by
    simpa [prefixWord, tailWord_6900550, baseEnd_6900550] using wordTrace_append hprefix tailTrace_6900550
  have hstable : (prefixWord ++ tailWord_6900550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900550).length < 2 ^ (prefixWord ++ tailWord_6900550).sum := by decide
  have hdescent : baseEnd_6900550 < baseStart_6900550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900552 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_6900552 : Nat := 118140960795 + 6900552 * 2 ^ 59
def prefixEnd_6900552 : Nat := 4983230072969 + 3 ^ 40 * 6900552 * 2
def baseEnd_6900552 : Nat := 3543299957344390792264945

theorem tailTrace_6900552 : CollatzResearch.WordTrace tailWord_6900552 prefixEnd_6900552 3543299957344390792264945 := by
  unfold tailWord_6900552
  simp only [CollatzResearch.WordTrace]
  refine ⟨125841904048243049649951955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167789205397657399533269273 125841904048243049649951955)
  ·
    refine ⟨188762856072364574474927933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125841904048243049649951955 188762856072364574474927933)
    ·
      refine ⟨70786071027136715428097975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188762856072364574474927933 70786071027136715428097975)
      ·
        refine ⟨106179106540705073142146963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70786071027136715428097975 106179106540705073142146963)
        ·
          refine ⟨159268659811057609713220445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106179106540705073142146963 159268659811057609713220445)
          ·
            refine ⟨59725747429146603642457667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159268659811057609713220445 59725747429146603642457667)
            ·
              refine ⟨89588621143719905463686501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59725747429146603642457667 89588621143719905463686501)
              ·
                refine ⟨16797866464447482274441219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89588621143719905463686501 16797866464447482274441219)
                ·
                  refine ⟨25196799696671223411661829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16797866464447482274441219 25196799696671223411661829)
                  ·
                    refine ⟨4724399943125854389686593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25196799696671223411661829 4724399943125854389686593)
                    ·
                      refine ⟨3543299957344390792264945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724399943125854389686593 3543299957344390792264945)
                      ·
                        rfl

theorem cell23_6900552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_6900552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900552 prefixEnd_6900552 := by exact prefixLift 6900552
  have htrace : WordTrace (prefixWord ++ tailWord_6900552) baseStart_6900552 baseEnd_6900552 := by
    simpa [prefixWord, tailWord_6900552, baseEnd_6900552] using wordTrace_append hprefix tailTrace_6900552
  have hstable : (prefixWord ++ tailWord_6900552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900552).length < 2 ^ (prefixWord ++ tailWord_6900552).sum := by decide
  have hdescent : baseEnd_6900552 < baseStart_6900552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900556 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_6900556 : Nat := 118140960795 + 6900556 * 2 ^ 59
def prefixEnd_6900556 : Nat := 4983230072969 + 3 ^ 40 * 6900556 * 2
def baseEnd_6900556 : Nat := 3543302011267008776614927

theorem tailTrace_6900556 : CollatzResearch.WordTrace tailWord_6900556 prefixEnd_6900556 3543302011267008776614927 := by
  unfold tailWord_6900556
  simp only [CollatzResearch.WordTrace]
  refine ⟨125841976994235803991524761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167789302658981071988699681 125841976994235803991524761)
  ·
    refine ⟨94381482745676852993643571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125841976994235803991524761 94381482745676852993643571)
    ·
      refine ⟨141572224118515279490465357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94381482745676852993643571 141572224118515279490465357)
      ·
        refine ⟨53089584044443229808924509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141572224118515279490465357 53089584044443229808924509)
        ·
          refine ⟨19908594016666211178346691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53089584044443229808924509 19908594016666211178346691)
          ·
            refine ⟨29862891024999316767520037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19908594016666211178346691 29862891024999316767520037)
            ·
              refine ⟨5599292067187371893910007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29862891024999316767520037 5599292067187371893910007)
              ·
                refine ⟨8398938100781057840865011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599292067187371893910007 8398938100781057840865011)
                ·
                  refine ⟨12598407151171586761297517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398938100781057840865011 12598407151171586761297517)
                  ·
                    refine ⟨4724402681689345035486569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12598407151171586761297517 4724402681689345035486569)
                    ·
                      refine ⟨3543302011267008776614927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724402681689345035486569 3543302011267008776614927)
                      ·
                        rfl

theorem cell23_6900556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_6900556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900556 prefixEnd_6900556 := by exact prefixLift 6900556
  have htrace : WordTrace (prefixWord ++ tailWord_6900556) baseStart_6900556 baseEnd_6900556 := by
    simpa [prefixWord, tailWord_6900556, baseEnd_6900556] using wordTrace_append hprefix tailTrace_6900556
  have hstable : (prefixWord ++ tailWord_6900556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900556).length < 2 ^ (prefixWord ++ tailWord_6900556).sum := by decide
  have hdescent : baseEnd_6900556 < baseStart_6900556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900565 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6900565 : Nat := 118140960795 + 6900565 * 2 ^ 59
def prefixEnd_6900565 : Nat := 4983230072969 + 3 ^ 40 * 6900565 * 2
def baseEnd_6900565 : Nat := 3543306632592899241402385

theorem tailTrace_6900565 : CollatzResearch.WordTrace tailWord_6900565 prefixEnd_6900565 3543306632592899241402385 := by
  unfold tailWord_6900565
  simp only [CollatzResearch.WordTrace]
  refine ⟨251684282245439002520127149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167789521496959335013418099 251684282245439002520127149)
  ·
    refine ⟨94381605842039625945047681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251684282245439002520127149 94381605842039625945047681)
    ·
      refine ⟨70786204381529719458785761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94381605842039625945047681 70786204381529719458785761)
      ·
        refine ⟨53089653286147289594089321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70786204381529719458785761 53089653286147289594089321)
        ·
          refine ⟨39817239964610467195566991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53089653286147289594089321 39817239964610467195566991)
          ·
            refine ⟨59725859946915700793350487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39817239964610467195566991 59725859946915700793350487)
            ·
              refine ⟨89588789920373551190025731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59725859946915700793350487 89588789920373551190025731)
              ·
                refine ⟨134383184880560326785038597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89588789920373551190025731 134383184880560326785038597)
                ·
                  refine ⟨25196847165105061272194737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134383184880560326785038597 25196847165105061272194737)
                  ·
                    refine ⟨18897635373828795954146053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25196847165105061272194737 18897635373828795954146053)
                    ·
                      refine ⟨3543306632592899241402385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18897635373828795954146053 3543306632592899241402385)
                      ·
                        rfl

theorem cell23_6900565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6900565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900565 prefixEnd_6900565 := by exact prefixLift 6900565
  have htrace : WordTrace (prefixWord ++ tailWord_6900565) baseStart_6900565 baseEnd_6900565 := by
    simpa [prefixWord, tailWord_6900565, baseEnd_6900565] using wordTrace_append hprefix tailTrace_6900565
  have hstable : (prefixWord ++ tailWord_6900565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900565).length < 2 ^ (prefixWord ++ tailWord_6900565).sum := by decide
  have hdescent : baseEnd_6900565 < baseStart_6900565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900569 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 4, 2, 2]
def baseStart_6900569 : Nat := 118140960795 + 6900569 * 2 ^ 59
def prefixEnd_6900569 : Nat := 4983230072969 + 3 ^ 40 * 6900569 * 2
def baseEnd_6900569 : Nat := 3543308686515517225752367

theorem tailTrace_6900569 : CollatzResearch.WordTrace tailWord_6900569 prefixEnd_6900569 3543308686515517225752367 := by
  unfold tailWord_6900569
  simp only [CollatzResearch.WordTrace]
  refine ⟨251684428137424511203272761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167789618758283007468848507 251684428137424511203272761)
  ·
    refine ⟨188763321103068383402454571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251684428137424511203272761 188763321103068383402454571)
    ·
      refine ⟨283144981654602575103681857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188763321103068383402454571 283144981654602575103681857)
      ·
        refine ⟨212358736240951931327761393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283144981654602575103681857 212358736240951931327761393)
        ·
          refine ⟨159269052180713948495821045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212358736240951931327761393 159269052180713948495821045)
          ·
            refine ⟨14931473641941932671483223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159269052180713948495821045 14931473641941932671483223)
            ·
              refine ⟨22397210462912899007224835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14931473641941932671483223 22397210462912899007224835)
              ·
                refine ⟨33595815694369348510837253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22397210462912899007224835 33595815694369348510837253)
                ·
                  refine ⟨6299215442694252845781985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33595815694369348510837253 6299215442694252845781985)
                  ·
                    refine ⟨4724411582020689634336489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299215442694252845781985 4724411582020689634336489)
                    ·
                      refine ⟨3543308686515517225752367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724411582020689634336489 3543308686515517225752367)
                      ·
                        rfl

theorem cell23_6900569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_6900569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900569 prefixEnd_6900569 := by exact prefixLift 6900569
  have htrace : WordTrace (prefixWord ++ tailWord_6900569) baseStart_6900569 baseEnd_6900569 := by
    simpa [prefixWord, tailWord_6900569, baseEnd_6900569] using wordTrace_append hprefix tailTrace_6900569
  have hstable : (prefixWord ++ tailWord_6900569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900569).length < 2 ^ (prefixWord ++ tailWord_6900569).sum := by decide
  have hdescent : baseEnd_6900569 < baseStart_6900569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900575 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 7]
def baseStart_6900575 : Nat := 118140960795 + 6900575 * 2 ^ 59
def prefixEnd_6900575 : Nat := 4983230072969 + 3 ^ 40 * 6900575 * 2
def baseEnd_6900575 : Nat := 393701307488827133586371

theorem tailTrace_6900575 : CollatzResearch.WordTrace tailWord_6900575 prefixEnd_6900575 393701307488827133586371 := by
  unfold tailWord_6900575
  simp only [CollatzResearch.WordTrace]
  refine ⟨251684646975402774227991179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167789764650268516151994119 251684646975402774227991179)
  ·
    refine ⟨377526970463104161341986769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251684646975402774227991179 377526970463104161341986769)
    ·
      refine ⟨283145227847328121006490077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377526970463104161341986769 283145227847328121006490077)
      ·
        refine ⟨106179460442748045377433779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283145227847328121006490077 106179460442748045377433779)
        ·
          refine ⟨159269190664122068066150669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106179460442748045377433779 159269190664122068066150669)
          ·
            refine ⟨59725946499045775524806501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159269190664122068066150669 59725946499045775524806501)
            ·
              refine ⟨11198614968571082910901219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59725946499045775524806501 11198614968571082910901219)
              ·
                refine ⟨16797922452856624366351829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198614968571082910901219 16797922452856624366351829)
                ·
                  refine ⟨393701307488827133586371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16797922452856624366351829 393701307488827133586371)
                  ·
                    rfl

theorem cell23_6900575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 7].length) (baseStart_6900575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900575 prefixEnd_6900575 := by exact prefixLift 6900575
  have htrace : WordTrace (prefixWord ++ tailWord_6900575) baseStart_6900575 baseEnd_6900575 := by
    simpa [prefixWord, tailWord_6900575, baseEnd_6900575] using wordTrace_append hprefix tailTrace_6900575
  have hstable : (prefixWord ++ tailWord_6900575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900575).length < 2 ^ (prefixWord ++ tailWord_6900575).sum := by decide
  have hdescent : baseEnd_6900575 < baseStart_6900575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900605 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_6900605 : Nat := 118140960795 + 6900605 * 2 ^ 59
def prefixEnd_6900605 : Nat := 4983230072969 + 3 ^ 40 * 6900605 * 2
def baseEnd_6900605 : Nat := 1181109057273026361634067

theorem tailTrace_6900605 : CollatzResearch.WordTrace tailWord_6900605 prefixEnd_6900605 1181109057273026361634067 := by
  unfold tailWord_6900605
  simp only [CollatzResearch.WordTrace]
  refine ⟨251685741165294089351583269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167790494110196059567722179 251685741165294089351583269)
  ·
    refine ⟨47191076468492641753421863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251685741165294089351583269 47191076468492641753421863)
    ·
      refine ⟨70786614702738962630132795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47191076468492641753421863 70786614702738962630132795)
      ·
        refine ⟨106179922054108443945199193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70786614702738962630132795 106179922054108443945199193)
        ·
          refine ⟨79634941540581332958899395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106179922054108443945199193 79634941540581332958899395)
          ·
            refine ⟨119452412310871999438349093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79634941540581332958899395 119452412310871999438349093)
            ·
              refine ⟨22397327308288499894690455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119452412310871999438349093 22397327308288499894690455)
              ·
                refine ⟨33595990962432749842035683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22397327308288499894690455 33595990962432749842035683)
                ·
                  refine ⟨50393986443649124763053525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33595990962432749842035683 50393986443649124763053525)
                  ·
                    refine ⟨1181109057273026361634067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50393986443649124763053525 1181109057273026361634067)
                    ·
                      rfl

theorem cell23_6900605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_6900605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900605 prefixEnd_6900605 := by exact prefixLift 6900605
  have htrace : WordTrace (prefixWord ++ tailWord_6900605) baseStart_6900605 baseEnd_6900605 := by
    simpa [prefixWord, tailWord_6900605, baseEnd_6900605] using wordTrace_append hprefix tailTrace_6900605
  have hstable : (prefixWord ++ tailWord_6900605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900605).length < 2 ^ (prefixWord ++ tailWord_6900605).sum := by decide
  have hdescent : baseEnd_6900605 < baseStart_6900605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900612 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6900612 : Nat := 118140960795 + 6900612 * 2 ^ 59
def prefixEnd_6900612 : Nat := 4983230072969 + 3 ^ 40 * 6900612 * 2
def baseEnd_6900612 : Nat := 3543330766183660557514669

theorem tailTrace_6900612 : CollatzResearch.WordTrace tailWord_6900612 prefixEnd_6900612 3543330766183660557514669 := by
  unfold tailWord_6900612
  simp only [CollatzResearch.WordTrace]
  refine ⟨125842998238134364773544045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167790664317512486364725393 125842998238134364773544045)
  ·
    refine ⟨47191124339300386790079017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125842998238134364773544045 47191124339300386790079017)
    ·
      refine ⟨35393343254475290092559263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47191124339300386790079017 35393343254475290092559263)
      ·
        refine ⟨53090014881712935138838895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35393343254475290092559263 53090014881712935138838895)
        ·
          refine ⟨79635022322569402708258343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53090014881712935138838895 79635022322569402708258343)
          ·
            refine ⟨119452533483854104062387515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79635022322569402708258343 119452533483854104062387515)
            ·
              refine ⟨179178800225781156093581273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119452533483854104062387515 179178800225781156093581273)
              ·
                refine ⟨134384100169335867070185955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179178800225781156093581273 134384100169335867070185955)
                ·
                  refine ⟨201576150254003800605278933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134384100169335867070185955 201576150254003800605278933)
                  ·
                    refine ⟨4724441021578214076686225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201576150254003800605278933 4724441021578214076686225)
                    ·
                      refine ⟨3543330766183660557514669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724441021578214076686225 3543330766183660557514669)
                      ·
                        rfl

theorem cell23_6900612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6900612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900612 prefixEnd_6900612 := by exact prefixLift 6900612
  have htrace : WordTrace (prefixWord ++ tailWord_6900612) baseStart_6900612 baseEnd_6900612 := by
    simpa [prefixWord, tailWord_6900612, baseEnd_6900612] using wordTrace_append hprefix tailTrace_6900612
  have hstable : (prefixWord ++ tailWord_6900612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900612).length < 2 ^ (prefixWord ++ tailWord_6900612).sum := by decide
  have hdescent : baseEnd_6900612 < baseStart_6900612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900626 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_6900626 : Nat := 118140960795 + 6900626 * 2 ^ 59
def prefixEnd_6900626 : Nat := 4983230072969 + 3 ^ 40 * 6900626 * 2
def baseEnd_6900626 : Nat := 393704217212535944748845

theorem tailTrace_6900626 : CollatzResearch.WordTrace tailWord_6900626 prefixEnd_6900626 393704217212535944748845 := by
  unfold tailWord_6900626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62921626774554502484524433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167791004732145339958731821 62921626774554502484524433)
  ·
    refine ⟨47191220080915876863393325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62921626774554502484524433 47191220080915876863393325)
    ·
      refine ⟨17696707530343453823772497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47191220080915876863393325 17696707530343453823772497)
      ·
        refine ⟨13272530647757590367829373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17696707530343453823772497 13272530647757590367829373)
        ·
          refine ⟨4977198992909096387936015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13272530647757590367829373 4977198992909096387936015)
          ·
            refine ⟨7465798489363644581904023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977198992909096387936015 7465798489363644581904023)
            ·
              refine ⟨11198697734045466872856035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465798489363644581904023 11198697734045466872856035)
              ·
                refine ⟨16798046601068200309284053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198697734045466872856035 16798046601068200309284053)
                ·
                  refine ⟨393704217212535944748845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16798046601068200309284053 393704217212535944748845)
                  ·
                    rfl

theorem cell23_6900626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_6900626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900626 prefixEnd_6900626 := by exact prefixLift 6900626
  have htrace : WordTrace (prefixWord ++ tailWord_6900626) baseStart_6900626 baseEnd_6900626 := by
    simpa [prefixWord, tailWord_6900626, baseEnd_6900626] using wordTrace_append hprefix tailTrace_6900626
  have hstable : (prefixWord ++ tailWord_6900626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900626).length < 2 ^ (prefixWord ++ tailWord_6900626).sum := by decide
  have hdescent : baseEnd_6900626 < baseStart_6900626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900686 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_6900686 : Nat := 118140960795 + 6900686 * 2 ^ 59
def prefixEnd_6900686 : Nat := 4983230072969 + 3 ^ 40 * 6900686 * 2
def baseEnd_6900686 : Nat := 1181122921250697755996443

theorem tailTrace_6900686 : CollatzResearch.WordTrace tailWord_6900686 prefixEnd_6900686 1181122921250697755996443 := by
  unfold tailWord_6900686
  simp only [CollatzResearch.WordTrace]
  refine ⟨31461086934750080023160239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167792463652000426790187941 31461086934750080023160239)
  ·
    refine ⟨47191630402125120034740359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31461086934750080023160239 47191630402125120034740359)
    ·
      refine ⟨70787445603187680052110539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47191630402125120034740359 70787445603187680052110539)
      ·
        refine ⟨106181168404781520078165809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70787445603187680052110539 106181168404781520078165809)
        ·
          refine ⟨79635876303586140058624357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106181168404781520078165809 79635876303586140058624357)
          ·
            refine ⟨14931726806922401260992067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79635876303586140058624357 14931726806922401260992067)
            ·
              refine ⟨22397590210383601891488101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14931726806922401260992067 22397590210383601891488101)
              ·
                refine ⟨4199548164446925354654019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22397590210383601891488101 4199548164446925354654019)
                ·
                  refine ⟨6299322246670388031981029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199548164446925354654019 6299322246670388031981029)
                  ·
                    refine ⟨1181122921250697755996443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299322246670388031981029 1181122921250697755996443)
                    ·
                      rfl

theorem cell23_6900686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_6900686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900686 prefixEnd_6900686 := by exact prefixLift 6900686
  have htrace : WordTrace (prefixWord ++ tailWord_6900686) baseStart_6900686 baseEnd_6900686 := by
    simpa [prefixWord, tailWord_6900686, baseEnd_6900686] using wordTrace_append hprefix tailTrace_6900686
  have hstable : (prefixWord ++ tailWord_6900686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900686).length < 2 ^ (prefixWord ++ tailWord_6900686).sum := by decide
  have hdescent : baseEnd_6900686 < baseStart_6900686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900705 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6900705 : Nat := 118140960795 + 6900705 * 2 ^ 59
def prefixEnd_6900705 : Nat := 4983230072969 + 3 ^ 40 * 6900705 * 2
def baseEnd_6900705 : Nat := 3543378519884528693651741

theorem tailTrace_6900705 : CollatzResearch.WordTrace tailWord_6900705 prefixEnd_6900705 3543378519884528693651741 := by
  unfold tailWord_6900705
  simp only [CollatzResearch.WordTrace]
  refine ⟨251689388464931806430223569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167792925643287870953482379 251689388464931806430223569)
  ·
    refine ⟨188767041348698854822667677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251689388464931806430223569 188767041348698854822667677)
    ·
      refine ⟨70787640505762070558500379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188767041348698854822667677 70787640505762070558500379)
      ·
        refine ⟨106181460758643105837750569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70787640505762070558500379 106181460758643105837750569)
        ·
          refine ⟨79636095568982329378312927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106181460758643105837750569 79636095568982329378312927)
          ·
            refine ⟨119454143353473494067469391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79636095568982329378312927 119454143353473494067469391)
            ·
              refine ⟨179181215030210241101204087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119454143353473494067469391 179181215030210241101204087)
              ·
                refine ⟨268771822545315361651806131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179181215030210241101204087 268771822545315361651806131)
                ·
                  refine ⟨403157733817973042477709197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268771822545315361651806131 403157733817973042477709197)
                  ·
                    refine ⟨151184150181739890929140949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403157733817973042477709197 151184150181739890929140949)
                    ·
                      refine ⟨3543378519884528693651741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151184150181739890929140949 3543378519884528693651741)
                      ·
                        rfl

theorem cell23_6900705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6900705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900705 prefixEnd_6900705 := by exact prefixLift 6900705
  have htrace : WordTrace (prefixWord ++ tailWord_6900705) baseStart_6900705 baseEnd_6900705 := by
    simpa [prefixWord, tailWord_6900705, baseEnd_6900705] using wordTrace_append hprefix tailTrace_6900705
  have hstable : (prefixWord ++ tailWord_6900705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900705).length < 2 ^ (prefixWord ++ tailWord_6900705).sum := by decide
  have hdescent : baseEnd_6900705 < baseStart_6900705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900712 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6900712 : Nat := 118140960795 + 6900712 * 2 ^ 59
def prefixEnd_6900712 : Nat := 4983230072969 + 3 ^ 40 * 6900712 * 2
def baseEnd_6900712 : Nat := 1181127371416370055421403

theorem tailTrace_6900712 : CollatzResearch.WordTrace tailWord_6900712 prefixEnd_6900712 1181127371416370055421403 := by
  unfold tailWord_6900712
  simp only [CollatzResearch.WordTrace]
  refine ⟨125844821887953223312864195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167793095850604297750485593 125844821887953223312864195)
  ·
    refine ⟨188767232831929834969296293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125844821887953223312864195 188767232831929834969296293)
    ·
      refine ⟨35393856155986844056743055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188767232831929834969296293 35393856155986844056743055)
      ·
        refine ⟨53090784233980266085114583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35393856155986844056743055 53090784233980266085114583)
        ·
          refine ⟨79636176350970399127671875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53090784233980266085114583 79636176350970399127671875)
          ·
            refine ⟨119454264526455598691507813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79636176350970399127671875 119454264526455598691507813)
            ·
              refine ⟨22397674598710424754657715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119454264526455598691507813 22397674598710424754657715)
              ·
                refine ⟨33596511898065637131986573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22397674598710424754657715 33596511898065637131986573)
                ·
                  refine ⟨12598691961774613924494965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33596511898065637131986573 12598691961774613924494965)
                  ·
                    refine ⟨1181127371416370055421403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12598691961774613924494965 1181127371416370055421403)
                    ·
                      rfl

theorem cell23_6900712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6900712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900712 prefixEnd_6900712 := by exact prefixLift 6900712
  have htrace : WordTrace (prefixWord ++ tailWord_6900712) baseStart_6900712 baseEnd_6900712 := by
    simpa [prefixWord, tailWord_6900712, baseEnd_6900712] using wordTrace_append hprefix tailTrace_6900712
  have hstable : (prefixWord ++ tailWord_6900712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900712).length < 2 ^ (prefixWord ++ tailWord_6900712).sum := by decide
  have hdescent : baseEnd_6900712 < baseStart_6900712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900719 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 5, 2]
def baseStart_6900719 : Nat := 118140960795 + 6900719 * 2 ^ 59
def prefixEnd_6900719 : Nat := 4983230072969 + 3 ^ 40 * 6900719 * 2
def baseEnd_6900719 : Nat := 3543385708613691638876677

theorem tailTrace_6900719 : CollatzResearch.WordTrace tailWord_6900719 prefixEnd_6900719 3543385708613691638876677 := by
  unfold tailWord_6900719
  simp only [CollatzResearch.WordTrace]
  refine ⟨251689899086881086821233211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167793266057920724547488807 251689899086881086821233211)
  ·
    refine ⟨377534848630321630231849817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251689899086881086821233211 377534848630321630231849817)
    ·
      refine ⟨283151136472741222673887363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377534848630321630231849817 283151136472741222673887363)
      ·
        refine ⟨424726704709111834010831045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283151136472741222673887363 424726704709111834010831045)
        ·
          refine ⟨79636257132958468877030821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424726704709111834010831045 79636257132958468877030821)
          ·
            refine ⟨14931798212429712914443279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79636257132958468877030821 14931798212429712914443279)
            ·
              refine ⟨22397697318644569371664919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14931798212429712914443279 22397697318644569371664919)
              ·
                refine ⟨33596545977966854057497379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22397697318644569371664919 33596545977966854057497379)
                ·
                  refine ⟨50394818966950281086246069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33596545977966854057497379 50394818966950281086246069)
                  ·
                    refine ⟨4724514278151588851835569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50394818966950281086246069 4724514278151588851835569)
                    ·
                      refine ⟨3543385708613691638876677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724514278151588851835569 3543385708613691638876677)
                      ·
                        rfl

theorem cell23_6900719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5, 2].length) (baseStart_6900719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900719 prefixEnd_6900719 := by exact prefixLift 6900719
  have htrace : WordTrace (prefixWord ++ tailWord_6900719) baseStart_6900719 baseEnd_6900719 := by
    simpa [prefixWord, tailWord_6900719, baseEnd_6900719] using wordTrace_append hprefix tailTrace_6900719
  have hstable : (prefixWord ++ tailWord_6900719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900719).length < 2 ^ (prefixWord ++ tailWord_6900719).sum := by decide
  have hdescent : baseEnd_6900719 < baseStart_6900719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900755 : List Nat := [1, 1, 1, 2, 1, 4, 1, 12]
def baseStart_6900755 : Nat := 118140960795 + 6900755 * 2 ^ 59
def prefixEnd_6900755 : Nat := 4983230072969 + 3 ^ 40 * 6900755 * 2
def baseEnd_6900755 : Nat := 131237192367305685112093

theorem tailTrace_6900755 : CollatzResearch.WordTrace tailWord_6900755 prefixEnd_6900755 131237192367305685112093 := by
  unfold tailWord_6900755
  simp only [CollatzResearch.WordTrace]
  refine ⟨251691212114750664969543719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167794141409833776646362479 251691212114750664969543719)
  ·
    refine ⟨377536818172125997454315579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251691212114750664969543719 377536818172125997454315579)
    ·
      refine ⟨566305227258188996181473369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377536818172125997454315579 566305227258188996181473369)
      ·
        refine ⟨424728920443641747136105027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566305227258188996181473369 424728920443641747136105027)
        ·
          refine ⟨637093380665462620704157541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424728920443641747136105027 637093380665462620704157541)
          ·
            refine ⟨119455008874774241382029539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637093380665462620704157541 119455008874774241382029539)
            ·
              refine ⟨179182513312161362073044309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119455008874774241382029539 179182513312161362073044309)
              ·
                refine ⟨131237192367305685112093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 179182513312161362073044309 131237192367305685112093)
                ·
                  rfl

theorem cell23_6900755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 12].length) (baseStart_6900755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900755 prefixEnd_6900755 := by exact prefixLift 6900755
  have htrace : WordTrace (prefixWord ++ tailWord_6900755) baseStart_6900755 baseEnd_6900755 := by
    simpa [prefixWord, tailWord_6900755, baseEnd_6900755] using wordTrace_append hprefix tailTrace_6900755
  have hstable : (prefixWord ++ tailWord_6900755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900755).length < 2 ^ (prefixWord ++ tailWord_6900755).sum := by decide
  have hdescent : baseEnd_6900755 < baseStart_6900755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900759 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 1, 6]
def baseStart_6900759 : Nat := 118140960795 + 6900759 * 2 ^ 59
def prefixEnd_6900759 : Nat := 4983230072969 + 3 ^ 40 * 6900759 * 2
def baseEnd_6900759 : Nat := 1181135415946623827458831

theorem tailTrace_6900759 : CollatzResearch.WordTrace tailWord_6900759 prefixEnd_6900759 1181135415946623827458831 := by
  unfold tailWord_6900759
  simp only [CollatzResearch.WordTrace]
  refine ⟨251691358006736173652689331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167794238671157449101792887 251691358006736173652689331)
  ·
    refine ⟨377537037010104260479033997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251691358006736173652689331 377537037010104260479033997)
    ·
      refine ⟨141576388878789097679637749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377537037010104260479033997 141576388878789097679637749)
      ·
        refine ⟨13272786457386477907466039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141576388878789097679637749 13272786457386477907466039)
        ·
          refine ⟨19909179686079716861199059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13272786457386477907466039 19909179686079716861199059)
          ·
            refine ⟨29863769529119575291798589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19909179686079716861199059 29863769529119575291798589)
            ·
              refine ⟨11198913573419840734424471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29863769529119575291798589 11198913573419840734424471)
              ·
                refine ⟨16798370360129761101636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198913573419840734424471 16798370360129761101636707)
                ·
                  refine ⟨25197555540194641652455061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16798370360129761101636707 25197555540194641652455061)
                  ·
                    refine ⟨1181135415946623827458831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25197555540194641652455061 1181135415946623827458831)
                    ·
                      rfl

theorem cell23_6900759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_6900759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900759 prefixEnd_6900759 := by exact prefixLift 6900759
  have htrace : WordTrace (prefixWord ++ tailWord_6900759) baseStart_6900759 baseEnd_6900759 := by
    simpa [prefixWord, tailWord_6900759, baseEnd_6900759] using wordTrace_append hprefix tailTrace_6900759
  have hstable : (prefixWord ++ tailWord_6900759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900759).length < 2 ^ (prefixWord ++ tailWord_6900759).sum := by decide
  have hdescent : baseEnd_6900759 < baseStart_6900759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900762 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_6900762 : Nat := 118140960795 + 6900762 * 2 ^ 59
def prefixEnd_6900762 : Nat := 4983230072969 + 3 ^ 40 * 6900762 * 2
def baseEnd_6900762 : Nat := 3543407788281834970638979

theorem tailTrace_6900762 : CollatzResearch.WordTrace tailWord_6900762 prefixEnd_6900762 3543407788281834970638979 := by
  unfold tailWord_6900762
  simp only [CollatzResearch.WordTrace]
  refine ⟨62922866856431326291262135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167794311617150203443365693 62922866856431326291262135)
  ·
    refine ⟨94384300284646989436893203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62922866856431326291262135 94384300284646989436893203)
    ·
      refine ⟨141576450426970484155339805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94384300284646989436893203 141576450426970484155339805)
      ·
        refine ⟨53091168910113931558252427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141576450426970484155339805 53091168910113931558252427)
        ·
          refine ⟨79636753365170897337378641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53091168910113931558252427 79636753365170897337378641)
          ·
            refine ⟨59727565023878173003033981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79636753365170897337378641 59727565023878173003033981)
            ·
              refine ⟨22397836883954314876137743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59727565023878173003033981 22397836883954314876137743)
              ·
                refine ⟨33596755325931472314206615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22397836883954314876137743 33596755325931472314206615)
                ·
                  refine ⟨50395132988897208471309923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33596755325931472314206615 50395132988897208471309923)
                  ·
                    refine ⟨75592699483345812706964885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50395132988897208471309923 75592699483345812706964885)
                    ·
                      refine ⟨3543407788281834970638979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75592699483345812706964885 3543407788281834970638979)
                      ·
                        rfl

theorem cell23_6900762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_6900762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900762 prefixEnd_6900762 := by exact prefixLift 6900762
  have htrace : WordTrace (prefixWord ++ tailWord_6900762) baseStart_6900762 baseEnd_6900762 := by
    simpa [prefixWord, tailWord_6900762, baseEnd_6900762] using wordTrace_append hprefix tailTrace_6900762
  have hstable : (prefixWord ++ tailWord_6900762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900762).length < 2 ^ (prefixWord ++ tailWord_6900762).sum := by decide
  have hdescent : baseEnd_6900762 < baseStart_6900762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900800 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 1, 2, 2]
def baseStart_6900800 : Nat := 118140960795 + 6900800 * 2 ^ 59
def prefixEnd_6900800 : Nat := 4983230072969 + 3 ^ 40 * 6900800 * 2
def baseEnd_6900800 : Nat := 3543427300546705821963805

theorem tailTrace_6900800 : CollatzResearch.WordTrace tailWord_6900800 prefixEnd_6900800 3543427300546705821963805 := by
  unfold tailWord_6900800
  simp only [CollatzResearch.WordTrace]
  refine ⟨125846426699793818827465927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167795235599725091769954569 125846426699793818827465927)
  ·
    refine ⟨188769640049690728241198891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125846426699793818827465927 188769640049690728241198891)
    ·
      refine ⟨283154460074536092361798337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188769640049690728241198891 283154460074536092361798337)
      ·
        refine ⟨212365845055902069271348753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283154460074536092361798337 212365845055902069271348753)
        ·
          refine ⟨159274383791926551953511565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212365845055902069271348753 159274383791926551953511565)
          ·
            refine ⟨59727893921972456982566837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159274383791926551953511565 59727893921972456982566837)
            ·
              refine ⟨5599490055184917842115641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59727893921972456982566837 5599490055184917842115641)
              ·
                refine ⟨4199617541388688381586731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599490055184917842115641 4199617541388688381586731)
                ·
                  refine ⟨6299426312083032572380097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199617541388688381586731 6299426312083032572380097)
                  ·
                    refine ⟨4724569734062274429285073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299426312083032572380097 4724569734062274429285073)
                    ·
                      refine ⟨3543427300546705821963805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724569734062274429285073 3543427300546705821963805)
                      ·
                        rfl

theorem cell23_6900800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_6900800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900800 prefixEnd_6900800 := by exact prefixLift 6900800
  have htrace : WordTrace (prefixWord ++ tailWord_6900800) baseStart_6900800 baseEnd_6900800 := by
    simpa [prefixWord, tailWord_6900800, baseEnd_6900800] using wordTrace_append hprefix tailTrace_6900800
  have hstable : (prefixWord ++ tailWord_6900800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900800).length < 2 ^ (prefixWord ++ tailWord_6900800).sum := by decide
  have hdescent : baseEnd_6900800 < baseStart_6900800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900806 : List Nat := [6, 1, 1, 1, 1, 3, 2, 8]
def baseStart_6900806 : Nat := 118140960795 + 6900806 * 2 ^ 59
def prefixEnd_6900806 : Nat := 4983230072969 + 3 ^ 40 * 6900806 * 2
def baseEnd_6900806 : Nat := 131238162275208622166251

theorem tailTrace_6900806 : CollatzResearch.WordTrace tailWord_6900806 prefixEnd_6900806 131238162275208622166251 := by
  unfold tailWord_6900806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865408507423934396239071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167795381491710600453100181 7865408507423934396239071)
  ·
    refine ⟨11798112761135901594358607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7865408507423934396239071 11798112761135901594358607)
    ·
      refine ⟨17697169141703852391537911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11798112761135901594358607 17697169141703852391537911)
      ·
        refine ⟨26545753712555778587306867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17697169141703852391537911 26545753712555778587306867)
        ·
          refine ⟨39818630568833667880960301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26545753712555778587306867 39818630568833667880960301)
          ·
            refine ⟨14931986463312625455360113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39818630568833667880960301 14931986463312625455360113)
            ·
              refine ⟨11198989847484469091520085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14931986463312625455360113 11198989847484469091520085)
              ·
                refine ⟨131238162275208622166251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11198989847484469091520085 131238162275208622166251)
                ·
                  rfl

theorem cell23_6900806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_6900806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900806 prefixEnd_6900806 := by exact prefixLift 6900806
  have htrace : WordTrace (prefixWord ++ tailWord_6900806) baseStart_6900806 baseEnd_6900806 := by
    simpa [prefixWord, tailWord_6900806, baseEnd_6900806] using wordTrace_append hprefix tailTrace_6900806
  have hstable : (prefixWord ++ tailWord_6900806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900806).length < 2 ^ (prefixWord ++ tailWord_6900806).sum := by decide
  have hdescent : baseEnd_6900806 < baseStart_6900806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900826 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_6900826 : Nat := 118140960795 + 6900826 * 2 ^ 59
def prefixEnd_6900826 : Nat := 4983230072969 + 3 ^ 40 * 6900826 * 2
def baseEnd_6900826 : Nat := 3543440651043722720238685

theorem tailTrace_6900826 : CollatzResearch.WordTrace tailWord_6900826 prefixEnd_6900826 3543440651043722720238685 := by
  unfold tailWord_6900826
  simp only [CollatzResearch.WordTrace]
  refine ⟨62923450424373361023844583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167795867798328962730252221 62923450424373361023844583)
  ·
    refine ⟨94385175636560041535766875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62923450424373361023844583 94385175636560041535766875)
    ·
      refine ⟨141577763454840062303650313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94385175636560041535766875 141577763454840062303650313)
      ·
        refine ⟨106183322591130046727737735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141577763454840062303650313 106183322591130046727737735)
        ·
          refine ⟨159274983886695070091606603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106183322591130046727737735 159274983886695070091606603)
          ·
            refine ⟨238912475830042605137409905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159274983886695070091606603 238912475830042605137409905)
            ·
              refine ⟨179184356872531953853057429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238912475830042605137409905 179184356872531953853057429)
              ·
                refine ⟨8399266728399935336862067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179184356872531953853057429 8399266728399935336862067)
                ·
                  refine ⟨12598900092599903005293101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8399266728399935336862067 12598900092599903005293101)
                  ·
                    refine ⟨4724587534724963626984913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12598900092599903005293101 4724587534724963626984913)
                    ·
                      refine ⟨3543440651043722720238685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724587534724963626984913 3543440651043722720238685)
                      ·
                        rfl

theorem cell23_6900826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_6900826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900826 prefixEnd_6900826 := by exact prefixLift 6900826
  have htrace : WordTrace (prefixWord ++ tailWord_6900826) baseStart_6900826 baseEnd_6900826 := by
    simpa [prefixWord, tailWord_6900826, baseEnd_6900826] using wordTrace_append hprefix tailTrace_6900826
  have hstable : (prefixWord ++ tailWord_6900826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900826).length < 2 ^ (prefixWord ++ tailWord_6900826).sum := by decide
  have hdescent : baseEnd_6900826 < baseStart_6900826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900856 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_6900856 : Nat := 118140960795 + 6900856 * 2 ^ 59
def prefixEnd_6900856 : Nat := 4983230072969 + 3 ^ 40 * 6900856 * 2
def baseEnd_6900856 : Nat := 3543456055463357602863547

theorem tailTrace_6900856 : CollatzResearch.WordTrace tailWord_6900856 prefixEnd_6900856 3543456055463357602863547 := by
  unfold tailWord_6900856
  simp only [CollatzResearch.WordTrace]
  refine ⟨125847447943692379609485211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167796597258256506145980281 125847447943692379609485211)
  ·
    refine ⟨188771171915538569414227817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125847447943692379609485211 188771171915538569414227817)
    ·
      refine ⟨141578378936653927060670863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188771171915538569414227817 141578378936653927060670863)
      ·
        refine ⟨212367568404980890591006295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141578378936653927060670863 212367568404980890591006295)
        ·
          refine ⟨318551352607471335886509443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212367568404980890591006295 318551352607471335886509443)
          ·
            refine ⟨477827028911207003829764165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318551352607471335886509443 477827028911207003829764165)
            ·
              refine ⟨89592567920851313218080781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 477827028911207003829764165 89592567920851313218080781)
              ·
                refine ⟨33597212970319242456780293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89592567920851313218080781 33597212970319242456780293)
                ·
                  refine ⟨6299477431934857960646305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33597212970319242456780293 6299477431934857960646305)
                  ·
                    refine ⟨4724608073951143470484729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299477431934857960646305 4724608073951143470484729)
                    ·
                      refine ⟨3543456055463357602863547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724608073951143470484729 3543456055463357602863547)
                      ·
                        rfl

theorem cell23_6900856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_6900856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900856 prefixEnd_6900856 := by exact prefixLift 6900856
  have htrace : WordTrace (prefixWord ++ tailWord_6900856) baseStart_6900856 baseEnd_6900856 := by
    simpa [prefixWord, tailWord_6900856, baseEnd_6900856] using wordTrace_append hprefix tailTrace_6900856
  have hstable : (prefixWord ++ tailWord_6900856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900856).length < 2 ^ (prefixWord ++ tailWord_6900856).sum := by decide
  have hdescent : baseEnd_6900856 < baseStart_6900856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900873 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 2, 2, 2]
def baseStart_6900873 : Nat := 118140960795 + 6900873 * 2 ^ 59
def prefixEnd_6900873 : Nat := 4983230072969 + 3 ^ 40 * 6900873 * 2
def baseEnd_6900873 : Nat := 3543464784634484036350969

theorem tailTrace_6900873 : CollatzResearch.WordTrace tailWord_6900873 prefixEnd_6900873 3543464784634484036350969 := by
  unfold tailWord_6900873
  simp only [CollatzResearch.WordTrace]
  refine ⟨251695515928323171122339273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167797010618882114081559515 251695515928323171122339273)
  ·
    refine ⟨188771636946242378341754455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251695515928323171122339273 188771636946242378341754455)
    ·
      refine ⟨283157455419363567512631683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188771636946242378341754455 283157455419363567512631683)
      ·
        refine ⟨424736183129045351268947525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283157455419363567512631683 424736183129045351268947525)
        ·
          refine ⟨79638034336696003362927661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424736183129045351268947525 79638034336696003362927661)
          ·
            refine ⟨29864262876261001261097873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79638034336696003362927661 29864262876261001261097873)
            ·
              refine ⟨22398197157195750945823405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29864262876261001261097873 22398197157195750945823405)
              ·
                refine ⟨8399323933948406604683777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22398197157195750945823405 8399323933948406604683777)
                ·
                  refine ⟨6299492950461304953512833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8399323933948406604683777 6299492950461304953512833)
                  ·
                    refine ⟨4724619712845978715134625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299492950461304953512833 4724619712845978715134625)
                    ·
                      refine ⟨3543464784634484036350969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724619712845978715134625 3543464784634484036350969)
                      ·
                        rfl

theorem cell23_6900873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2, 2].length) (baseStart_6900873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900873 prefixEnd_6900873 := by exact prefixLift 6900873
  have htrace : WordTrace (prefixWord ++ tailWord_6900873) baseStart_6900873 baseEnd_6900873 := by
    simpa [prefixWord, tailWord_6900873, baseEnd_6900873] using wordTrace_append hprefix tailTrace_6900873
  have hstable : (prefixWord ++ tailWord_6900873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900873).length < 2 ^ (prefixWord ++ tailWord_6900873).sum := by decide
  have hdescent : baseEnd_6900873 < baseStart_6900873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900896 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 5]
def baseStart_6900896 : Nat := 118140960795 + 6900896 * 2 ^ 59
def prefixEnd_6900896 : Nat := 4983230072969 + 3 ^ 40 * 6900896 * 2
def baseEnd_6900896 : Nat := 393719621632170827373707

theorem tailTrace_6900896 : CollatzResearch.WordTrace tailWord_6900896 prefixEnd_6900896 393719621632170827373707 := by
  unfold tailWord_6900896
  simp only [CollatzResearch.WordTrace]
  refine ⟨125848177403619923025213271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167797569871493230700284361 125848177403619923025213271)
  ·
    refine ⟨188772266105429884537819907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125848177403619923025213271 188772266105429884537819907)
    ·
      refine ⟨283158399158144826806729861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188772266105429884537819907 283158399158144826806729861)
      ·
        refine ⟨53092199842152155026261849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283158399158144826806729861 53092199842152155026261849)
        ·
          refine ⟨39819149881614116269696387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53092199842152155026261849 39819149881614116269696387)
          ·
            refine ⟨59728724822421174404544581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39819149881614116269696387 59728724822421174404544581)
            ·
              refine ⟨11199135904203970200852109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59728724822421174404544581 11199135904203970200852109)
              ·
                refine ⟨4199675964076488825319541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11199135904203970200852109 4199675964076488825319541)
                ·
                  refine ⟨393719621632170827373707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4199675964076488825319541 393719621632170827373707)
                  ·
                    rfl

theorem cell23_6900896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 5].length) (baseStart_6900896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900896 prefixEnd_6900896 := by exact prefixLift 6900896
  have htrace : WordTrace (prefixWord ++ tailWord_6900896) baseStart_6900896 baseEnd_6900896 := by
    simpa [prefixWord, tailWord_6900896, baseEnd_6900896] using wordTrace_append hprefix tailTrace_6900896
  have hstable : (prefixWord ++ tailWord_6900896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900896).length < 2 ^ (prefixWord ++ tailWord_6900896).sum := by decide
  have hdescent : baseEnd_6900896 < baseStart_6900896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900939 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 5, 4]
def baseStart_6900939 : Nat := 118140960795 + 6900939 * 2 ^ 59
def prefixEnd_6900939 : Nat := 4983230072969 + 3 ^ 40 * 6900939 * 2
def baseEnd_6900939 : Nat := 1181166224785893592708555

theorem tailTrace_6900939 : CollatzResearch.WordTrace tailWord_6900939 prefixEnd_6900939 1181166224785893592708555 := by
  unfold tailWord_6900939
  simp only [CollatzResearch.WordTrace]
  refine ⟨251697923146084064394241871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167798615430722709596161247 251697923146084064394241871)
  ·
    refine ⟨377546884719126096591362807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251697923146084064394241871 377546884719126096591362807)
    ·
      refine ⟨566320327078689144887044211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377546884719126096591362807 566320327078689144887044211)
      ·
        refine ⟨849480490618033717330566317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566320327078689144887044211 849480490618033717330566317)
        ·
          refine ⟨318555183981762643998962369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849480490618033717330566317 318555183981762643998962369)
          ·
            refine ⟨238916387986321982999221777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318555183981762643998962369 238916387986321982999221777)
            ·
              refine ⟨179187290989741487249416333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238916387986321982999221777 179187290989741487249416333)
              ·
                refine ⟨67195234121153057718531125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179187290989741487249416333 67195234121153057718531125)
                ·
                  refine ⟨6299553198858099161112293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67195234121153057718531125 6299553198858099161112293)
                  ·
                    refine ⟨1181166224785893592708555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299553198858099161112293 1181166224785893592708555)
                    ·
                      rfl

theorem cell23_6900939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 4].length) (baseStart_6900939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900939 prefixEnd_6900939 := by exact prefixLift 6900939
  have htrace : WordTrace (prefixWord ++ tailWord_6900939) baseStart_6900939 baseEnd_6900939 := by
    simpa [prefixWord, tailWord_6900939, baseEnd_6900939] using wordTrace_append hprefix tailTrace_6900939
  have hstable : (prefixWord ++ tailWord_6900939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900939).length < 2 ^ (prefixWord ++ tailWord_6900939).sum := by decide
  have hdescent : baseEnd_6900939 < baseStart_6900939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900946 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6900946 : Nat := 118140960795 + 6900946 * 2 ^ 59
def prefixEnd_6900946 : Nat := 4983230072969 + 3 ^ 40 * 6900946 * 2
def baseEnd_6900946 : Nat := 3543502268722262250738133

theorem tailTrace_6900946 : CollatzResearch.WordTrace tailWord_6900946 prefixEnd_6900946 3543502268722262250738133 := by
  unfold tailWord_6900946
  simp only [CollatzResearch.WordTrace]
  refine ⟨62924544614264676147436673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167798785638039136393164461 62924544614264676147436673)
  ·
    refine ⟨47193408460698507110577505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62924544614264676147436673 47193408460698507110577505)
    ·
      refine ⟨35395056345523880332933129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47193408460698507110577505 35395056345523880332933129)
      ·
        refine ⟨26546292259142910249699847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35395056345523880332933129 26546292259142910249699847)
        ·
          refine ⟨39819438388714365374549771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26546292259142910249699847 39819438388714365374549771)
          ·
            refine ⟨59729157583071548061824657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39819438388714365374549771 59729157583071548061824657)
            ·
              refine ⟨44796868187303661046368493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59729157583071548061824657 44796868187303661046368493)
              ·
                refine ⟨16798825570238872892388185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44796868187303661046368493 16798825570238872892388185)
                ·
                  refine ⟨12599119177679154669291139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16798825570238872892388185 12599119177679154669291139)
                  ·
                    refine ⟨18898678766518732003936709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12599119177679154669291139 18898678766518732003936709)
                    ·
                      refine ⟨3543502268722262250738133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18898678766518732003936709 3543502268722262250738133)
                      ·
                        rfl

theorem cell23_6900946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6900946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900946 prefixEnd_6900946 := by exact prefixLift 6900946
  have htrace : WordTrace (prefixWord ++ tailWord_6900946) baseStart_6900946 baseEnd_6900946 := by
    simpa [prefixWord, tailWord_6900946, baseEnd_6900946] using wordTrace_append hprefix tailTrace_6900946
  have hstable : (prefixWord ++ tailWord_6900946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900946).length < 2 ^ (prefixWord ++ tailWord_6900946).sum := by decide
  have hdescent : baseEnd_6900946 < baseStart_6900946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6900973 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6900973 : Nat := 118140960795 + 6900973 * 2 ^ 59
def prefixEnd_6900973 : Nat := 4983230072969 + 3 ^ 40 * 6900973 * 2
def baseEnd_6900973 : Nat := 1181172044233311215033503

theorem tailTrace_6900973 : CollatzResearch.WordTrace tailWord_6900973 prefixEnd_6900973 1181172044233311215033503 := by
  unfold tailWord_6900973
  simp only [CollatzResearch.WordTrace]
  refine ⟨251699163227960888200979573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167799442151973925467319715 251699163227960888200979573)
  ·
    refine ⟨23596796552621333268841835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251699163227960888200979573 23596796552621333268841835)
    ·
      refine ⟨35395194828931999903262753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23596796552621333268841835 35395194828931999903262753)
      ·
        refine ⟨26546396121698999927447065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35395194828931999903262753 26546396121698999927447065)
        ·
          refine ⟨19909797091274249945585299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26546396121698999927447065 19909797091274249945585299)
          ·
            refine ⟨29864695636911374918377949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19909797091274249945585299 29864695636911374918377949)
            ·
              refine ⟨11199260863841765594391731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29864695636911374918377949 11199260863841765594391731)
              ·
                refine ⟨16798891295762648391587597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11199260863841765594391731 16798891295762648391587597)
                ·
                  refine ⟨6299584235910993146845349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16798891295762648391587597 6299584235910993146845349)
                  ·
                    refine ⟨1181172044233311215033503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299584235910993146845349 1181172044233311215033503)
                    ·
                      rfl

theorem cell23_6900973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6900973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6900973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6900973 prefixEnd_6900973 := by exact prefixLift 6900973
  have htrace : WordTrace (prefixWord ++ tailWord_6900973) baseStart_6900973 baseEnd_6900973 := by
    simpa [prefixWord, tailWord_6900973, baseEnd_6900973] using wordTrace_append hprefix tailTrace_6900973
  have hstable : (prefixWord ++ tailWord_6900973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6900973).length < 2 ^ (prefixWord ++ tailWord_6900973).sum := by decide
  have hdescent : baseEnd_6900973 < baseStart_6900973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6900973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901024 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 1, 4]
def baseStart_6901024 : Nat := 118140960795 + 6901024 * 2 ^ 59
def prefixEnd_6901024 : Nat := 4983230072969 + 3 ^ 40 * 6901024 * 2
def baseEnd_6901024 : Nat := 1181180773404437648520925

theorem tailTrace_6901024 : CollatzResearch.WordTrace tailWord_6901024 prefixEnd_6901024 1181180773404437648520925 := by
  unfold tailWord_6901024
  simp only [CollatzResearch.WordTrace]
  refine ⟨125850511675388061955543063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167800682233850749274057417 125850511675388061955543063)
  ·
    refine ⟨188775767513082092933314595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125850511675388061955543063 188775767513082092933314595)
    ·
      refine ⟨283163651269623139399971893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188775767513082092933314595 283163651269623139399971893)
      ·
        refine ⟨26546592306527169318747365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283163651269623139399971893 26546592306527169318747365)
        ·
          refine ⟨4977486057473844247265131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26546592306527169318747365 4977486057473844247265131)
          ·
            refine ⟨7466229086210766370897697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977486057473844247265131 7466229086210766370897697)
            ·
              refine ⟨5599671814658074778173273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466229086210766370897697 5599671814658074778173273)
              ·
                refine ⟨4199753860993556083629955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599671814658074778173273 4199753860993556083629955)
                ·
                  refine ⟨6299630791490334125444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199753860993556083629955 6299630791490334125444933)
                  ·
                    refine ⟨1181180773404437648520925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299630791490334125444933 1181180773404437648520925)
                    ·
                      rfl

theorem cell23_6901024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 4].length) (baseStart_6901024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901024 prefixEnd_6901024 := by exact prefixLift 6901024
  have htrace : WordTrace (prefixWord ++ tailWord_6901024) baseStart_6901024 baseEnd_6901024 := by
    simpa [prefixWord, tailWord_6901024, baseEnd_6901024] using wordTrace_append hprefix tailTrace_6901024
  have hstable : (prefixWord ++ tailWord_6901024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901024).length < 2 ^ (prefixWord ++ tailWord_6901024).sum := by decide
  have hdescent : baseEnd_6901024 < baseStart_6901024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901036 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_6901036 : Nat := 118140960795 + 6901036 * 2 ^ 59
def prefixEnd_6901036 : Nat := 4983230072969 + 3 ^ 40 * 6901036 * 2
def baseEnd_6901036 : Nat := 3543548481981166898612719

theorem tailTrace_6901036 : CollatzResearch.WordTrace tailWord_6901036 prefixEnd_6901036 3543548481981166898612719 := by
  unfold tailWord_6901036
  simp only [CollatzResearch.WordTrace]
  refine ⟨125850730513366324980261481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167800974017821766640348641 125850730513366324980261481)
  ·
    refine ⟨94388047885024743735196111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125850730513366324980261481 94388047885024743735196111)
    ·
      refine ⟨141582071827537115602794167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94388047885024743735196111 141582071827537115602794167)
      ·
        refine ⟨212373107741305673404191251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141582071827537115602794167 212373107741305673404191251)
        ·
          refine ⟨318559661611958510106286877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212373107741305673404191251 318559661611958510106286877)
          ·
            refine ⟨119459873104484441289857579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318559661611958510106286877 119459873104484441289857579)
            ·
              refine ⟨179189809656726661934786369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119459873104484441289857579 179189809656726661934786369)
              ·
                refine ⟨134392357242544996451089777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179189809656726661934786369 134392357242544996451089777)
                ·
                  refine ⟨100794267931908747338317333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134392357242544996451089777 100794267931908747338317333)
                  ·
                    refine ⟨4724731309308222531483625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100794267931908747338317333 4724731309308222531483625)
                    ·
                      refine ⟨3543548481981166898612719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724731309308222531483625 3543548481981166898612719)
                      ·
                        rfl

theorem cell23_6901036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_6901036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901036 prefixEnd_6901036 := by exact prefixLift 6901036
  have htrace : WordTrace (prefixWord ++ tailWord_6901036) baseStart_6901036 baseEnd_6901036 := by
    simpa [prefixWord, tailWord_6901036, baseEnd_6901036] using wordTrace_append hprefix tailTrace_6901036
  have hstable : (prefixWord ++ tailWord_6901036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901036).length < 2 ^ (prefixWord ++ tailWord_6901036).sum := by decide
  have hdescent : baseEnd_6901036 < baseStart_6901036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901039 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_6901039 : Nat := 118140960795 + 6901039 * 2 ^ 59
def prefixEnd_6901039 : Nat := 4983230072969 + 3 ^ 40 * 6901039 * 2
def baseEnd_6901039 : Nat := 3543550022423130386875205

theorem tailTrace_6901039 : CollatzResearch.WordTrace tailWord_6901039 prefixEnd_6901039 3543550022423130386875205 := by
  unfold tailWord_6901039
  simp only [CollatzResearch.WordTrace]
  refine ⟨251701570445721781472882171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167801046963814520981921447 251701570445721781472882171)
  ·
    refine ⟨377552355668582672209323257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251701570445721781472882171 377552355668582672209323257)
    ·
      refine ⟨283164266751437004156992443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377552355668582672209323257 283164266751437004156992443)
      ·
        refine ⟨424746400127155506235488665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283164266751437004156992443 424746400127155506235488665)
        ·
          refine ⟨318559800095366629676616499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424746400127155506235488665 318559800095366629676616499)
          ·
            refine ⟨477839700143049944514924749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318559800095366629676616499 477839700143049944514924749)
            ·
              refine ⟨179189887553643729193096781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 477839700143049944514924749 179189887553643729193096781)
              ·
                refine ⟨67196207832616398447411293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179189887553643729193096781 67196207832616398447411293)
                ·
                  refine ⟨25198577937231149417779235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67196207832616398447411293 25198577937231149417779235)
                  ·
                    refine ⟨37797866905846724126668853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25198577937231149417779235 37797866905846724126668853)
                    ·
                      refine ⟨3543550022423130386875205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37797866905846724126668853 3543550022423130386875205)
                      ·
                        rfl

theorem cell23_6901039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_6901039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901039 prefixEnd_6901039 := by exact prefixLift 6901039
  have htrace : WordTrace (prefixWord ++ tailWord_6901039) baseStart_6901039 baseEnd_6901039 := by
    simpa [prefixWord, tailWord_6901039, baseEnd_6901039] using wordTrace_append hprefix tailTrace_6901039
  have hstable : (prefixWord ++ tailWord_6901039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901039).length < 2 ^ (prefixWord ++ tailWord_6901039).sum := by decide
  have hdescent : baseEnd_6901039 < baseStart_6901039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901056 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_6901056 : Nat := 118140960795 + 6901056 * 2 ^ 59
def prefixEnd_6901056 : Nat := 4983230072969 + 3 ^ 40 * 6901056 * 2
def baseEnd_6901056 : Nat := 3543558751594256820362627

theorem tailTrace_6901056 : CollatzResearch.WordTrace tailWord_6901056 prefixEnd_6901056 3543558751594256820362627 := by
  unfold tailWord_6901056
  simp only [CollatzResearch.WordTrace]
  refine ⟨125851095243330096688125511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167801460324440128917500681 125851095243330096688125511)
  ·
    refine ⟨188776642864995145032188267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125851095243330096688125511 188776642864995145032188267)
    ·
      refine ⟨283164964297492717548282401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188776642864995145032188267 283164964297492717548282401)
      ·
        refine ⟨212373723223119538161211801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283164964297492717548282401 212373723223119538161211801)
        ·
          refine ⟨159280292417339653620908851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212373723223119538161211801 159280292417339653620908851)
          ·
            refine ⟨238920438626009480431363277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159280292417339653620908851 238920438626009480431363277)
            ·
              refine ⟨89595164484753555161761229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238920438626009480431363277 89595164484753555161761229)
              ·
                refine ⟨33598186681782583185660461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89595164484753555161761229 33598186681782583185660461)
                ·
                  refine ⟨12599320005668468694622673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33598186681782583185660461 12599320005668468694622673)
                  ·
                    refine ⟨9449490004251351520967005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12599320005668468694622673 9449490004251351520967005)
                    ·
                      refine ⟨3543558751594256820362627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9449490004251351520967005 3543558751594256820362627)
                      ·
                        rfl

theorem cell23_6901056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_6901056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901056 prefixEnd_6901056 := by exact prefixLift 6901056
  have htrace : WordTrace (prefixWord ++ tailWord_6901056) baseStart_6901056 baseEnd_6901056 := by
    simpa [prefixWord, tailWord_6901056, baseEnd_6901056] using wordTrace_append hprefix tailTrace_6901056
  have hstable : (prefixWord ++ tailWord_6901056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901056).length < 2 ^ (prefixWord ++ tailWord_6901056).sum := by decide
  have hdescent : baseEnd_6901056 < baseStart_6901056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901057 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6901057 : Nat := 118140960795 + 6901057 * 2 ^ 59
def prefixEnd_6901057 : Nat := 4983230072969 + 3 ^ 40 * 6901057 * 2
def baseEnd_6901057 : Nat := 3543559265074911316450123

theorem tailTrace_6901057 : CollatzResearch.WordTrace tailWord_6901057 prefixEnd_6901057 3543559265074911316450123 := by
  unfold tailWord_6901057
  simp only [CollatzResearch.WordTrace]
  refine ⟨251702226959656570547037425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167801484639771047031358283 251702226959656570547037425)
  ·
    refine ⟨188776670219742427910278069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251702226959656570547037425 188776670219742427910278069)
    ·
      refine ⟨17697812833100852616588569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188776670219742427910278069 17697812833100852616588569)
      ·
        refine ⟨13273359624825639462441427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17697812833100852616588569 13273359624825639462441427)
        ·
          refine ⟨19910039437238459193662141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13273359624825639462441427 19910039437238459193662141)
          ·
            refine ⟨7466264788964422197623303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19910039437238459193662141 7466264788964422197623303)
            ·
              refine ⟨11199397183446633296434955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466264788964422197623303 11199397183446633296434955)
              ·
                refine ⟨16799095775169949944652433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11199397183446633296434955 16799095775169949944652433)
                ·
                  refine ⟨12599321831377462458489325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16799095775169949944652433 12599321831377462458489325)
                  ·
                    refine ⟨4724745686766548421933497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12599321831377462458489325 4724745686766548421933497)
                    ·
                      refine ⟨3543559265074911316450123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724745686766548421933497 3543559265074911316450123)
                      ·
                        rfl

theorem cell23_6901057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6901057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901057 prefixEnd_6901057 := by exact prefixLift 6901057
  have htrace : WordTrace (prefixWord ++ tailWord_6901057) baseStart_6901057 baseEnd_6901057 := by
    simpa [prefixWord, tailWord_6901057, baseEnd_6901057] using wordTrace_append hprefix tailTrace_6901057
  have hstable : (prefixWord ++ tailWord_6901057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901057).length < 2 ^ (prefixWord ++ tailWord_6901057).sum := by decide
  have hdescent : baseEnd_6901057 < baseStart_6901057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901073 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_6901073 : Nat := 118140960795 + 6901073 * 2 ^ 59
def prefixEnd_6901073 : Nat := 4983230072969 + 3 ^ 40 * 6901073 * 2
def baseEnd_6901073 : Nat := 3543567480765383253850049

theorem tailTrace_6901073 : CollatzResearch.WordTrace tailWord_6901073 prefixEnd_6901073 3543567480765383253850049 := by
  unfold tailWord_6901073
  simp only [CollatzResearch.WordTrace]
  refine ⟨251702810527598605279619873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167801873685065736853079915 251702810527598605279619873)
  ·
    refine ⟨188777107895698953959714905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251702810527598605279619873 188777107895698953959714905)
    ·
      refine ⟨141582830921774215469786179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188777107895698953959714905 141582830921774215469786179)
      ·
        refine ⟨212374246382661323204679269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141582830921774215469786179 212374246382661323204679269)
        ·
          refine ⟨39820171196748998100877363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212374246382661323204679269 39820171196748998100877363)
          ·
            refine ⟨59730256795123497151316045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39820171196748998100877363 59730256795123497151316045)
            ·
              refine ⟨22398846298171311431743517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59730256795123497151316045 22398846298171311431743517)
              ·
                refine ⟨8399567361814241786903819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22398846298171311431743517 8399567361814241786903819)
                ·
                  refine ⟨12599351042721362680355729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8399567361814241786903819 12599351042721362680355729)
                  ·
                    refine ⟨9449513282041022010266797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12599351042721362680355729 9449513282041022010266797)
                    ·
                      refine ⟨3543567480765383253850049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9449513282041022010266797 3543567480765383253850049)
                      ·
                        rfl

theorem cell23_6901073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_6901073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901073 prefixEnd_6901073 := by exact prefixLift 6901073
  have htrace : WordTrace (prefixWord ++ tailWord_6901073) baseStart_6901073 baseEnd_6901073 := by
    simpa [prefixWord, tailWord_6901073, baseEnd_6901073] using wordTrace_append hprefix tailTrace_6901073
  have hstable : (prefixWord ++ tailWord_6901073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901073).length < 2 ^ (prefixWord ++ tailWord_6901073).sum := by decide
  have hdescent : baseEnd_6901073 < baseStart_6901073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901089 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_6901089 : Nat := 118140960795 + 6901089 * 2 ^ 59
def prefixEnd_6901089 : Nat := 4983230072969 + 3 ^ 40 * 6901089 * 2
def baseEnd_6901089 : Nat := 1181191898818618397083325

theorem tailTrace_6901089 : CollatzResearch.WordTrace tailWord_6901089 prefixEnd_6901089 1181191898818618397083325 := by
  unfold tailWord_6901089
  simp only [CollatzResearch.WordTrace]
  refine ⟨251703394095540640012202321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167802262730360426674801547 251703394095540640012202321)
  ·
    refine ⟨188777545571655480009151741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251703394095540640012202321 188777545571655480009151741)
    ·
      refine ⟨70791579589370805003431903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188777545571655480009151741 70791579589370805003431903)
      ·
        refine ⟨106187369384056207505147855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70791579589370805003431903 106187369384056207505147855)
        ·
          refine ⟨159281054076084311257721783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106187369384056207505147855 159281054076084311257721783)
          ·
            refine ⟨238921581114126466886582675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159281054076084311257721783 238921581114126466886582675)
            ·
              refine ⟨358382371671189700329874013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238921581114126466886582675 358382371671189700329874013)
              ·
                refine ⟨134393389376696137623702755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358382371671189700329874013 134393389376696137623702755)
                ·
                  refine ⟨201590084065044206435554133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134393389376696137623702755 201590084065044206435554133)
                  ·
                    refine ⟨1181191898818618397083325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 201590084065044206435554133 1181191898818618397083325)
                    ·
                      rfl

theorem cell23_6901089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_6901089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901089 prefixEnd_6901089 := by exact prefixLift 6901089
  have htrace : WordTrace (prefixWord ++ tailWord_6901089) baseStart_6901089 baseEnd_6901089 := by
    simpa [prefixWord, tailWord_6901089, baseEnd_6901089] using wordTrace_append hprefix tailTrace_6901089
  have hstable : (prefixWord ++ tailWord_6901089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901089).length < 2 ^ (prefixWord ++ tailWord_6901089).sum := by decide
  have hdescent : baseEnd_6901089 < baseStart_6901089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901099 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_6901099 : Nat := 118140960795 + 6901099 * 2 ^ 59
def prefixEnd_6901099 : Nat := 4983230072969 + 3 ^ 40 * 6901099 * 2
def baseEnd_6901099 : Nat := 3543580831262400152124929

theorem tailTrace_6901099 : CollatzResearch.WordTrace tailWord_6901099 prefixEnd_6901099 3543580831262400152124929 := by
  unfold tailWord_6901099
  simp only [CollatzResearch.WordTrace]
  refine ⟨251703758825504411720066351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167802505883669607813377567 251703758825504411720066351)
  ·
    refine ⟨377555638238256617580099527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251703758825504411720066351 377555638238256617580099527)
    ·
      refine ⟨566333457357384926370149291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377555638238256617580099527 566333457357384926370149291)
      ·
        refine ⟨849500186036077389555223937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566333457357384926370149291 849500186036077389555223937)
        ·
          refine ⟨637125139527058042166417953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849500186036077389555223937 637125139527058042166417953)
          ·
            refine ⟨477843854645293531624813465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637125139527058042166417953 477843854645293531624813465)
            ·
              refine ⟨358382890983970148718610099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477843854645293531624813465 358382890983970148718610099)
              ·
                refine ⟨537574336475955223077915149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358382890983970148718610099 537574336475955223077915149)
                ·
                  refine ⟨201590376178483208654218181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537574336475955223077915149 201590376178483208654218181)
                  ·
                    refine ⟨37798195533465601622665909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201590376178483208654218181 37798195533465601622665909)
                    ·
                      refine ⟨3543580831262400152124929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37798195533465601622665909 3543580831262400152124929)
                      ·
                        rfl

theorem cell23_6901099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_6901099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901099 prefixEnd_6901099 := by exact prefixLift 6901099
  have htrace : WordTrace (prefixWord ++ tailWord_6901099) baseStart_6901099 baseEnd_6901099 := by
    simpa [prefixWord, tailWord_6901099, baseEnd_6901099] using wordTrace_append hprefix tailTrace_6901099
  have hstable : (prefixWord ++ tailWord_6901099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901099).length < 2 ^ (prefixWord ++ tailWord_6901099).sum := by decide
  have hdescent : baseEnd_6901099 < baseStart_6901099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901113 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 3, 3, 2]
def baseStart_6901113 : Nat := 118140960795 + 6901113 * 2 ^ 59
def prefixEnd_6901113 : Nat := 4983230072969 + 3 ^ 40 * 6901113 * 2
def baseEnd_6901113 : Nat := 3543588019991563097349865

theorem tailTrace_6901113 : CollatzResearch.WordTrace tailWord_6901113 prefixEnd_6901113 3543588019991563097349865 := by
  unfold tailWord_6901113
  simp only [CollatzResearch.WordTrace]
  refine ⟨251704269447453692111075993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167802846298302461407383995 251704269447453692111075993)
  ·
    refine ⟨188778202085590269083306995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251704269447453692111075993 188778202085590269083306995)
    ·
      refine ⟨283167303128385403624960493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188778202085590269083306995 283167303128385403624960493)
      ·
        refine ⟨106187738673144526359360185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283167303128385403624960493 106187738673144526359360185)
        ·
          refine ⟨79640804004858394769520139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106187738673144526359360185 79640804004858394769520139)
          ·
            refine ⟨119461206007287592154280209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79640804004858394769520139 119461206007287592154280209)
            ·
              refine ⟨89595904505465694115710157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119461206007287592154280209 89595904505465694115710157)
              ·
                refine ⟨33598464189549635293391309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89595904505465694115710157 33598464189549635293391309)
                ·
                  refine ⟨12599424071081113235021741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33598464189549635293391309 12599424071081113235021741)
                  ·
                    refine ⟨4724784026655417463133153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12599424071081113235021741 4724784026655417463133153)
                    ·
                      refine ⟨3543588019991563097349865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724784026655417463133153 3543588019991563097349865)
                      ·
                        rfl

theorem cell23_6901113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_6901113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901113 prefixEnd_6901113 := by exact prefixLift 6901113
  have htrace : WordTrace (prefixWord ++ tailWord_6901113) baseStart_6901113 baseEnd_6901113 := by
    simpa [prefixWord, tailWord_6901113, baseEnd_6901113] using wordTrace_append hprefix tailTrace_6901113
  have hstable : (prefixWord ++ tailWord_6901113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901113).length < 2 ^ (prefixWord ++ tailWord_6901113).sum := by decide
  have hdescent : baseEnd_6901113 < baseStart_6901113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901121 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6901121 : Nat := 118140960795 + 6901121 * 2 ^ 59
def prefixEnd_6901121 : Nat := 4983230072969 + 3 ^ 40 * 6901121 * 2
def baseEnd_6901121 : Nat := 3543592127836799066049829

theorem tailTrace_6901121 : CollatzResearch.WordTrace tailWord_6901121 prefixEnd_6901121 3543592127836799066049829 := by
  unfold tailWord_6901121
  simp only [CollatzResearch.WordTrace]
  refine ⟨251704561231424709477367217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167803040820949806318244811 251704561231424709477367217)
  ·
    refine ⟨188778420923568532108025413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251704561231424709477367217 188778420923568532108025413)
    ·
      refine ⟨35395953923169099770254765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188778420923568532108025413 35395953923169099770254765)
      ·
        refine ⟨13273482721188412413845537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35395953923169099770254765 13273482721188412413845537)
        ·
          refine ⟨9955112040891309310384153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13273482721188412413845537 9955112040891309310384153)
          ·
            refine ⟨7466334030668481982788115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9955112040891309310384153 7466334030668481982788115)
            ·
              refine ⟨11199501046002722974182173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466334030668481982788115 11199501046002722974182173)
              ·
                refine ⟨4199812892251021115318315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11199501046002722974182173 4199812892251021115318315)
                ·
                  refine ⟨6299719338376531672977473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199812892251021115318315 6299719338376531672977473)
                  ·
                    refine ⟨4724789503782398754733105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299719338376531672977473 4724789503782398754733105)
                    ·
                      refine ⟨3543592127836799066049829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724789503782398754733105 3543592127836799066049829)
                      ·
                        rfl

theorem cell23_6901121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6901121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901121 prefixEnd_6901121 := by exact prefixLift 6901121
  have htrace : WordTrace (prefixWord ++ tailWord_6901121) baseStart_6901121 baseEnd_6901121 := by
    simpa [prefixWord, tailWord_6901121, baseEnd_6901121] using wordTrace_append hprefix tailTrace_6901121
  have hstable : (prefixWord ++ tailWord_6901121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901121).length < 2 ^ (prefixWord ++ tailWord_6901121).sum := by decide
  have hdescent : baseEnd_6901121 < baseStart_6901121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901138 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6901138 : Nat := 118140960795 + 6901138 * 2 ^ 59
def prefixEnd_6901138 : Nat := 4983230072969 + 3 ^ 40 * 6901138 * 2
def baseEnd_6901138 : Nat := 3543600857007925499537251

theorem tailTrace_6901138 : CollatzResearch.WordTrace tailWord_6901138 prefixEnd_6901138 3543600857007925499537251 := by
  unfold tailWord_6901138
  simp only [CollatzResearch.WordTrace]
  refine ⟨62926295318090780345184017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167803454181575414253824045 62926295318090780345184017)
  ·
    refine ⟨47194721488568085258888013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62926295318090780345184017 47194721488568085258888013)
    ·
      refine ⟨17698020558213031972083005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47194721488568085258888013 17698020558213031972083005)
      ·
        refine ⟨6636757709329886989531127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17698020558213031972083005 6636757709329886989531127)
        ·
          refine ⟨9955136563994830484296691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636757709329886989531127 9955136563994830484296691)
          ·
            refine ⟨14932704845992245726445037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955136563994830484296691 14932704845992245726445037)
            ·
              refine ⟨5599764317247092147416889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14932704845992245726445037 5599764317247092147416889)
              ·
                refine ⟨4199823237935319110562667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599764317247092147416889 4199823237935319110562667)
                ·
                  refine ⟨6299734856902978665844001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199823237935319110562667 6299734856902978665844001)
                  ·
                    refine ⟨4724801142677233999383001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299734856902978665844001 4724801142677233999383001)
                    ·
                      refine ⟨3543600857007925499537251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4724801142677233999383001 3543600857007925499537251)
                      ·
                        rfl

theorem cell23_6901138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6901138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901138 prefixEnd_6901138 := by exact prefixLift 6901138
  have htrace : WordTrace (prefixWord ++ tailWord_6901138) baseStart_6901138 baseEnd_6901138 := by
    simpa [prefixWord, tailWord_6901138, baseEnd_6901138] using wordTrace_append hprefix tailTrace_6901138
  have hstable : (prefixWord ++ tailWord_6901138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901138).length < 2 ^ (prefixWord ++ tailWord_6901138).sum := by decide
  have hdescent : baseEnd_6901138 < baseStart_6901138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901146 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6901146 : Nat := 118140960795 + 6901146 * 2 ^ 59
def prefixEnd_6901146 : Nat := 4983230072969 + 3 ^ 40 * 6901146 * 2
def baseEnd_6901146 : Nat := 3543604964853161468237213

theorem tailTrace_6901146 : CollatzResearch.WordTrace tailWord_6901146 prefixEnd_6901146 3543604964853161468237213 := by
  unfold tailWord_6901146
  simp only [CollatzResearch.WordTrace]
  refine ⟨62926368264083534686756823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167803648704222759164684861 62926368264083534686756823)
  ·
    refine ⟨94389552396125302030135235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62926368264083534686756823 94389552396125302030135235)
    ·
      refine ⟨141584328594187953045202853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94389552396125302030135235 141584328594187953045202853)
      ·
        refine ⟨26547061611410241195975535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141584328594187953045202853 26547061611410241195975535)
        ·
          refine ⟨39820592417115361793963303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26547061611410241195975535 39820592417115361793963303)
          ·
            refine ⟨59730888625673042690944955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39820592417115361793963303 59730888625673042690944955)
            ·
              refine ⟨89596332938509564036417433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59730888625673042690944955 89596332938509564036417433)
              ·
                refine ⟨67197249703882173027313075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89596332938509564036417433 67197249703882173027313075)
                ·
                  refine ⟨100795874555823259540969613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67197249703882173027313075 100795874555823259540969613)
                  ·
                    refine ⟨37798452958433722327863605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100795874555823259540969613 37798452958433722327863605)
                    ·
                      refine ⟨3543604964853161468237213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37798452958433722327863605 3543604964853161468237213)
                      ·
                        rfl

theorem cell23_6901146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6901146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901146 prefixEnd_6901146 := by exact prefixLift 6901146
  have htrace : WordTrace (prefixWord ++ tailWord_6901146) baseStart_6901146 baseEnd_6901146 := by
    simpa [prefixWord, tailWord_6901146, baseEnd_6901146] using wordTrace_append hprefix tailTrace_6901146
  have hstable : (prefixWord ++ tailWord_6901146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901146).length < 2 ^ (prefixWord ++ tailWord_6901146).sum := by decide
  have hdescent : baseEnd_6901146 < baseStart_6901146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901154 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6901154 : Nat := 118140960795 + 6901154 * 2 ^ 59
def prefixEnd_6901154 : Nat := 4983230072969 + 3 ^ 40 * 6901154 * 2
def baseEnd_6901154 : Nat := 3543609072698397436937177

theorem tailTrace_6901154 : CollatzResearch.WordTrace tailWord_6901154 prefixEnd_6901154 3543609072698397436937177 := by
  unfold tailWord_6901154
  simp only [CollatzResearch.WordTrace]
  refine ⟨62926441210076289028329629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167803843226870104075545677 62926441210076289028329629)
  ·
    refine ⟨23597415453778608385623611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62926441210076289028329629 23597415453778608385623611)
    ·
      refine ⟨35396123180667912578435417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23597415453778608385623611 35396123180667912578435417)
      ·
        refine ⟨26547092385500934433826563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35396123180667912578435417 26547092385500934433826563)
        ·
          refine ⟨39820638578251401650739845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26547092385500934433826563 39820638578251401650739845)
          ·
            refine ⟨7466369733422137809513721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39820638578251401650739845 7466369733422137809513721)
            ·
              refine ⟨5599777300066603357135291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466369733422137809513721 5599777300066603357135291)
              ·
                refine ⟨8399665950099905035702937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599777300066603357135291 8399665950099905035702937)
                ·
                  refine ⟨6299749462574928776777203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8399665950099905035702937 6299749462574928776777203)
                  ·
                    refine ⟨9449624193862393165165805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6299749462574928776777203 9449624193862393165165805)
                    ·
                      refine ⟨3543609072698397436937177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9449624193862393165165805 3543609072698397436937177)
                      ·
                        rfl

theorem cell23_6901154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6901154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901154 prefixEnd_6901154 := by exact prefixLift 6901154
  have htrace : WordTrace (prefixWord ++ tailWord_6901154) baseStart_6901154 baseEnd_6901154 := by
    simpa [prefixWord, tailWord_6901154, baseEnd_6901154] using wordTrace_append hprefix tailTrace_6901154
  have hstable : (prefixWord ++ tailWord_6901154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901154).length < 2 ^ (prefixWord ++ tailWord_6901154).sum := by decide
  have hdescent : baseEnd_6901154 < baseStart_6901154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901156 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6901156 : Nat := 118140960795 + 6901156 * 2 ^ 59
def prefixEnd_6901156 : Nat := 4983230072969 + 3 ^ 40 * 6901156 * 2
def baseEnd_6901156 : Nat := 3543610099659706429112167

theorem tailTrace_6901156 : CollatzResearch.WordTrace tailWord_6901156 prefixEnd_6901156 3543610099659706429112167 := by
  unfold tailWord_6901156
  simp only [CollatzResearch.WordTrace]
  refine ⟨125852918893148955227445661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167803891857531940303260881 125852918893148955227445661)
  ·
    refine ⟨47194844584930858210292123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125852918893148955227445661 47194844584930858210292123)
    ·
      refine ⟨70792266877396287315438185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47194844584930858210292123 70792266877396287315438185)
      ·
        refine ⟨53094200158047215486578639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70792266877396287315438185 53094200158047215486578639)
        ·
          refine ⟨79641300237070823229867959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53094200158047215486578639 79641300237070823229867959)
          ·
            refine ⟨119461950355606234844801939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79641300237070823229867959 119461950355606234844801939)
            ·
              refine ⟨179192925533409352267202909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119461950355606234844801939 179192925533409352267202909)
              ·
                refine ⟨67197347075028507100201091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179192925533409352267202909 67197347075028507100201091)
                ·
                  refine ⟨100796020612542760650301637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67197347075028507100201091 100796020612542760650301637)
                  ·
                    refine ⟨18899253864851767621931557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100796020612542760650301637 18899253864851767621931557)
                    ·
                      refine ⟨3543610099659706429112167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18899253864851767621931557 3543610099659706429112167)
                      ·
                        rfl

theorem cell23_6901156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6901156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901156 prefixEnd_6901156 := by exact prefixLift 6901156
  have htrace : WordTrace (prefixWord ++ tailWord_6901156) baseStart_6901156 baseEnd_6901156 := by
    simpa [prefixWord, tailWord_6901156, baseEnd_6901156] using wordTrace_append hprefix tailTrace_6901156
  have hstable : (prefixWord ++ tailWord_6901156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901156).length < 2 ^ (prefixWord ++ tailWord_6901156).sum := by decide
  have hdescent : baseEnd_6901156 < baseStart_6901156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901233 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_6901233 : Nat := 118140960795 + 6901233 * 2 ^ 59
def prefixEnd_6901233 : Nat := 4983230072969 + 3 ^ 40 * 6901233 * 2
def baseEnd_6901233 : Nat := 3543649637670102627849313

theorem tailTrace_6901233 : CollatzResearch.WordTrace tailWord_6901233 prefixEnd_6901233 3543649637670102627849313 := by
  unfold tailWord_6901233
  simp only [CollatzResearch.WordTrace]
  refine ⟨251708646207018952605444353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167805764138012635070296235 251708646207018952605444353)
  ·
    refine ⟨188781484655264214454083265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251708646207018952605444353 188781484655264214454083265)
    ·
      refine ⟨141586113491448160840562449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188781484655264214454083265 141586113491448160840562449)
      ·
        refine ⟨106189585118586120630421837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141586113491448160840562449 106189585118586120630421837)
        ·
          refine ⟨39821094419469795236408189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106189585118586120630421837 39821094419469795236408189)
          ·
            refine ⟨14932910407301173213653071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39821094419469795236408189 14932910407301173213653071)
            ·
              refine ⟨22399365610951759820479607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14932910407301173213653071 22399365610951759820479607)
              ·
                refine ⟨33599048416427639730719411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22399365610951759820479607 33599048416427639730719411)
                ·
                  refine ⟨50398572624641459596079117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33599048416427639730719411 50398572624641459596079117)
                  ·
                    refine ⟨18899464734240547348529669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50398572624641459596079117 18899464734240547348529669)
                    ·
                      refine ⟨3543649637670102627849313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18899464734240547348529669 3543649637670102627849313)
                      ·
                        rfl

theorem cell23_6901233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_6901233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901233 prefixEnd_6901233 := by exact prefixLift 6901233
  have htrace : WordTrace (prefixWord ++ tailWord_6901233) baseStart_6901233 baseEnd_6901233 := by
    simpa [prefixWord, tailWord_6901233, baseEnd_6901233] using wordTrace_append hprefix tailTrace_6901233
  have hstable : (prefixWord ++ tailWord_6901233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901233).length < 2 ^ (prefixWord ++ tailWord_6901233).sum := by decide
  have hdescent : baseEnd_6901233 < baseStart_6901233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901253 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_6901253 : Nat := 118140960795 + 6901253 * 2 ^ 59
def prefixEnd_6901253 : Nat := 4983230072969 + 3 ^ 40 * 6901253 * 2
def baseEnd_6901253 : Nat := 3543659907283192549599221

theorem tailTrace_6901253 : CollatzResearch.WordTrace tailWord_6901253 prefixEnd_6901253 3543659907283192549599221 := by
  unfold tailWord_6901253
  simp only [CollatzResearch.WordTrace]
  refine ⟨251709375666946496021172413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167806250444630997347448275 251709375666946496021172413)
  ·
    refine ⟨94391015875104936007939655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251709375666946496021172413 94391015875104936007939655)
    ·
      refine ⟨141586523812657404011909483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94391015875104936007939655 141586523812657404011909483)
      ·
        refine ⟨212379785718986106017864225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141586523812657404011909483 212379785718986106017864225)
        ·
          refine ⟨159284839289239579513398169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212379785718986106017864225 159284839289239579513398169)
          ·
            refine ⟨119463629466929684635048627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159284839289239579513398169 119463629466929684635048627)
            ·
              refine ⟨179195444200394526952572941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119463629466929684635048627 179195444200394526952572941)
              ·
                refine ⟨67198291575147947607214853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179195444200394526952572941 67198291575147947607214853)
                ·
                  refine ⟨12599679670340240176352785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67198291575147947607214853 12599679670340240176352785)
                  ·
                    refine ⟨9449759752755180132264589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12599679670340240176352785 9449759752755180132264589)
                    ·
                      refine ⟨3543659907283192549599221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9449759752755180132264589 3543659907283192549599221)
                      ·
                        rfl

theorem cell23_6901253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_6901253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901253 prefixEnd_6901253 := by exact prefixLift 6901253
  have htrace : WordTrace (prefixWord ++ tailWord_6901253) baseStart_6901253 baseEnd_6901253 := by
    simpa [prefixWord, tailWord_6901253, baseEnd_6901253] using wordTrace_append hprefix tailTrace_6901253
  have hstable : (prefixWord ++ tailWord_6901253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901253).length < 2 ^ (prefixWord ++ tailWord_6901253).sum := by decide
  have hdescent : baseEnd_6901253 < baseStart_6901253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901294 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6901294 : Nat := 118140960795 + 6901294 * 2 ^ 59
def prefixEnd_6901294 : Nat := 4983230072969 + 3 ^ 40 * 6901294 * 2
def baseEnd_6901294 : Nat := 1181226986663342296395511

theorem tailTrace_6901294 : CollatzResearch.WordTrace tailWord_6901294 prefixEnd_6901294 1181226986663342296395511 := by
  unfold tailWord_6901294
  simp only [CollatzResearch.WordTrace]
  refine ⟨31463858882474745002926867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167807247373198640015609957 31463858882474745002926867)
  ·
    refine ⟨47195788323712117504390301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31463858882474745002926867 47195788323712117504390301)
    ·
      refine ⟨17698420621392044064146363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47195788323712117504390301 17698420621392044064146363)
      ·
        refine ⟨26547630932088066096219545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17698420621392044064146363 26547630932088066096219545)
        ·
          refine ⟨19910723199066049572164659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26547630932088066096219545 19910723199066049572164659)
          ·
            refine ⟨29866084798599074358246989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19910723199066049572164659 29866084798599074358246989)
            ·
              refine ⟨11199781799474652884342621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29866084798599074358246989 11199781799474652884342621)
              ·
                refine ⟨4199918174802994831628483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11199781799474652884342621 4199918174802994831628483)
                ·
                  refine ⟨6299877262204492247442725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199918174802994831628483 6299877262204492247442725)
                  ·
                    refine ⟨1181226986663342296395511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299877262204492247442725 1181226986663342296395511)
                    ·
                      rfl

theorem cell23_6901294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6901294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901294 prefixEnd_6901294 := by exact prefixLift 6901294
  have htrace : WordTrace (prefixWord ++ tailWord_6901294) baseStart_6901294 baseEnd_6901294 := by
    simpa [prefixWord, tailWord_6901294, baseEnd_6901294] using wordTrace_append hprefix tailTrace_6901294
  have hstable : (prefixWord ++ tailWord_6901294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901294).length < 2 ^ (prefixWord ++ tailWord_6901294).sum := by decide
  have hdescent : baseEnd_6901294 < baseStart_6901294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901323 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4]
def baseStart_6901323 : Nat := 118140960795 + 6901323 * 2 ^ 59
def prefixEnd_6901323 : Nat := 4983230072969 + 3 ^ 40 * 6901323 * 2
def baseEnd_6901323 : Nat := 3543695850929007275723899

theorem tailTrace_6901323 : CollatzResearch.WordTrace tailWord_6901323 prefixEnd_6901323 3543695850929007275723899 := by
  unfold tailWord_6901323
  simp only [CollatzResearch.WordTrace]
  refine ⟨251711928776692897976220623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167807952517795265317480415 251711928776692897976220623)
  ·
    refine ⟨377567893165039346964330935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251711928776692897976220623 377567893165039346964330935)
    ·
      refine ⟨566351839747559020446496403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377567893165039346964330935 566351839747559020446496403)
      ·
        refine ⟨849527759621338530669744605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566351839747559020446496403 849527759621338530669744605)
        ·
          refine ⟨318572909858001949001154227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849527759621338530669744605 318572909858001949001154227)
          ·
            refine ⟨477859364787002923501731341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318572909858001949001154227 477859364787002923501731341)
            ·
              refine ⟨179197261795126096313149253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 477859364787002923501731341 179197261795126096313149253)
              ·
                refine ⟨33599486586586143058715485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179197261795126096313149253 33599486586586143058715485)
                ·
                  refine ⟨12599807469969803647018307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33599486586586143058715485 12599807469969803647018307)
                  ·
                    refine ⟨18899711204954705470527461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12599807469969803647018307 18899711204954705470527461)
                    ·
                      refine ⟨3543695850929007275723899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18899711204954705470527461 3543695850929007275723899)
                      ·
                        rfl

theorem cell23_6901323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4].length) (baseStart_6901323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901323 prefixEnd_6901323 := by exact prefixLift 6901323
  have htrace : WordTrace (prefixWord ++ tailWord_6901323) baseStart_6901323 baseEnd_6901323 := by
    simpa [prefixWord, tailWord_6901323, baseEnd_6901323] using wordTrace_append hprefix tailTrace_6901323
  have hstable : (prefixWord ++ tailWord_6901323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901323).length < 2 ^ (prefixWord ++ tailWord_6901323).sum := by decide
  have hdescent : baseEnd_6901323 < baseStart_6901323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901333 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_6901333 : Nat := 118140960795 + 6901333 * 2 ^ 59
def prefixEnd_6901333 : Nat := 4983230072969 + 3 ^ 40 * 6901333 * 2
def baseEnd_6901333 : Nat := 1181233661911850745532951

theorem tailTrace_6901333 : CollatzResearch.WordTrace tailWord_6901333 prefixEnd_6901333 1181233661911850745532951 := by
  unfold tailWord_6901333
  simp only [CollatzResearch.WordTrace]
  refine ⟨251712293506656669684084653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167808195671104446456056435 251712293506656669684084653)
  ·
    refine ⟨94392110064996251131531745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251712293506656669684084653 94392110064996251131531745)
    ·
      refine ⟨70794082548747188348648809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94392110064996251131531745 70794082548747188348648809)
      ·
        refine ⟨53095561911560391261486607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70794082548747188348648809 53095561911560391261486607)
        ·
          refine ⟨79643342867340586892229911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53095561911560391261486607 79643342867340586892229911)
          ·
            refine ⟨119465014301010880338344867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79643342867340586892229911 119465014301010880338344867)
            ·
              refine ⟨179197521451516320507517301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119465014301010880338344867 179197521451516320507517301)
              ·
                refine ⟨16799767636079655047579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179197521451516320507517301 16799767636079655047579747)
                ·
                  refine ⟨25199651454119482571369621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16799767636079655047579747 25199651454119482571369621)
                  ·
                    refine ⟨1181233661911850745532951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25199651454119482571369621 1181233661911850745532951)
                    ·
                      rfl

theorem cell23_6901333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_6901333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901333 prefixEnd_6901333 := by exact prefixLift 6901333
  have htrace : WordTrace (prefixWord ++ tailWord_6901333) baseStart_6901333 baseEnd_6901333 := by
    simpa [prefixWord, tailWord_6901333, baseEnd_6901333] using wordTrace_append hprefix tailTrace_6901333
  have hstable : (prefixWord ++ tailWord_6901333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901333).length < 2 ^ (prefixWord ++ tailWord_6901333).sum := by decide
  have hdescent : baseEnd_6901333 < baseStart_6901333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901353 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_6901353 : Nat := 118140960795 + 6901353 * 2 ^ 59
def prefixEnd_6901353 : Nat := 4983230072969 + 3 ^ 40 * 6901353 * 2
def baseEnd_6901353 : Nat := 3543711255348642158348761

theorem tailTrace_6901353 : CollatzResearch.WordTrace tailWord_6901353 prefixEnd_6901353 3543711255348642158348761 := by
  unfold tailWord_6901353
  simp only [CollatzResearch.WordTrace]
  refine ⟨251713022966584213099812713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167808681977722808733208475 251713022966584213099812713)
  ·
    refine ⟨188784767224938159824859535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251713022966584213099812713 188784767224938159824859535)
    ·
      refine ⟨283177150837407239737289303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188784767224938159824859535 283177150837407239737289303)
      ·
        refine ⟨424765726256110859605933955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283177150837407239737289303 424765726256110859605933955)
        ·
          refine ⟨637148589384166289408900933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424765726256110859605933955 637148589384166289408900933)
          ·
            refine ⟨119465360509531179264168925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637148589384166289408900933 119465360509531179264168925)
            ·
              refine ⟨44799510191074192224063347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119465360509531179264168925 44799510191074192224063347)
              ·
                refine ⟨67199265286611288336095021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44799510191074192224063347 67199265286611288336095021)
                ·
                  refine ⟨25199724482479233126035633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67199265286611288336095021 25199724482479233126035633)
                  ·
                    refine ⟨18899793361859424844526725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25199724482479233126035633 18899793361859424844526725)
                    ·
                      refine ⟨3543711255348642158348761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18899793361859424844526725 3543711255348642158348761)
                      ·
                        rfl

theorem cell23_6901353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_6901353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901353 prefixEnd_6901353 := by exact prefixLift 6901353
  have htrace : WordTrace (prefixWord ++ tailWord_6901353) baseStart_6901353 baseEnd_6901353 := by
    simpa [prefixWord, tailWord_6901353, baseEnd_6901353] using wordTrace_append hprefix tailTrace_6901353
  have hstable : (prefixWord ++ tailWord_6901353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901353).length < 2 ^ (prefixWord ++ tailWord_6901353).sum := by decide
  have hdescent : baseEnd_6901353 < baseStart_6901353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901360 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_6901360 : Nat := 118140960795 + 6901360 * 2 ^ 59
def prefixEnd_6901360 : Nat := 4983230072969 + 3 ^ 40 * 6901360 * 2
def baseEnd_6901360 : Nat := 3543714849713223630961229

theorem tailTrace_6901360 : CollatzResearch.WordTrace tailWord_6901360 prefixEnd_6901360 3543714849713223630961229 := by
  unfold tailWord_6901360
  simp only [CollatzResearch.WordTrace]
  refine ⟨125856639138779426647658767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167808852185039235530211689 125856639138779426647658767)
  ·
    refine ⟨188784958708169139971488151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125856639138779426647658767 188784958708169139971488151)
    ·
      refine ⟨283177438062253709957232227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188784958708169139971488151 283177438062253709957232227)
      ·
        refine ⟨424766157093380564935848341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283177438062253709957232227 424766157093380564935848341)
        ·
          refine ⟨19910913613752213981367891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 424766157093380564935848341 19910913613752213981367891)
          ·
            refine ⟨29866370420628320972051837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19910913613752213981367891 29866370420628320972051837)
            ·
              refine ⟨11199888907735620364519439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29866370420628320972051837 11199888907735620364519439)
              ·
                refine ⟨16799833361603430546779159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11199888907735620364519439 16799833361603430546779159)
                ·
                  refine ⟨25199750042405145820168739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16799833361603430546779159 25199750042405145820168739)
                  ·
                    refine ⟨37799625063607718730253109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25199750042405145820168739 37799625063607718730253109)
                    ·
                      refine ⟨3543714849713223630961229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37799625063607718730253109 3543714849713223630961229)
                      ·
                        rfl

theorem cell23_6901360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_6901360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901360 prefixEnd_6901360 := by exact prefixLift 6901360
  have htrace : WordTrace (prefixWord ++ tailWord_6901360) baseStart_6901360 baseEnd_6901360 := by
    simpa [prefixWord, tailWord_6901360, baseEnd_6901360] using wordTrace_append hprefix tailTrace_6901360
  have hstable : (prefixWord ++ tailWord_6901360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901360).length < 2 ^ (prefixWord ++ tailWord_6901360).sum := by decide
  have hdescent : baseEnd_6901360 < baseStart_6901360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901423 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 4, 6]
def baseStart_6901423 : Nat := 118140960795 + 6901423 * 2 ^ 59
def prefixEnd_6901423 : Nat := 4983230072969 + 3 ^ 40 * 6901423 * 2
def baseEnd_6901423 : Nat := 1181249066331485628157813

theorem tailTrace_6901423 : CollatzResearch.WordTrace tailWord_6901423 prefixEnd_6901423 1181249066331485628157813 := by
  unfold tailWord_6901423
  simp only [CollatzResearch.WordTrace]
  refine ⟨251715576076330615054860923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167810384050887076703240615 251715576076330615054860923)
  ·
    refine ⟨377573364114495922582291385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251715576076330615054860923 377573364114495922582291385)
    ·
      refine ⟨283180023085871941936718539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377573364114495922582291385 283180023085871941936718539)
      ·
        refine ⟨424770034628807912905077809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283180023085871941936718539 424770034628807912905077809)
        ·
          refine ⟨318577525971605934678808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424770034628807912905077809 318577525971605934678808357)
          ·
            refine ⟨59733286119676112752276567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318577525971605934678808357 59733286119676112752276567)
            ·
              refine ⟨89599929179514169128414851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59733286119676112752276567 89599929179514169128414851)
              ·
                refine ⟨134399893769271253692622277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89599929179514169128414851 134399893769271253692622277)
                ·
                  refine ⟨25199980081738360067366677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134399893769271253692622277 25199980081738360067366677)
                  ·
                    refine ⟨1181249066331485628157813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25199980081738360067366677 1181249066331485628157813)
                    ·
                      rfl

theorem cell23_6901423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_6901423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901423 prefixEnd_6901423 := by exact prefixLift 6901423
  have htrace : WordTrace (prefixWord ++ tailWord_6901423) baseStart_6901423 baseEnd_6901423 := by
    simpa [prefixWord, tailWord_6901423, baseEnd_6901423] using wordTrace_append hprefix tailTrace_6901423
  have hstable : (prefixWord ++ tailWord_6901423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901423).length < 2 ^ (prefixWord ++ tailWord_6901423).sum := by decide
  have hdescent : baseEnd_6901423 < baseStart_6901423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901500 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_6901500 : Nat := 118140960795 + 6901500 * 2 ^ 59
def prefixEnd_6901500 : Nat := 4983230072969 + 3 ^ 40 * 6901500 * 2
def baseEnd_6901500 : Nat := 1181262245668284361070195

theorem tailTrace_6901500 : CollatzResearch.WordTrace tailWord_6901500 prefixEnd_6901500 1181262245668284361070195 := by
  unfold tailWord_6901500
  simp only [CollatzResearch.WordTrace]
  refine ⟨125859192248525828602706977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167812256331367771470275969 125859192248525828602706977)
  ·
    refine ⟨94394394186394371452030233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125859192248525828602706977 94394394186394371452030233)
    ·
      refine ⟨70795795639795778589022675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94394394186394371452030233 70795795639795778589022675)
      ·
        refine ⟨106193693459693667883534013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70795795639795778589022675 106193693459693667883534013)
        ·
          refine ⟨39822635047385125456325255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106193693459693667883534013 39822635047385125456325255)
          ·
            refine ⟨59733952571077688184487883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39822635047385125456325255 59733952571077688184487883)
            ·
              refine ⟨89600928856616532276731825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59733952571077688184487883 89600928856616532276731825)
              ·
                refine ⟨67200696642462399207548869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89600928856616532276731825 67200696642462399207548869)
                ·
                  refine ⟨12600130620461699851415413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67200696642462399207548869 12600130620461699851415413)
                  ·
                    refine ⟨1181262245668284361070195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12600130620461699851415413 1181262245668284361070195)
                    ·
                      rfl

theorem cell23_6901500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_6901500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901500 prefixEnd_6901500 := by exact prefixLift 6901500
  have htrace : WordTrace (prefixWord ++ tailWord_6901500) baseStart_6901500 baseEnd_6901500 := by
    simpa [prefixWord, tailWord_6901500, baseEnd_6901500] using wordTrace_append hprefix tailTrace_6901500
  have hstable : (prefixWord ++ tailWord_6901500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901500).length < 2 ^ (prefixWord ++ tailWord_6901500).sum := by decide
  have hdescent : baseEnd_6901500 < baseStart_6901500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901537 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6901537 : Nat := 118140960795 + 6901537 * 2 ^ 59
def prefixEnd_6901537 : Nat := 4983230072969 + 3 ^ 40 * 6901537 * 2
def baseEnd_6901537 : Nat := 3543805735789069438447915

theorem tailTrace_6901537 : CollatzResearch.WordTrace tailWord_6901537 prefixEnd_6901537 3543805735789069438447915 := by
  unfold tailWord_6901537
  simp only [CollatzResearch.WordTrace]
  refine ⟨251719733997917612524510865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167813155998611741683007243 251719733997917612524510865)
  ·
    refine ⟨188789800498438209393383149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251719733997917612524510865 188789800498438209393383149)
    ·
      refine ⟨70796175186914328522518681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188789800498438209393383149 70796175186914328522518681)
      ·
        refine ⟨53097131390185746391889011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70796175186914328522518681 53097131390185746391889011)
        ·
          refine ⟨79645697085278619587833517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53097131390185746391889011 79645697085278619587833517)
          ·
            refine ⟨29867136406979482345437569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79645697085278619587833517 29867136406979482345437569)
            ·
              refine ⟨22400352305234611759078177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29867136406979482345437569 22400352305234611759078177)
              ·
                refine ⟨16800264228925958819308633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22400352305234611759078177 16800264228925958819308633)
                ·
                  refine ⟨12600198171694469114481475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16800264228925958819308633 12600198171694469114481475)
                  ·
                    refine ⟨18900297257541703671722213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12600198171694469114481475 18900297257541703671722213)
                    ·
                      refine ⟨3543805735789069438447915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18900297257541703671722213 3543805735789069438447915)
                      ·
                        rfl

theorem cell23_6901537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6901537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901537 prefixEnd_6901537 := by exact prefixLift 6901537
  have htrace : WordTrace (prefixWord ++ tailWord_6901537) baseStart_6901537 baseEnd_6901537 := by
    simpa [prefixWord, tailWord_6901537, baseEnd_6901537] using wordTrace_append hprefix tailTrace_6901537
  have hstable : (prefixWord ++ tailWord_6901537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901537).length < 2 ^ (prefixWord ++ tailWord_6901537).sum := by decide
  have hdescent : baseEnd_6901537 < baseStart_6901537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901554 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_6901554 : Nat := 118140960795 + 6901554 * 2 ^ 59
def prefixEnd_6901554 : Nat := 4983230072969 + 3 ^ 40 * 6901554 * 2
def baseEnd_6901554 : Nat := 3543814464960195871935337

theorem tailTrace_6901554 : CollatzResearch.WordTrace tailWord_6901554 prefixEnd_6901554 3543814464960195871935337 := by
  unfold tailWord_6901554
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930088509714006106969929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167813569359237349618586477 62930088509714006106969929)
  ·
    refine ⟨47197566382285504580227447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62930088509714006106969929 47197566382285504580227447)
    ·
      refine ⟨70796349573428256870341171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47197566382285504580227447 70796349573428256870341171)
      ·
        refine ⟨106194524360142385305511757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70796349573428256870341171 106194524360142385305511757)
        ·
          refine ⟨39822946635053394489566909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106194524360142385305511757 39822946635053394489566909)
          ·
            refine ⟨14933604988145022933587591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39822946635053394489566909 14933604988145022933587591)
            ·
              refine ⟨22400407482217534400381387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933604988145022933587591 22400407482217534400381387)
              ·
                refine ⟨33600611223326301600572081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22400407482217534400381387 33600611223326301600572081)
                ·
                  refine ⟨25200458417494726200429061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33600611223326301600572081 25200458417494726200429061)
                  ·
                    refine ⟨4725085953280261162580449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25200458417494726200429061 4725085953280261162580449)
                    ·
                      refine ⟨3543814464960195871935337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725085953280261162580449 3543814464960195871935337)
                      ·
                        rfl

theorem cell23_6901554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_6901554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901554 prefixEnd_6901554 := by exact prefixLift 6901554
  have htrace : WordTrace (prefixWord ++ tailWord_6901554) baseStart_6901554 baseEnd_6901554 := by
    simpa [prefixWord, tailWord_6901554, baseEnd_6901554] using wordTrace_append hprefix tailTrace_6901554
  have hstable : (prefixWord ++ tailWord_6901554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901554).length < 2 ^ (prefixWord ++ tailWord_6901554).sum := by decide
  have hdescent : baseEnd_6901554 < baseStart_6901554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901627 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 8, 2]
def baseStart_6901627 : Nat := 118140960795 + 6901627 * 2 ^ 59
def prefixEnd_6901627 : Nat := 4983230072969 + 3 ^ 40 * 6901627 * 2
def baseEnd_6901627 : Nat := 3543851949047974086322501

theorem tailTrace_6901627 : CollatzResearch.WordTrace tailWord_6901627 prefixEnd_6901627 3543851949047974086322501 := by
  unfold tailWord_6901627
  simp only [CollatzResearch.WordTrace]
  refine ⟨251723016567591557895287135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167815344378394371930191423 251723016567591557895287135)
  ·
    refine ⟨377584524851387336842930703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251723016567591557895287135 377584524851387336842930703)
    ·
      refine ⟨566376787277081005264396055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377584524851387336842930703 566376787277081005264396055)
      ·
        refine ⟨849565180915621507896594083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566376787277081005264396055 849565180915621507896594083)
        ·
          refine ⟨1274347771373432261844891125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849565180915621507896594083 1274347771373432261844891125)
          ·
            refine ⟨119470103566259274547958543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1274347771373432261844891125 119470103566259274547958543)
            ·
              refine ⟨179205155349388911821937815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119470103566259274547958543 179205155349388911821937815)
              ·
                refine ⟨268807733024083367732906723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179205155349388911821937815 268807733024083367732906723)
                ·
                  refine ⟨403211599536125051599360085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268807733024083367732906723 403211599536125051599360085)
                  ·
                    refine ⟨4725135932063965448430001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 403211599536125051599360085 4725135932063965448430001)
                    ·
                      refine ⟨3543851949047974086322501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725135932063965448430001 3543851949047974086322501)
                      ·
                        rfl

theorem cell23_6901627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8, 2].length) (baseStart_6901627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901627 prefixEnd_6901627 := by exact prefixLift 6901627
  have htrace : WordTrace (prefixWord ++ tailWord_6901627) baseStart_6901627 baseEnd_6901627 := by
    simpa [prefixWord, tailWord_6901627, baseEnd_6901627] using wordTrace_append hprefix tailTrace_6901627
  have hstable : (prefixWord ++ tailWord_6901627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901627).length < 2 ^ (prefixWord ++ tailWord_6901627).sum := by decide
  have hdescent : baseEnd_6901627 < baseStart_6901627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901637 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_6901637 : Nat := 118140960795 + 6901637 * 2 ^ 59
def prefixEnd_6901637 : Nat := 4983230072969 + 3 ^ 40 * 6901637 * 2
def baseEnd_6901637 : Nat := 1181285694618173015732485

theorem tailTrace_6901637 : CollatzResearch.WordTrace tailWord_6901637 prefixEnd_6901637 1181285694618173015732485 := by
  unfold tailWord_6901637
  simp only [CollatzResearch.WordTrace]
  refine ⟨251723381297555329603151165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167815587531703553068767443 251723381297555329603151165)
  ·
    refine ⟨94396267986583248601181687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251723381297555329603151165 94396267986583248601181687)
    ·
      refine ⟨141594401979874872901772531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94396267986583248601181687 141594401979874872901772531)
      ·
        refine ⟨212391602969812309352658797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141594401979874872901772531 212391602969812309352658797)
        ·
          refine ⟨79646851113679616007247049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212391602969812309352658797 79646851113679616007247049)
          ·
            refine ⟨59735138335259712005435287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79646851113679616007247049 59735138335259712005435287)
            ·
              refine ⟨89602707502889568008152931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59735138335259712005435287 89602707502889568008152931)
              ·
                refine ⟨134404061254334352012229397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89602707502889568008152931 134404061254334352012229397)
                ·
                  refine ⟨6300190371296922750573253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134404061254334352012229397 6300190371296922750573253)
                  ·
                    refine ⟨1181285694618173015732485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300190371296922750573253 1181285694618173015732485)
                    ·
                      rfl

theorem cell23_6901637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_6901637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901637 prefixEnd_6901637 := by exact prefixLift 6901637
  have htrace : WordTrace (prefixWord ++ tailWord_6901637) baseStart_6901637 baseEnd_6901637 := by
    simpa [prefixWord, tailWord_6901637, baseEnd_6901637] using wordTrace_append hprefix tailTrace_6901637
  have hstable : (prefixWord ++ tailWord_6901637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901637).length < 2 ^ (prefixWord ++ tailWord_6901637).sum := by decide
  have hdescent : baseEnd_6901637 < baseStart_6901637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901671 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6901671 : Nat := 118140960795 + 6901671 * 2 ^ 59
def prefixEnd_6901671 : Nat := 4983230072969 + 3 ^ 40 * 6901671 * 2
def baseEnd_6901671 : Nat := 1181291514065590638057433

theorem tailTrace_6901671 : CollatzResearch.WordTrace tailWord_6901671 prefixEnd_6901671 1181291514065590638057433 := by
  unfold tailWord_6901671
  simp only [CollatzResearch.WordTrace]
  refine ⟨251724621379432153409888867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167816414252954768939925911 251724621379432153409888867)
  ·
    refine ⟨377586932069148230114833301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251724621379432153409888867 377586932069148230114833301)
    ·
      refine ⟨17699387440741323286632811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 377586932069148230114833301 17699387440741323286632811)
      ·
        refine ⟨26549081161111984929949217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17699387440741323286632811 26549081161111984929949217)
        ·
          refine ⟨19911810870833988697461913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26549081161111984929949217 19911810870833988697461913)
          ·
            refine ⟨14933858153125491523096435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19911810870833988697461913 14933858153125491523096435)
            ·
              refine ⟨22400787229688237284644653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933858153125491523096435 22400787229688237284644653)
              ·
                refine ⟨8400295211133088981741745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22400787229688237284644653 8400295211133088981741745)
                ·
                  refine ⟨6300221408349816736306309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8400295211133088981741745 6300221408349816736306309)
                  ·
                    refine ⟨1181291514065590638057433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300221408349816736306309 1181291514065590638057433)
                    ·
                      rfl

theorem cell23_6901671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6901671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901671 prefixEnd_6901671 := by exact prefixLift 6901671
  have htrace : WordTrace (prefixWord ++ tailWord_6901671) baseStart_6901671 baseEnd_6901671 := by
    simpa [prefixWord, tailWord_6901671, baseEnd_6901671] using wordTrace_append hprefix tailTrace_6901671
  have hstable : (prefixWord ++ tailWord_6901671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901671).length < 2 ^ (prefixWord ++ tailWord_6901671).sum := by decide
  have hdescent : baseEnd_6901671 < baseStart_6901671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901681 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_6901681 : Nat := 118140960795 + 6901681 * 2 ^ 59
def prefixEnd_6901681 : Nat := 4983230072969 + 3 ^ 40 * 6901681 * 2
def baseEnd_6901681 : Nat := 3543879677003316875047253

theorem tailTrace_6901681 : CollatzResearch.WordTrace tailWord_6901681 prefixEnd_6901681 3543879677003316875047253 := by
  unfold tailWord_6901681
  simp only [CollatzResearch.WordTrace]
  refine ⟨251724986109395925117752897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167816657406263950078501931 251724986109395925117752897)
  ·
    refine ⟨188793739582046943838314673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251724986109395925117752897 188793739582046943838314673)
    ·
      refine ⟨141595304686535207878736005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188793739582046943838314673 141595304686535207878736005)
      ·
        refine ⟨26549119628725351477263001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141595304686535207878736005 26549119628725351477263001)
        ·
          refine ⟨19911839721544013607947251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26549119628725351477263001 19911839721544013607947251)
          ·
            refine ⟨29867759582316020411920877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19911839721544013607947251 29867759582316020411920877)
            ·
              refine ⟨11200409843368507654470329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29867759582316020411920877 11200409843368507654470329)
              ·
                refine ⟨8400307382526380740852747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200409843368507654470329 8400307382526380740852747)
                ·
                  refine ⟨12600461073789571111279121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8400307382526380740852747 12600461073789571111279121)
                  ·
                    refine ⟨9450345805342178333459341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12600461073789571111279121 9450345805342178333459341)
                    ·
                      refine ⟨3543879677003316875047253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450345805342178333459341 3543879677003316875047253)
                      ·
                        rfl

theorem cell23_6901681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_6901681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901681 prefixEnd_6901681 := by exact prefixLift 6901681
  have htrace : WordTrace (prefixWord ++ tailWord_6901681) baseStart_6901681 baseEnd_6901681 := by
    simpa [prefixWord, tailWord_6901681, baseEnd_6901681] using wordTrace_append hprefix tailTrace_6901681
  have hstable : (prefixWord ++ tailWord_6901681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901681).length < 2 ^ (prefixWord ++ tailWord_6901681).sum := by decide
  have hdescent : baseEnd_6901681 < baseStart_6901681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901694 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6901694 : Nat := 118140960795 + 6901694 * 2 ^ 59
def prefixEnd_6901694 : Nat := 4983230072969 + 3 ^ 40 * 6901694 * 2
def baseEnd_6901694 : Nat := 3543886352251825324184693

theorem tailTrace_6901694 : CollatzResearch.WordTrace tailWord_6901694 prefixEnd_6901694 3543886352251825324184693 := by
  unfold tailWord_6901694
  simp only [CollatzResearch.WordTrace]
  refine ⟨31465682532293603542247017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167816973505565885558650757 31465682532293603542247017)
  ·
    refine ⟨23599261899220202656685263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31465682532293603542247017 23599261899220202656685263)
    ·
      refine ⟨35398892848830303985027895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23599261899220202656685263 35398892848830303985027895)
      ·
        refine ⟨53098339273245455977541843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35398892848830303985027895 53098339273245455977541843)
        ·
          refine ⟨79647508909868183966312765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53098339273245455977541843 79647508909868183966312765)
          ·
            refine ⟨29867815841200568987367287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79647508909868183966312765 29867815841200568987367287)
            ·
              refine ⟨44801723761800853481050931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29867815841200568987367287 44801723761800853481050931)
              ·
                refine ⟨67202585642701280221576397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44801723761800853481050931 67202585642701280221576397)
                ·
                  refine ⟨25200969616012980083091149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67202585642701280221576397 25200969616012980083091149)
                  ·
                    refine ⟨9450363606004867531159181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25200969616012980083091149 9450363606004867531159181)
                    ·
                      refine ⟨3543886352251825324184693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450363606004867531159181 3543886352251825324184693)
                      ·
                        rfl

theorem cell23_6901694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6901694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901694 prefixEnd_6901694 := by exact prefixLift 6901694
  have htrace : WordTrace (prefixWord ++ tailWord_6901694) baseStart_6901694 baseEnd_6901694 := by
    simpa [prefixWord, tailWord_6901694, baseEnd_6901694] using wordTrace_append hprefix tailTrace_6901694
  have hstable : (prefixWord ++ tailWord_6901694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901694).length < 2 ^ (prefixWord ++ tailWord_6901694).sum := by decide
  have hdescent : baseEnd_6901694 < baseStart_6901694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901711 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 3]
def baseStart_6901711 : Nat := 118140960795 + 6901711 * 2 ^ 59
def prefixEnd_6901711 : Nat := 4983230072969 + 3 ^ 40 * 6901711 * 2
def baseEnd_6901711 : Nat := 3543895081422951757672115

theorem tailTrace_6901711 : CollatzResearch.WordTrace tailWord_6901711 prefixEnd_6901711 3543895081422951757672115 := by
  unfold tailWord_6901711
  simp only [CollatzResearch.WordTrace]
  refine ⟨251726080299287240241344987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167817386866191493494229991 251726080299287240241344987)
  ·
    refine ⟨377589120448930860362017481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251726080299287240241344987 377589120448930860362017481)
    ·
      refine ⟨283191840336698145271513111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377589120448930860362017481 283191840336698145271513111)
      ·
        refine ⟨424787760505047217907269667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283191840336698145271513111 424787760505047217907269667)
        ·
          refine ⟨637181640757570826860904501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424787760505047217907269667 637181640757570826860904501)
          ·
            refine ⟨59735778821022265018209797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 637181640757570826860904501 59735778821022265018209797)
            ·
              refine ⟨11200458528941674690914337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59735778821022265018209797 11200458528941674690914337)
              ·
                refine ⟨8400343896706256018185753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200458528941674690914337 8400343896706256018185753)
                ·
                  refine ⟨6300257922529692013639315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8400343896706256018185753 6300257922529692013639315)
                  ·
                    refine ⟨9450386883794538020458973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6300257922529692013639315 9450386883794538020458973)
                    ·
                      refine ⟨3543895081422951757672115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450386883794538020458973 3543895081422951757672115)
                      ·
                        rfl

theorem cell23_6901711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_6901711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901711 prefixEnd_6901711 := by exact prefixLift 6901711
  have htrace : WordTrace (prefixWord ++ tailWord_6901711) baseStart_6901711 baseEnd_6901711 := by
    simpa [prefixWord, tailWord_6901711, baseEnd_6901711] using wordTrace_append hprefix tailTrace_6901711
  have hstable : (prefixWord ++ tailWord_6901711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901711).length < 2 ^ (prefixWord ++ tailWord_6901711).sum := by decide
  have hdescent : baseEnd_6901711 < baseStart_6901711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
