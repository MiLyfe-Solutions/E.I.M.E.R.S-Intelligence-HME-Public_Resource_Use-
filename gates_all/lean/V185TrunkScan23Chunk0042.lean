import V185TrunkScan23Chunk0041

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_249269 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_249269 : Nat := 118140960795 + 249269 * 2 ^ 59
def prefixEnd_249269 : Nat := 4983230072969 + 3 ^ 40 * 249269 * 2
def baseEnd_249269 : Nat := 127994809265690467591139

theorem tailTrace_249269 : CollatzResearch.WordTrace tailWord_249269 prefixEnd_249269 127994809265690467591139 := by
  unfold tailWord_249269
  simp only [CollatzResearch.WordTrace]
  refine ⟨9091587333948459600998861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6061058222632306400665907 9091587333948459600998861)
  ·
    refine ⟨3409345250230672350374573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9091587333948459600998861 3409345250230672350374573)
    ·
      refine ⟨1278504468836502131390465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3409345250230672350374573 1278504468836502131390465)
      ·
        refine ⟨958878351627376598542849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1278504468836502131390465 958878351627376598542849)
        ·
          refine ⟨719158763720532448907137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958878351627376598542849 719158763720532448907137)
          ·
            refine ⟨539369072790399336680353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719158763720532448907137 539369072790399336680353)
            ·
              refine ⟨404526804592799502510265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539369072790399336680353 404526804592799502510265)
              ·
                refine ⟨303395103444599626882699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404526804592799502510265 303395103444599626882699)
                ·
                  refine ⟨455092655166899440324049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303395103444599626882699 455092655166899440324049)
                  ·
                    refine ⟨341319491375174580243037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 455092655166899440324049 341319491375174580243037)
                    ·
                      refine ⟨127994809265690467591139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 341319491375174580243037 127994809265690467591139)
                      ·
                        rfl

theorem cell23_249269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_249269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249269 prefixEnd_249269 := by exact prefixLift 249269
  have htrace : WordTrace (prefixWord ++ tailWord_249269) baseStart_249269 baseEnd_249269 := by
    simpa [prefixWord, tailWord_249269, baseEnd_249269] using wordTrace_append hprefix tailTrace_249269
  have hstable : (prefixWord ++ tailWord_249269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249269).length < 2 ^ (prefixWord ++ tailWord_249269).sum := by decide
  have hdescent : baseEnd_249269 < baseStart_249269 := by decide
  rcases family_descends (prefixWord ++ tailWord_249269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249300 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_249300 : Nat := 118140960795 + 249300 * 2 ^ 59
def prefixEnd_249300 : Nat := 4983230072969 + 3 ^ 40 * 249300 * 2
def baseEnd_249300 : Nat := 128010727165979846303497

theorem tailTrace_249300 : CollatzResearch.WordTrace tailWord_249300 prefixEnd_249300 128010727165979846303497 := by
  unfold tailWord_249300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546358998418075947688677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6061811997890767930251569 4546358998418075947688677)
  ·
    refine ⟨852442312203389240191627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4546358998418075947688677 852442312203389240191627)
    ·
      refine ⟨1278663468305083860287441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852442312203389240191627 1278663468305083860287441)
      ·
        refine ⟨958997601228812895215581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1278663468305083860287441 958997601228812895215581)
        ·
          refine ⟨359624100460804835705843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958997601228812895215581 359624100460804835705843)
          ·
            refine ⟨539436150691207253558765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359624100460804835705843 539436150691207253558765)
            ·
              refine ⟨202288556509202720084537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539436150691207253558765 202288556509202720084537)
              ·
                refine ⟨151716417381902040063403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202288556509202720084537 151716417381902040063403)
                ·
                  refine ⟨227574626072853060095105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151716417381902040063403 227574626072853060095105)
                  ·
                    refine ⟨170680969554639795071329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227574626072853060095105 170680969554639795071329)
                    ·
                      refine ⟨128010727165979846303497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170680969554639795071329 128010727165979846303497)
                      ·
                        rfl

theorem cell23_249300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_249300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249300 prefixEnd_249300 := by exact prefixLift 249300
  have htrace : WordTrace (prefixWord ++ tailWord_249300) baseStart_249300 baseEnd_249300 := by
    simpa [prefixWord, tailWord_249300, baseEnd_249300] using wordTrace_append hprefix tailTrace_249300
  have hstable : (prefixWord ++ tailWord_249300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249300).length < 2 ^ (prefixWord ++ tailWord_249300).sum := by decide
  have hdescent : baseEnd_249300 < baseStart_249300 := by decide
  rcases family_descends (prefixWord ++ tailWord_249300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249372 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_249372 : Nat := 118140960795 + 249372 * 2 ^ 59
def prefixEnd_249372 : Nat := 4983230072969 + 3 ^ 40 * 249372 * 2
def baseEnd_249372 : Nat := 128047697773103564603165

theorem tailTrace_249372 : CollatzResearch.WordTrace tailWord_249372 prefixEnd_249372 128047697773103564603165 := by
  unfold tailWord_249372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547672026287654095999185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6063562701716872127998913 4547672026287654095999185)
  ·
    refine ⟨3410754019715740571999389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4547672026287654095999185 3410754019715740571999389)
    ·
      refine ⟨1279032757393402714499771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3410754019715740571999389 1279032757393402714499771)
      ·
        refine ⟨1918549136090104071749657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279032757393402714499771 1918549136090104071749657)
        ·
          refine ⟨1438911852067578053812243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918549136090104071749657 1438911852067578053812243)
          ·
            refine ⟨2158367778101367080718365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438911852067578053812243 2158367778101367080718365)
            ·
              refine ⟨809387916788012655269387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2158367778101367080718365 809387916788012655269387)
              ·
                refine ⟨1214081875182018982904081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809387916788012655269387 1214081875182018982904081)
                ·
                  refine ⟨910561406386514237178061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1214081875182018982904081 910561406386514237178061)
                  ·
                    refine ⟨341460527394942838941773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 910561406386514237178061 341460527394942838941773)
                    ·
                      refine ⟨128047697773103564603165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 341460527394942838941773 128047697773103564603165)
                      ·
                        rfl

theorem cell23_249372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_249372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249372 prefixEnd_249372 := by exact prefixLift 249372
  have htrace : WordTrace (prefixWord ++ tailWord_249372) baseStart_249372 baseEnd_249372 := by
    simpa [prefixWord, tailWord_249372, baseEnd_249372] using wordTrace_append hprefix tailTrace_249372
  have hstable : (prefixWord ++ tailWord_249372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249372).length < 2 ^ (prefixWord ++ tailWord_249372).sum := by decide
  have hdescent : baseEnd_249372 < baseStart_249372 := by decide
  rcases family_descends (prefixWord ++ tailWord_249372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249375 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 4, 5]
def baseStart_249375 : Nat := 118140960795 + 249375 * 2 ^ 59
def prefixEnd_249375 : Nat := 4983230072969 + 3 ^ 40 * 249375 * 2
def baseEnd_249375 : Nat := 42683079405022350955217

theorem tailTrace_249375 : CollatzResearch.WordTrace tailWord_249375 prefixEnd_249375 42683079405022350955217 := by
  unfold tailWord_249375
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095453471564439704357579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6063635647709626469571719 9095453471564439704357579)
  ·
    refine ⟨13643180207346659556536369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9095453471564439704357579 13643180207346659556536369)
    ·
      refine ⟨10232385155509994667402277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13643180207346659556536369 10232385155509994667402277)
      ·
        refine ⟨1918572216658124000137927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10232385155509994667402277 1918572216658124000137927)
        ·
          refine ⟨2877858324987186000206891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918572216658124000137927 2877858324987186000206891)
          ·
            refine ⟨4316787487480779000310337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877858324987186000206891 4316787487480779000310337)
            ·
              refine ⟨3237590615610584250232753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4316787487480779000310337 3237590615610584250232753)
              ·
                refine ⟨2428192961707938187674565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237590615610584250232753 2428192961707938187674565)
                ·
                  refine ⟨455286180320238410188981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428192961707938187674565 455286180320238410188981)
                  ·
                    refine ⟨42683079405022350955217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 455286180320238410188981 42683079405022350955217)
                    ·
                      rfl

theorem cell23_249375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_249375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249375 prefixEnd_249375 := by exact prefixLift 249375
  have htrace : WordTrace (prefixWord ++ tailWord_249375) baseStart_249375 baseEnd_249375 := by
    simpa [prefixWord, tailWord_249375, baseEnd_249375] using wordTrace_append hprefix tailTrace_249375
  have hstable : (prefixWord ++ tailWord_249375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249375).length < 2 ^ (prefixWord ++ tailWord_249375).sum := by decide
  have hdescent : baseEnd_249375 < baseStart_249375 := by decide
  rcases family_descends (prefixWord ++ tailWord_249375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249425 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_249425 : Nat := 118140960795 + 249425 * 2 ^ 59
def prefixEnd_249425 : Nat := 4983230072969 + 3 ^ 40 * 249425 * 2
def baseEnd_249425 : Nat := 128074912247791857240421

theorem tailTrace_249425 : CollatzResearch.WordTrace tailWord_249425 prefixEnd_249425 128074912247791857240421 := by
  unfold tailWord_249425
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097277121383298243677729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6064851414255532162451819 9097277121383298243677729)
  ·
    refine ⟨6822957841037473682758297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9097277121383298243677729 6822957841037473682758297)
    ·
      refine ⟨5117218380778105262068723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6822957841037473682758297 5117218380778105262068723)
      ·
        refine ⟨7675827571167157893103085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5117218380778105262068723 7675827571167157893103085)
        ·
          refine ⟨2878435339187684209913657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7675827571167157893103085 2878435339187684209913657)
          ·
            refine ⟨2158826504390763157435243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878435339187684209913657 2158826504390763157435243)
            ·
              refine ⟨3238239756586144736152865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158826504390763157435243 3238239756586144736152865)
              ·
                refine ⟨2428679817439608552114649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238239756586144736152865 2428679817439608552114649)
                ·
                  refine ⟨1821509863079706414085987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428679817439608552114649 1821509863079706414085987)
                  ·
                    refine ⟨2732264794619559621128981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821509863079706414085987 2732264794619559621128981)
                    ·
                      refine ⟨128074912247791857240421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2732264794619559621128981 128074912247791857240421)
                      ·
                        rfl

theorem cell23_249425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_249425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249425 prefixEnd_249425 := by exact prefixLift 249425
  have htrace : WordTrace (prefixWord ++ tailWord_249425) baseStart_249425 baseEnd_249425 := by
    simpa [prefixWord, tailWord_249425, baseEnd_249425] using wordTrace_append hprefix tailTrace_249425
  have hstable : (prefixWord ++ tailWord_249425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249425).length < 2 ^ (prefixWord ++ tailWord_249425).sum := by decide
  have hdescent : baseEnd_249425 < baseStart_249425 := by decide
  rcases family_descends (prefixWord ++ tailWord_249425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249456 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 1, 4]
def baseStart_249456 : Nat := 118140960795 + 249456 * 2 ^ 59
def prefixEnd_249456 : Nat := 4983230072969 + 3 ^ 40 * 249456 * 2
def baseEnd_249456 : Nat := 42696943382693745317593

theorem tailTrace_249456 : CollatzResearch.WordTrace tailWord_249456 prefixEnd_249456 42696943382693745317593 := by
  unfold tailWord_249456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549203892135495269028111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6065605189513993692037481 4549203892135495269028111)
  ·
    refine ⟨6823805838203242903542167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4549203892135495269028111 6823805838203242903542167)
    ·
      refine ⟨10235708757304864355313251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823805838203242903542167 10235708757304864355313251)
      ·
        refine ⟨15353563135957296532969877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235708757304864355313251 15353563135957296532969877)
        ·
          refine ⟨719698271997998274982963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15353563135957296532969877 719698271997998274982963)
          ·
            refine ⟨1079547407996997412474445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719698271997998274982963 1079547407996997412474445)
            ·
              refine ⟨404830277998874029677917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079547407996997412474445 404830277998874029677917)
              ·
                refine ⟨151811354249577761129219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404830277998874029677917 151811354249577761129219)
                ·
                  refine ⟨227717031374366641693829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151811354249577761129219 227717031374366641693829)
                  ·
                    refine ⟨42696943382693745317593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227717031374366641693829 42696943382693745317593)
                    ·
                      rfl

theorem cell23_249456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 4].length) (baseStart_249456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249456 prefixEnd_249456 := by exact prefixLift 249456
  have htrace : WordTrace (prefixWord ++ tailWord_249456) baseStart_249456 baseEnd_249456 := by
    simpa [prefixWord, tailWord_249456, baseEnd_249456] using wordTrace_append hprefix tailTrace_249456
  have hstable : (prefixWord ++ tailWord_249456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249456).length < 2 ^ (prefixWord ++ tailWord_249456).sum := by decide
  have hdescent : baseEnd_249456 < baseStart_249456 := by decide
  rcases family_descends (prefixWord ++ tailWord_249456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249473 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 1, 4]
def baseStart_249473 : Nat := 118140960795 + 249473 * 2 ^ 59
def prefixEnd_249473 : Nat := 4983230072969 + 3 ^ 40 * 249473 * 2
def baseEnd_249473 : Nat := 42699853106402556480067

theorem tailTrace_249473 : CollatzResearch.WordTrace tailWord_249473 prefixEnd_249473 42699853106402556480067 := by
  unfold tailWord_249473
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099027825209402441425073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6066018550139601627616715 9099027825209402441425073)
  ·
    refine ⟨6824270868907051831068805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9099027825209402441425073 6824270868907051831068805)
    ·
      refine ⟨1279550787920072218325401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6824270868907051831068805 1279550787920072218325401)
      ·
        refine ⟨959663090940054163744051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279550787920072218325401 959663090940054163744051)
        ·
          refine ⟨1439494636410081245616077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959663090940054163744051 1439494636410081245616077)
          ·
            refine ⟨539810488653780467106029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1439494636410081245616077 539810488653780467106029)
            ·
              refine ⟨202428933245167675164761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539810488653780467106029 202428933245167675164761)
              ·
                refine ⟨151821699933875756373571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202428933245167675164761 151821699933875756373571)
                ·
                  refine ⟨227732549900813634560357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151821699933875756373571 227732549900813634560357)
                  ·
                    refine ⟨42699853106402556480067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227732549900813634560357 42699853106402556480067)
                    ·
                      rfl

theorem cell23_249473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_249473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249473 prefixEnd_249473 := by exact prefixLift 249473
  have htrace : WordTrace (prefixWord ++ tailWord_249473) baseStart_249473 baseEnd_249473 := by
    simpa [prefixWord, tailWord_249473, baseEnd_249473] using wordTrace_append hprefix tailTrace_249473
  have hstable : (prefixWord ++ tailWord_249473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249473).length < 2 ^ (prefixWord ++ tailWord_249473).sum := by decide
  have hdescent : baseEnd_249473 < baseStart_249473 := by decide
  rcases family_descends (prefixWord ++ tailWord_249473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249475 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_249475 : Nat := 118140960795 + 249475 * 2 ^ 59
def prefixEnd_249475 : Nat := 4983230072969 + 3 ^ 40 * 249475 * 2
def baseEnd_249475 : Nat := 128100586280516661615191

theorem tailTrace_249475 : CollatzResearch.WordTrace tailWord_249475 prefixEnd_249475 128100586280516661615191 := by
  unfold tailWord_249475
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099100771202156782997879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6066067180801437855331919 9099100771202156782997879)
  ·
    refine ⟨13648651156803235174496819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099100771202156782997879 13648651156803235174496819)
    ·
      refine ⟨20472976735204852761745229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648651156803235174496819 20472976735204852761745229)
      ·
        refine ⟨7677366275701819785654461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20472976735204852761745229 7677366275701819785654461)
        ·
          refine ⟨2879012353388182419620423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7677366275701819785654461 2879012353388182419620423)
          ·
            refine ⟨4318518530082273629430635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879012353388182419620423 4318518530082273629430635)
            ·
              refine ⟨6477777795123410444145953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318518530082273629430635 6477777795123410444145953)
              ·
                refine ⟨4858333346342557833109465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6477777795123410444145953 4858333346342557833109465)
                ·
                  refine ⟨3643750009756918374832099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4858333346342557833109465 3643750009756918374832099)
                  ·
                    refine ⟨5465625014635377562248149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643750009756918374832099 5465625014635377562248149)
                    ·
                      refine ⟨128100586280516661615191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5465625014635377562248149 128100586280516661615191)
                      ·
                        rfl

theorem cell23_249475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_249475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249475 prefixEnd_249475 := by exact prefixLift 249475
  have htrace : WordTrace (prefixWord ++ tailWord_249475) baseStart_249475 baseEnd_249475 := by
    simpa [prefixWord, tailWord_249475, baseEnd_249475] using wordTrace_append hprefix tailTrace_249475
  have hstable : (prefixWord ++ tailWord_249475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249475).length < 2 ^ (prefixWord ++ tailWord_249475).sum := by decide
  have hdescent : baseEnd_249475 < baseStart_249475 := by decide
  rcases family_descends (prefixWord ++ tailWord_249475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249486 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_249486 : Nat := 118140960795 + 249486 * 2 ^ 59
def prefixEnd_249486 : Nat := 4983230072969 + 3 ^ 40 * 249486 * 2
def baseEnd_249486 : Nat := 14234026063079568730849

theorem tailTrace_249486 : CollatzResearch.WordTrace tailWord_249486 prefixEnd_249486 14234026063079568730849 := by
  unfold tailWord_249486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137437746770288207706039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6066334649441537107765541 1137437746770288207706039)
  ·
    refine ⟨1706156620155432311559059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1137437746770288207706039 1706156620155432311559059)
    ·
      refine ⟨2559234930233148467338589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706156620155432311559059 2559234930233148467338589)
      ·
        refine ⟨959713098837430675251971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2559234930233148467338589 959713098837430675251971)
        ·
          refine ⟨1439569648256146012877957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959713098837430675251971 1439569648256146012877957)
          ·
            refine ⟨269919309048027377414617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1439569648256146012877957 269919309048027377414617)
            ·
              refine ⟨202439481786020533060963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269919309048027377414617 202439481786020533060963)
              ·
                refine ⟨303659222679030799591445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202439481786020533060963 303659222679030799591445)
                ·
                  refine ⟨14234026063079568730849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303659222679030799591445 14234026063079568730849)
                  ·
                    rfl

theorem cell23_249486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_249486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249486 prefixEnd_249486 := by exact prefixLift 249486
  have htrace : WordTrace (prefixWord ++ tailWord_249486) baseStart_249486 baseEnd_249486 := by
    simpa [prefixWord, tailWord_249486, baseEnd_249486] using wordTrace_append hprefix tailTrace_249486
  have hstable : (prefixWord ++ tailWord_249486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249486).length < 2 ^ (prefixWord ++ tailWord_249486).sum := by decide
  have hdescent : baseEnd_249486 < baseStart_249486 := by decide
  rcases family_descends (prefixWord ++ tailWord_249486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249515 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_249515 : Nat := 118140960795 + 249515 * 2 ^ 59
def prefixEnd_249515 : Nat := 4983230072969 + 3 ^ 40 * 249515 * 2
def baseEnd_249515 : Nat := 128121125506696505115007

theorem tailTrace_249515 : CollatzResearch.WordTrace tailWord_249515 prefixEnd_249515 128121125506696505115007 := by
  unfold tailWord_249515
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100559691057243614453999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6067039794038162409635999 9100559691057243614453999)
  ·
    refine ⟨13650839536585865421680999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100559691057243614453999 13650839536585865421680999)
    ·
      refine ⟨20476259304878798132521499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13650839536585865421680999 20476259304878798132521499)
      ·
        refine ⟨30714388957318197198782249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20476259304878798132521499 30714388957318197198782249)
        ·
          refine ⟨23035791717988647899086687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30714388957318197198782249 23035791717988647899086687)
          ·
            refine ⟨34553687576982971848630031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23035791717988647899086687 34553687576982971848630031)
            ·
              refine ⟨51830531365474457772945047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34553687576982971848630031 51830531365474457772945047)
              ·
                refine ⟨77745797048211686659417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51830531365474457772945047 77745797048211686659417571)
                ·
                  refine ⟨116618695572317529989126357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77745797048211686659417571 116618695572317529989126357)
                  ·
                    refine ⟨2733250677476192109120149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116618695572317529989126357 2733250677476192109120149)
                    ·
                      refine ⟨128121125506696505115007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2733250677476192109120149 128121125506696505115007)
                      ·
                        rfl

theorem cell23_249515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_249515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249515 prefixEnd_249515 := by exact prefixLift 249515
  have htrace : WordTrace (prefixWord ++ tailWord_249515) baseStart_249515 baseEnd_249515 := by
    simpa [prefixWord, tailWord_249515, baseEnd_249515] using wordTrace_append hprefix tailTrace_249515
  have hstable : (prefixWord ++ tailWord_249515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249515).length < 2 ^ (prefixWord ++ tailWord_249515).sum := by decide
  have hdescent : baseEnd_249515 < baseStart_249515 := by decide
  rcases family_descends (prefixWord ++ tailWord_249515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249529 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_249529 : Nat := 118140960795 + 249529 * 2 ^ 59
def prefixEnd_249529 : Nat := 4983230072969 + 3 ^ 40 * 249529 * 2
def baseEnd_249529 : Nat := 42709438078619816779981

theorem tailTrace_249529 : CollatzResearch.WordTrace tailWord_249529 prefixEnd_249529 42709438078619816779981 := by
  unfold tailWord_249529
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101070313006524005463641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6067380208671016003642427 9101070313006524005463641)
  ·
    refine ⟨6825802734754893004097731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9101070313006524005463641 6825802734754893004097731)
    ·
      refine ⟨10238704102132339506146597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825802734754893004097731 10238704102132339506146597)
      ·
        refine ⟨1919757019149813657402487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10238704102132339506146597 1919757019149813657402487)
        ·
          refine ⟨2879635528724720486103731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919757019149813657402487 2879635528724720486103731)
          ·
            refine ⟨4319453293087080729155597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879635528724720486103731 4319453293087080729155597)
            ·
              refine ⟨1619794984907655273433349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4319453293087080729155597 1619794984907655273433349)
              ·
                refine ⟨303711559670185363768753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1619794984907655273433349 303711559670185363768753)
                ·
                  refine ⟨227783669752639022826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303711559670185363768753 227783669752639022826565)
                  ·
                    refine ⟨42709438078619816779981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227783669752639022826565 42709438078619816779981)
                    ·
                      rfl

theorem cell23_249529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_249529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249529 prefixEnd_249529 := by exact prefixLift 249529
  have htrace : WordTrace (prefixWord ++ tailWord_249529) baseStart_249529 baseEnd_249529 := by
    simpa [prefixWord, tailWord_249529, baseEnd_249529] using wordTrace_append hprefix tailTrace_249529
  have hstable : (prefixWord ++ tailWord_249529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249529).length < 2 ^ (prefixWord ++ tailWord_249529).sum := by decide
  have hdescent : baseEnd_249529 < baseStart_249529 := by decide
  rcases family_descends (prefixWord ++ tailWord_249529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249530 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3]
def baseStart_249530 : Nat := 118140960795 + 249530 * 2 ^ 59
def prefixEnd_249530 : Nat := 4983230072969 + 3 ^ 40 * 249530 * 2
def baseEnd_249530 : Nat := 128128827716513946427439

theorem tailTrace_249530 : CollatzResearch.WordTrace tailWord_249530 prefixEnd_249530 128128827716513946427439 := by
  unfold tailWord_249530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275276696500725294062511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6067404524001934117500029 2275276696500725294062511)
  ·
    refine ⟨3412915044751087941093767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2275276696500725294062511 3412915044751087941093767)
    ·
      refine ⟨5119372567126631911640651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412915044751087941093767 5119372567126631911640651)
      ·
        refine ⟨7679058850689947867460977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5119372567126631911640651 7679058850689947867460977)
        ·
          refine ⟨5759294138017460900595733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7679058850689947867460977 5759294138017460900595733)
          ·
            refine ⟨269966912719568479715425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5759294138017460900595733 269966912719568479715425)
            ·
              refine ⟨202475184539676359786569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269966912719568479715425 202475184539676359786569)
              ·
                refine ⟨151856388404757269839927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202475184539676359786569 151856388404757269839927)
                ·
                  refine ⟨227784582607135904759891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151856388404757269839927 227784582607135904759891)
                  ·
                    refine ⟨341676873910703857139837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227784582607135904759891 341676873910703857139837)
                    ·
                      refine ⟨128128827716513946427439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 341676873910703857139837 128128827716513946427439)
                      ·
                        rfl

theorem cell23_249530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_249530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249530 prefixEnd_249530 := by exact prefixLift 249530
  have htrace : WordTrace (prefixWord ++ tailWord_249530) baseStart_249530 baseEnd_249530 := by
    simpa [prefixWord, tailWord_249530, baseEnd_249530] using wordTrace_append hprefix tailTrace_249530
  have hstable : (prefixWord ++ tailWord_249530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249530).length < 2 ^ (prefixWord ++ tailWord_249530).sum := by decide
  have hdescent : baseEnd_249530 < baseStart_249530 := by decide
  rcases family_descends (prefixWord ++ tailWord_249530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249536 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2]
def baseStart_249536 : Nat := 118140960795 + 249536 * 2 ^ 59
def prefixEnd_249536 : Nat := 4983230072969 + 3 ^ 40 * 249536 * 2
def baseEnd_249536 : Nat := 128131908600440922952411

theorem tailTrace_249536 : CollatzResearch.WordTrace tailWord_249536 prefixEnd_249536 128131908600440922952411 := by
  unfold tailWord_249536
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550662811990582100484231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6067550415987442800645641 4550662811990582100484231)
  ·
    refine ⟨6825994217985873150726347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4550662811990582100484231 6825994217985873150726347)
    ·
      refine ⟨10238991326978809726089521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825994217985873150726347 10238991326978809726089521)
      ·
        refine ⟨7679243495234107294567141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10238991326978809726089521 7679243495234107294567141)
        ·
          refine ⟨1439858155356395117731339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7679243495234107294567141 1439858155356395117731339)
          ·
            refine ⟨2159787233034592676597009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439858155356395117731339 2159787233034592676597009)
            ·
              refine ⟨1619840424775944507447757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2159787233034592676597009 1619840424775944507447757)
              ·
                refine ⟨607440159290979190292909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1619840424775944507447757 607440159290979190292909)
                ·
                  refine ⟨227790059734117196359841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607440159290979190292909 227790059734117196359841)
                  ·
                    refine ⟨170842544800587897269881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227790059734117196359841 170842544800587897269881)
                    ·
                      refine ⟨128131908600440922952411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170842544800587897269881 128131908600440922952411)
                      ·
                        rfl

theorem cell23_249536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_249536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249536 prefixEnd_249536 := by exact prefixLift 249536
  have htrace : WordTrace (prefixWord ++ tailWord_249536) baseStart_249536 baseEnd_249536 := by
    simpa [prefixWord, tailWord_249536, baseEnd_249536] using wordTrace_append hprefix tailTrace_249536
  have hstable : (prefixWord ++ tailWord_249536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249536).length < 2 ^ (prefixWord ++ tailWord_249536).sum := by decide
  have hdescent : baseEnd_249536 < baseStart_249536 := by decide
  rcases family_descends (prefixWord ++ tailWord_249536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249556 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_249556 : Nat := 118140960795 + 249556 * 2 ^ 59
def prefixEnd_249556 : Nat := 4983230072969 + 3 ^ 40 * 249556 * 2
def baseEnd_249556 : Nat := 128142178213530844702319

theorem tailTrace_249556 : CollatzResearch.WordTrace tailWord_249556 prefixEnd_249556 128142178213530844702319 := by
  unfold tailWord_249556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551027541954353808348261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6068036722605805077797681 4551027541954353808348261)
  ·
    refine ⟨853317664116441339065299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4551027541954353808348261 853317664116441339065299)
    ·
      refine ⟨1279976496174662008597949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853317664116441339065299 1279976496174662008597949)
      ·
        refine ⟨479991186065498253224231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1279976496174662008597949 479991186065498253224231)
        ·
          refine ⟨719986779098247379836347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479991186065498253224231 719986779098247379836347)
          ·
            refine ⟨1079980168647371069754521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719986779098247379836347 1079980168647371069754521)
            ·
              refine ⟨809985126485528302315891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079980168647371069754521 809985126485528302315891)
              ·
                refine ⟨1214977689728292453473837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809985126485528302315891 1214977689728292453473837)
                ·
                  refine ⟨455616633648109670052689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214977689728292453473837 455616633648109670052689)
                  ·
                    refine ⟨341712475236082252539517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 455616633648109670052689 341712475236082252539517)
                    ·
                      refine ⟨128142178213530844702319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 341712475236082252539517 128142178213530844702319)
                      ·
                        rfl

theorem cell23_249556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_249556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249556 prefixEnd_249556 := by exact prefixLift 249556
  have htrace : WordTrace (prefixWord ++ tailWord_249556) baseStart_249556 baseEnd_249556 := by
    simpa [prefixWord, tailWord_249556, baseEnd_249556] using wordTrace_append hprefix tailTrace_249556
  have hstable : (prefixWord ++ tailWord_249556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249556).length < 2 ^ (prefixWord ++ tailWord_249556).sum := by decide
  have hdescent : baseEnd_249556 < baseStart_249556 := by decide
  rcases family_descends (prefixWord ++ tailWord_249556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249586 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_249586 : Nat := 118140960795 + 249586 * 2 ^ 59
def prefixEnd_249586 : Nat := 4983230072969 + 3 ^ 40 * 249586 * 2
def baseEnd_249586 : Nat := 128157582633165727327181

theorem tailTrace_249586 : CollatzResearch.WordTrace tailWord_249586 prefixEnd_249586 128157582633165727327181 := by
  unfold tailWord_249586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275787318450005685072153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6068766182533348493525741 2275787318450005685072153)
  ·
    refine ⟨1706840488837504263804115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2275787318450005685072153 1706840488837504263804115)
    ·
      refine ⟨2560260733256256395706173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706840488837504263804115 2560260733256256395706173)
      ·
        refine ⟨960097774971096148389815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2560260733256256395706173 960097774971096148389815)
        ·
          refine ⟨1440146662456644222584723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960097774971096148389815 1440146662456644222584723)
          ·
            refine ⟨2160219993684966333877085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440146662456644222584723 2160219993684966333877085)
            ·
              refine ⟨810082497631862375203907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2160219993684966333877085 810082497631862375203907)
              ·
                refine ⟨1215123746447793562805861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810082497631862375203907 1215123746447793562805861)
                ·
                  refine ⟨227835702458961293026099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215123746447793562805861 227835702458961293026099)
                  ·
                    refine ⟨341753553688441939539149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227835702458961293026099 341753553688441939539149)
                    ·
                      refine ⟨128157582633165727327181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 341753553688441939539149 128157582633165727327181)
                      ·
                        rfl

theorem cell23_249586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_249586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249586 prefixEnd_249586 := by exact prefixLift 249586
  have htrace : WordTrace (prefixWord ++ tailWord_249586) baseStart_249586 baseEnd_249586 := by
    simpa [prefixWord, tailWord_249586, baseEnd_249586] using wordTrace_append hprefix tailTrace_249586
  have hstable : (prefixWord ++ tailWord_249586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249586).length < 2 ^ (prefixWord ++ tailWord_249586).sum := by decide
  have hdescent : baseEnd_249586 < baseStart_249586 := by decide
  rcases family_descends (prefixWord ++ tailWord_249586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249592 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_249592 : Nat := 118140960795 + 249592 * 2 ^ 59
def prefixEnd_249592 : Nat := 4983230072969 + 3 ^ 40 * 249592 * 2
def baseEnd_249592 : Nat := 128160663517092703852153

theorem tailTrace_249592 : CollatzResearch.WordTrace tailWord_249592 prefixEnd_249592 128160663517092703852153 := by
  unfold tailWord_249592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551684055889142882503515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6068912074518857176671353 4551684055889142882503515)
  ·
    refine ⟨6827526083833714323755273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551684055889142882503515 6827526083833714323755273)
    ·
      refine ⟨5120644562875285742816455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6827526083833714323755273 5120644562875285742816455)
      ·
        refine ⟨7680966844312928614224683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120644562875285742816455 7680966844312928614224683)
        ·
          refine ⟨11521450266469392921337025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680966844312928614224683 11521450266469392921337025)
          ·
            refine ⟨8641087699852044691002769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11521450266469392921337025 8641087699852044691002769)
            ·
              refine ⟨6480815774889033518252077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8641087699852044691002769 6480815774889033518252077)
              ·
                refine ⟨2430305915583387569344529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480815774889033518252077 2430305915583387569344529)
                ·
                  refine ⟨1822729436687540677008397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2430305915583387569344529 1822729436687540677008397)
                  ·
                    refine ⟨683523538757827753878149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822729436687540677008397 683523538757827753878149)
                    ·
                      refine ⟨128160663517092703852153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 683523538757827753878149 128160663517092703852153)
                      ·
                        rfl

theorem cell23_249592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_249592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249592 prefixEnd_249592 := by exact prefixLift 249592
  have htrace : WordTrace (prefixWord ++ tailWord_249592) baseStart_249592 baseEnd_249592 := by
    simpa [prefixWord, tailWord_249592, baseEnd_249592] using wordTrace_append hprefix tailTrace_249592
  have hstable : (prefixWord ++ tailWord_249592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249592).length < 2 ^ (prefixWord ++ tailWord_249592).sum := by decide
  have hdescent : baseEnd_249592 < baseStart_249592 := by decide
  rcases family_descends (prefixWord ++ tailWord_249592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249649 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 7]
def baseStart_249649 : Nat := 118140960795 + 249649 * 2 ^ 59
def prefixEnd_249649 : Nat := 4983230072969 + 3 ^ 40 * 249649 * 2
def baseEnd_249649 : Nat := 14243325768266553426599

theorem tailTrace_249649 : CollatzResearch.WordTrace tailWord_249649 prefixEnd_249649 14243325768266553426599 := by
  unfold tailWord_249649
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105447072571784499832001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6070298048381189666554667 9105447072571784499832001)
  ·
    refine ⟨6829085304428838374874001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9105447072571784499832001 6829085304428838374874001)
    ·
      refine ⟨5121813978321628781155501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6829085304428838374874001 5121813978321628781155501)
      ·
        refine ⟨1920680241870610792933313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5121813978321628781155501 1920680241870610792933313)
        ·
          refine ⟨1440510181402958094699985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1920680241870610792933313 1440510181402958094699985)
          ·
            refine ⟨1080382636052218571024989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440510181402958094699985 1080382636052218571024989)
            ·
              refine ⟨405143488519581964134371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1080382636052218571024989 405143488519581964134371)
              ·
                refine ⟨607715232779372946201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405143488519581964134371 607715232779372946201557)
                ·
                  refine ⟨14243325768266553426599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 607715232779372946201557 14243325768266553426599)
                  ·
                    rfl

theorem cell23_249649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_249649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249649 prefixEnd_249649 := by exact prefixLift 249649
  have htrace : WordTrace (prefixWord ++ tailWord_249649) baseStart_249649 baseEnd_249649 := by
    simpa [prefixWord, tailWord_249649, baseEnd_249649] using wordTrace_append hprefix tailTrace_249649
  have hstable : (prefixWord ++ tailWord_249649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249649).length < 2 ^ (prefixWord ++ tailWord_249649).sum := by decide
  have hdescent : baseEnd_249649 < baseStart_249649 := by decide
  rcases family_descends (prefixWord ++ tailWord_249649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249660 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_249660 : Nat := 118140960795 + 249660 * 2 ^ 59
def prefixEnd_249660 : Nat := 4983230072969 + 3 ^ 40 * 249660 * 2
def baseEnd_249660 : Nat := 128195580201598437801841

theorem tailTrace_249660 : CollatzResearch.WordTrace tailWord_249660 prefixEnd_249660 128195580201598437801841 := by
  unfold tailWord_249660
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552924137765966689241217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6070565517021288918988289 4552924137765966689241217)
  ·
    refine ⟨3414693103324475016930913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4552924137765966689241217 3414693103324475016930913)
    ·
      refine ⟨2561019827493356262698185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3414693103324475016930913 2561019827493356262698185)
      ·
        refine ⟨1920764870620017197023639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561019827493356262698185 1920764870620017197023639)
        ·
          refine ⟨2881147305930025795535459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920764870620017197023639 2881147305930025795535459)
          ·
            refine ⟨4321720958895038693303189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881147305930025795535459 4321720958895038693303189)
            ·
              refine ⟨202580669948204938748587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4321720958895038693303189 202580669948204938748587)
              ·
                refine ⟨303871004922307408122881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202580669948204938748587 303871004922307408122881)
                ·
                  refine ⟨227903253691730556092161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303871004922307408122881 227903253691730556092161)
                  ·
                    refine ⟨170927440268797917069121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227903253691730556092161 170927440268797917069121)
                    ·
                      refine ⟨128195580201598437801841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170927440268797917069121 128195580201598437801841)
                      ·
                        rfl

theorem cell23_249660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_249660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249660 prefixEnd_249660 := by exact prefixLift 249660
  have htrace : WordTrace (prefixWord ++ tailWord_249660) baseStart_249660 baseEnd_249660 := by
    simpa [prefixWord, tailWord_249660, baseEnd_249660] using wordTrace_append hprefix tailTrace_249660
  have hstable : (prefixWord ++ tailWord_249660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249660).length < 2 ^ (prefixWord ++ tailWord_249660).sum := by decide
  have hdescent : baseEnd_249660 < baseStart_249660 := by decide
  rcases family_descends (prefixWord ++ tailWord_249660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249700 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 5]
def baseStart_249700 : Nat := 118140960795 + 249700 * 2 ^ 59
def prefixEnd_249700 : Nat := 4983230072969 + 3 ^ 40 * 249700 * 2
def baseEnd_249700 : Nat := 14246235491975364589073

theorem tailTrace_249700 : CollatzResearch.WordTrace tailWord_249700 prefixEnd_249700 14246235491975364589073 := by
  unfold tailWord_249700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553653597693510104969277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6071538130258013473292369 4553653597693510104969277)
  ·
    refine ⟨1707620099135066289363479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4553653597693510104969277 1707620099135066289363479)
    ·
      refine ⟨2561430148702599434045219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707620099135066289363479 2561430148702599434045219)
      ·
        refine ⟨3842145223053899151067829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561430148702599434045219 3842145223053899151067829)
        ·
          refine ⟨360201114661303045412609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3842145223053899151067829 360201114661303045412609)
          ·
            refine ⟨270150835995977284059457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360201114661303045412609 270150835995977284059457)
            ·
              refine ⟨202613126996982963044593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270150835995977284059457 202613126996982963044593)
              ·
                refine ⟨151959845247737222283445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202613126996982963044593 151959845247737222283445)
                ·
                  refine ⟨14246235491975364589073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151959845247737222283445 14246235491975364589073)
                  ·
                    rfl

theorem cell23_249700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_249700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249700 prefixEnd_249700 := by exact prefixLift 249700
  have htrace : WordTrace (prefixWord ++ tailWord_249700) baseStart_249700 baseEnd_249700 := by
    simpa [prefixWord, tailWord_249700, baseEnd_249700] using wordTrace_append hprefix tailTrace_249700
  have hstable : (prefixWord ++ tailWord_249700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249700).length < 2 ^ (prefixWord ++ tailWord_249700).sum := by decide
  have hdescent : baseEnd_249700 < baseStart_249700 := by decide
  rcases family_descends (prefixWord ++ tailWord_249700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249746 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_249746 : Nat := 118140960795 + 249746 * 2 ^ 59
def prefixEnd_249746 : Nat := 4983230072969 + 3 ^ 40 * 249746 * 2
def baseEnd_249746 : Nat := 128239739537885101326445

theorem tailTrace_249746 : CollatzResearch.WordTrace tailWord_249746 prefixEnd_249746 128239739537885101326445 := by
  unfold tailWord_249746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277246238305092516528273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6072656635480246710742061 2277246238305092516528273)
  ·
    refine ⟨1707934678728819387396205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2277246238305092516528273 1707934678728819387396205)
    ·
      refine ⟨640475504523307270273577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1707934678728819387396205 640475504523307270273577)
      ·
        refine ⟨480356628392480452705183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640475504523307270273577 480356628392480452705183)
        ·
          refine ⟨720534942588720679057775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480356628392480452705183 720534942588720679057775)
          ·
            refine ⟨1080802413883081018586663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720534942588720679057775 1080802413883081018586663)
            ·
              refine ⟨1621203620824621527879995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080802413883081018586663 1621203620824621527879995)
              ·
                refine ⟨2431805431236932291819993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621203620824621527879995 2431805431236932291819993)
                ·
                  refine ⟨1823854073427699218864995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2431805431236932291819993 1823854073427699218864995)
                  ·
                    refine ⟨2735781110141548828297493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1823854073427699218864995 2735781110141548828297493)
                    ·
                      refine ⟨128239739537885101326445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2735781110141548828297493 128239739537885101326445)
                      ·
                        rfl

theorem cell23_249746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_249746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249746 prefixEnd_249746 := by exact prefixLift 249746
  have htrace : WordTrace (prefixWord ++ tailWord_249746) baseStart_249746 baseEnd_249746 := by
    simpa [prefixWord, tailWord_249746, baseEnd_249746] using wordTrace_append hprefix tailTrace_249746
  have hstable : (prefixWord ++ tailWord_249746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249746).length < 2 ^ (prefixWord ++ tailWord_249746).sum := by decide
  have hdescent : baseEnd_249746 < baseStart_249746 := by decide
  rcases family_descends (prefixWord ++ tailWord_249746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249756 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 8]
def baseStart_249756 : Nat := 118140960795 + 249756 * 2 ^ 59
def prefixEnd_249756 : Nat := 4983230072969 + 3 ^ 40 * 249756 * 2
def baseEnd_249756 : Nat := 14249430482714451355711

theorem tailTrace_249756 : CollatzResearch.WordTrace tailWord_249756 prefixEnd_249756 14249430482714451355711 := by
  unfold tailWord_249756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554674841592070886988561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6072899788789427849318081 4554674841592070886988561)
  ·
    refine ⟨3416006131194053165241421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4554674841592070886988561 3416006131194053165241421)
    ·
      refine ⟨1281002299197769936965533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3416006131194053165241421 1281002299197769936965533)
      ·
        refine ⟨480375862199163726362075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1281002299197769936965533 480375862199163726362075)
        ·
          refine ⟨720563793298745589543113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480375862199163726362075 720563793298745589543113)
          ·
            refine ⟨540422844974059192157335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720563793298745589543113 540422844974059192157335)
            ·
              refine ⟨810634267461088788236003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540422844974059192157335 810634267461088788236003)
              ·
                refine ⟨1215951401191633182354005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810634267461088788236003 1215951401191633182354005)
                ·
                  refine ⟨14249430482714451355711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1215951401191633182354005 14249430482714451355711)
                  ·
                    rfl

theorem cell23_249756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_249756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249756 prefixEnd_249756 := by exact prefixLift 249756
  have htrace : WordTrace (prefixWord ++ tailWord_249756) baseStart_249756 baseEnd_249756 := by
    simpa [prefixWord, tailWord_249756, baseEnd_249756] using wordTrace_append hprefix tailTrace_249756
  have hstable : (prefixWord ++ tailWord_249756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249756).length < 2 ^ (prefixWord ++ tailWord_249756).sum := by decide
  have hdescent : baseEnd_249756 < baseStart_249756 := by decide
  rcases family_descends (prefixWord ++ tailWord_249756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249769 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_249769 : Nat := 118140960795 + 249769 * 2 ^ 59
def prefixEnd_249769 : Nat := 4983230072969 + 3 ^ 40 * 249769 * 2
def baseEnd_249769 : Nat := 42750516530979503779613

theorem tailTrace_249769 : CollatzResearch.WordTrace tailWord_249769 prefixEnd_249769 42750516530979503779613 := by
  unfold tailWord_249769
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109823832137044994200361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6073215888091363329466907 9109823832137044994200361)
  ·
    refine ⟨6832367874102783745650271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9109823832137044994200361 6832367874102783745650271)
    ·
      refine ⟨10248551811154175618475407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6832367874102783745650271 10248551811154175618475407)
      ·
        refine ⟨15372827716731263427713111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10248551811154175618475407 15372827716731263427713111)
        ·
          refine ⟨23059241575096895141569667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15372827716731263427713111 23059241575096895141569667)
          ·
            refine ⟨34588862362645342712354501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23059241575096895141569667 34588862362645342712354501)
            ·
              refine ⟨6485411692996001758566469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34588862362645342712354501 6485411692996001758566469)
              ·
                refine ⟨1216014692436750329731213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6485411692996001758566469 1216014692436750329731213)
                ·
                  refine ⟨456005509663781373649205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216014692436750329731213 456005509663781373649205)
                  ·
                    refine ⟨42750516530979503779613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 456005509663781373649205 42750516530979503779613)
                    ·
                      rfl

theorem cell23_249769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_249769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249769 prefixEnd_249769 := by exact prefixLift 249769
  have htrace : WordTrace (prefixWord ++ tailWord_249769) baseStart_249769 baseEnd_249769 := by
    simpa [prefixWord, tailWord_249769, baseEnd_249769] using wordTrace_append hprefix tailTrace_249769
  have hstable : (prefixWord ++ tailWord_249769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249769).length < 2 ^ (prefixWord ++ tailWord_249769).sum := by decide
  have hdescent : baseEnd_249769 < baseStart_249769 := by decide
  rcases family_descends (prefixWord ++ tailWord_249769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249799 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 3, 6]
def baseStart_249799 : Nat := 118140960795 + 249799 * 2 ^ 59
def prefixEnd_249799 : Nat := 4983230072969 + 3 ^ 40 * 249799 * 2
def baseEnd_249799 : Nat := 42755651337524464654567

theorem tailTrace_249799 : CollatzResearch.WordTrace tailWord_249799 prefixEnd_249799 42755651337524464654567 := by
  unfold tailWord_249799
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110918022028360117792451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6073945348018906745194967 9110918022028360117792451)
  ·
    refine ⟨13666377033042540176688677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110918022028360117792451 13666377033042540176688677)
    ·
      refine ⟨2562445693695476283129127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13666377033042540176688677 2562445693695476283129127)
      ·
        refine ⟨3843668540543214424693691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562445693695476283129127 3843668540543214424693691)
        ·
          refine ⟨5765502810814821637040537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843668540543214424693691 5765502810814821637040537)
          ·
            refine ⟨4324127108111116227780403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5765502810814821637040537 4324127108111116227780403)
            ·
              refine ⟨6486190662166674341670605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324127108111116227780403 6486190662166674341670605)
              ·
                refine ⟨2432321498312502878126477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6486190662166674341670605 2432321498312502878126477)
                ·
                  refine ⟨912120561867188579297429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2432321498312502878126477 912120561867188579297429)
                  ·
                    refine ⟨42755651337524464654567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 912120561867188579297429 42755651337524464654567)
                    ·
                      rfl

theorem cell23_249799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_249799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249799 prefixEnd_249799 := by exact prefixLift 249799
  have htrace : WordTrace (prefixWord ++ tailWord_249799) baseStart_249799 baseEnd_249799 := by
    simpa [prefixWord, tailWord_249799, baseEnd_249799] using wordTrace_append hprefix tailTrace_249799
  have hstable : (prefixWord ++ tailWord_249799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249799).length < 2 ^ (prefixWord ++ tailWord_249799).sum := by decide
  have hdescent : baseEnd_249799 < baseStart_249799 := by decide
  rcases family_descends (prefixWord ++ tailWord_249799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249816 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_249816 : Nat := 118140960795 + 249816 * 2 ^ 59
def prefixEnd_249816 : Nat := 4983230072969 + 3 ^ 40 * 249816 * 2
def baseEnd_249816 : Nat := 42758561061233275817041

theorem tailTrace_249816 : CollatzResearch.WordTrace tailWord_249816 prefixEnd_249816 42758561061233275817041 := by
  unfold tailWord_249816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555769031483386010580651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6074358708644514680774201 4555769031483386010580651)
  ·
    refine ⟨6833653547225079015870977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4555769031483386010580651 6833653547225079015870977)
    ·
      refine ⟨5125240160418809261903233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6833653547225079015870977 5125240160418809261903233)
      ·
        refine ⟨3843930120314106946427425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125240160418809261903233 3843930120314106946427425)
        ·
          refine ⟨2882947590235580209820569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3843930120314106946427425 2882947590235580209820569)
          ·
            refine ⟨2162210692676685157365427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882947590235580209820569 2162210692676685157365427)
            ·
              refine ⟨3243316039015027736048141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162210692676685157365427 3243316039015027736048141)
              ·
                refine ⟨1216243514630635401018053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243316039015027736048141 1216243514630635401018053)
                ·
                  refine ⟨228045658993244137690885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216243514630635401018053 228045658993244137690885)
                  ·
                    refine ⟨42758561061233275817041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228045658993244137690885 42758561061233275817041)
                    ·
                      rfl

theorem cell23_249816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_249816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249816 prefixEnd_249816 := by exact prefixLift 249816
  have htrace : WordTrace (prefixWord ++ tailWord_249816) baseStart_249816 baseEnd_249816 := by
    simpa [prefixWord, tailWord_249816, baseEnd_249816] using wordTrace_append hprefix tailTrace_249816
  have hstable : (prefixWord ++ tailWord_249816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249816).length < 2 ^ (prefixWord ++ tailWord_249816).sum := by decide
  have hdescent : baseEnd_249816 < baseStart_249816 := by decide
  rcases family_descends (prefixWord ++ tailWord_249816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249817 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 3, 1, 3]
def baseStart_249817 : Nat := 118140960795 + 249817 * 2 ^ 59
def prefixEnd_249817 : Nat := 4983230072969 + 3 ^ 40 * 249817 * 2
def baseEnd_249817 : Nat := 128276196664354323538619

theorem tailTrace_249817 : CollatzResearch.WordTrace tailWord_249817 prefixEnd_249817 128276196664354323538619 := by
  unfold tailWord_249817
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111574535963149191947705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6074383023975432794631803 9111574535963149191947705)
  ·
    refine ⟨6833680901972361893960779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9111574535963149191947705 6833680901972361893960779)
    ·
      refine ⟨10250521352958542840941169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833680901972361893960779 10250521352958542840941169)
      ·
        refine ⟨7687891014718907130705877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10250521352958542840941169 7687891014718907130705877)
        ·
          refine ⟨180184945657474385875919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7687891014718907130705877 180184945657474385875919)
          ·
            refine ⟨270277418486211578813879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180184945657474385875919 270277418486211578813879)
            ·
              refine ⟨405416127729317368220819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270277418486211578813879 405416127729317368220819)
              ·
                refine ⟨608124191593976052331229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405416127729317368220819 608124191593976052331229)
                ·
                  refine ⟨228046571847741019624211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608124191593976052331229 228046571847741019624211)
                  ·
                    refine ⟨342069857771611529436317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228046571847741019624211 342069857771611529436317)
                    ·
                      refine ⟨128276196664354323538619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342069857771611529436317 128276196664354323538619)
                      ·
                        rfl

theorem cell23_249817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_249817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249817 prefixEnd_249817 := by exact prefixLift 249817
  have htrace : WordTrace (prefixWord ++ tailWord_249817) baseStart_249817 baseEnd_249817 := by
    simpa [prefixWord, tailWord_249817, baseEnd_249817] using wordTrace_append hprefix tailTrace_249817
  have hstable : (prefixWord ++ tailWord_249817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249817).length < 2 ^ (prefixWord ++ tailWord_249817).sum := by decide
  have hdescent : baseEnd_249817 < baseStart_249817 := by decide
  rcases family_descends (prefixWord ++ tailWord_249817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249837 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_249837 : Nat := 118140960795 + 249837 * 2 ^ 59
def prefixEnd_249837 : Nat := 4983230072969 + 3 ^ 40 * 249837 * 2
def baseEnd_249837 : Nat := 42762155425814748429509

theorem tailTrace_249837 : CollatzResearch.WordTrace tailWord_249837 prefixEnd_249837 42762155425814748429509 := by
  unfold tailWord_249837
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112303995890692607675765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6074869330593795071783843 9112303995890692607675765)
  ·
    refine ⟨854278499614752431969603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9112303995890692607675765 854278499614752431969603)
    ·
      refine ⟨1281417749422128647954405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854278499614752431969603 1281417749422128647954405)
      ·
        refine ⟨240265828016649121491451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1281417749422128647954405 240265828016649121491451)
        ·
          refine ⟨360398742024973682237177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240265828016649121491451 360398742024973682237177)
          ·
            refine ⟨270299056518730261677883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360398742024973682237177 270299056518730261677883)
            ·
              refine ⟨405448584778095392516825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270299056518730261677883 405448584778095392516825)
              ·
                refine ⟨304086438583571544387619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405448584778095392516825 304086438583571544387619)
                ·
                  refine ⟨456129657875357316581429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304086438583571544387619 456129657875357316581429)
                  ·
                    refine ⟨42762155425814748429509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 456129657875357316581429 42762155425814748429509)
                    ·
                      rfl

theorem cell23_249837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_249837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249837 prefixEnd_249837 := by exact prefixLift 249837
  have htrace : WordTrace (prefixWord ++ tailWord_249837) baseStart_249837 baseEnd_249837 := by
    simpa [prefixWord, tailWord_249837, baseEnd_249837] using wordTrace_append hprefix tailTrace_249837
  have hstable : (prefixWord ++ tailWord_249837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249837).length < 2 ^ (prefixWord ++ tailWord_249837).sum := by decide
  have hdescent : baseEnd_249837 < baseStart_249837 := by decide
  rcases family_descends (prefixWord ++ tailWord_249837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249857 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_249857 : Nat := 118140960795 + 249857 * 2 ^ 59
def prefixEnd_249857 : Nat := 4983230072969 + 3 ^ 40 * 249857 * 2
def baseEnd_249857 : Nat := 128296735890534167038435

theorem tailTrace_249857 : CollatzResearch.WordTrace tailWord_249857 prefixEnd_249857 128296735890534167038435 := by
  unfold tailWord_249857
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113033455818236023403825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6075355637212157348935883 9113033455818236023403825)
  ·
    refine ⟨6834775091863677017552869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9113033455818236023403825 6834775091863677017552869)
    ·
      refine ⟨1281520329724439440791163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6834775091863677017552869 1281520329724439440791163)
      ·
        refine ⟨1922280494586659161186745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281520329724439440791163 1922280494586659161186745)
        ·
          refine ⟨1441710370939994370890059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922280494586659161186745 1441710370939994370890059)
          ·
            refine ⟨2162565556409991556335089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441710370939994370890059 2162565556409991556335089)
            ·
              refine ⟨1621924167307493667251317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162565556409991556335089 1621924167307493667251317)
              ·
                refine ⟨152055390685077531304811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1621924167307493667251317 152055390685077531304811)
                ·
                  refine ⟨228083086027616296957217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152055390685077531304811 228083086027616296957217)
                  ·
                    refine ⟨171062314520712222717913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228083086027616296957217 171062314520712222717913)
                    ·
                      refine ⟨128296735890534167038435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171062314520712222717913 128296735890534167038435)
                      ·
                        rfl

theorem cell23_249857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_249857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249857 prefixEnd_249857 := by exact prefixLift 249857
  have htrace : WordTrace (prefixWord ++ tailWord_249857) baseStart_249857 baseEnd_249857 := by
    simpa [prefixWord, tailWord_249857, baseEnd_249857] using wordTrace_append hprefix tailTrace_249857
  have hstable : (prefixWord ++ tailWord_249857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249857).length < 2 ^ (prefixWord ++ tailWord_249857).sum := by decide
  have hdescent : baseEnd_249857 < baseStart_249857 := by decide
  rcases family_descends (prefixWord ++ tailWord_249857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249859 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 7]
def baseStart_249859 : Nat := 118140960795 + 249859 * 2 ^ 59
def prefixEnd_249859 : Nat := 4983230072969 + 3 ^ 40 * 249859 * 2
def baseEnd_249859 : Nat := 42765920950614386404475

theorem tailTrace_249859 : CollatzResearch.WordTrace tailWord_249859 prefixEnd_249859 42765920950614386404475 := by
  unfold tailWord_249859
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113106401810990364976631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6075404267873993576651087 9113106401810990364976631)
  ·
    refine ⟨13669659602716485547464947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113106401810990364976631 13669659602716485547464947)
    ·
      refine ⟨20504489404074728321197421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13669659602716485547464947 20504489404074728321197421)
      ·
        refine ⟨7689183526528023120449033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20504489404074728321197421 7689183526528023120449033)
        ·
          refine ⟨5766887644896017340336775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7689183526528023120449033 5766887644896017340336775)
          ·
            refine ⟨8650331467344026010505163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766887644896017340336775 8650331467344026010505163)
            ·
              refine ⟨12975497201016039015757745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650331467344026010505163 12975497201016039015757745)
              ·
                refine ⟨9731622900762029261818309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12975497201016039015757745 9731622900762029261818309)
                ·
                  refine ⟨1824679293892880486590933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9731622900762029261818309 1824679293892880486590933)
                  ·
                    refine ⟨42765920950614386404475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1824679293892880486590933 42765920950614386404475)
                    ·
                      rfl

theorem cell23_249859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_249859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249859 prefixEnd_249859 := by exact prefixLift 249859
  have htrace : WordTrace (prefixWord ++ tailWord_249859) baseStart_249859 baseEnd_249859 := by
    simpa [prefixWord, tailWord_249859, baseEnd_249859] using wordTrace_append hprefix tailTrace_249859
  have hstable : (prefixWord ++ tailWord_249859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249859).length < 2 ^ (prefixWord ++ tailWord_249859).sum := by decide
  have hdescent : baseEnd_249859 < baseStart_249859 := by decide
  rcases family_descends (prefixWord ++ tailWord_249859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249890 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_249890 : Nat := 118140960795 + 249890 * 2 ^ 59
def prefixEnd_249890 : Nat := 4983230072969 + 3 ^ 40 * 249890 * 2
def baseEnd_249890 : Nat := 128313680752132537925783

theorem tailTrace_249890 : CollatzResearch.WordTrace tailWord_249890 prefixEnd_249890 128313680752132537925783 := by
  unfold tailWord_249890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278559266174670664838781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6076158043132455106236749 2278559266174670664838781)
  ·
    refine ⟨854459724815501499314543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2278559266174670664838781 854459724815501499314543)
    ·
      refine ⟨1281689587223252248971815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854459724815501499314543 1281689587223252248971815)
      ·
        refine ⟨1922534380834878373457723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281689587223252248971815 1922534380834878373457723)
        ·
          refine ⟨2883801571252317560186585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922534380834878373457723 2883801571252317560186585)
          ·
            refine ⟨2162851178439238170139939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2883801571252317560186585 2162851178439238170139939)
            ·
              refine ⟨3244276767658857255209909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162851178439238170139939 3244276767658857255209909)
              ·
                refine ⟨304150946968017867675929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3244276767658857255209909 304150946968017867675929)
                ·
                  refine ⟨228113210226013400756947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304150946968017867675929 228113210226013400756947)
                  ·
                    refine ⟨342169815339020101135421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228113210226013400756947 342169815339020101135421)
                    ·
                      refine ⟨128313680752132537925783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342169815339020101135421 128313680752132537925783)
                      ·
                        rfl

theorem cell23_249890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_249890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249890 prefixEnd_249890 := by exact prefixLift 249890
  have htrace : WordTrace (prefixWord ++ tailWord_249890) baseStart_249890 baseEnd_249890 := by
    simpa [prefixWord, tailWord_249890, baseEnd_249890] using wordTrace_append hprefix tailTrace_249890
  have hstable : (prefixWord ++ tailWord_249890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249890).length < 2 ^ (prefixWord ++ tailWord_249890).sum := by decide
  have hdescent : baseEnd_249890 < baseStart_249890 := by decide
  rcases family_descends (prefixWord ++ tailWord_249890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249916 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_249916 : Nat := 118140960795 + 249916 * 2 ^ 59
def prefixEnd_249916 : Nat := 4983230072969 + 3 ^ 40 * 249916 * 2
def baseEnd_249916 : Nat := 128327031249149436200663

theorem tailTrace_249916 : CollatzResearch.WordTrace tailWord_249916 prefixEnd_249916 128327031249149436200663 := by
  unfold tailWord_249916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557592681302244549900801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6076790241736326066534401 4557592681302244549900801)
  ·
    refine ⟨3418194510976683412425601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4557592681302244549900801 3418194510976683412425601)
    ·
      refine ⟨2563645883232512559319201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3418194510976683412425601 2563645883232512559319201)
      ·
        refine ⟨1922734412424384419489401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2563645883232512559319201 1922734412424384419489401)
        ·
          refine ⟨1442050809318288314617051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922734412424384419489401 1442050809318288314617051)
          ·
            refine ⟨2163076213977432471925577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442050809318288314617051 2163076213977432471925577)
            ·
              refine ⟨1622307160483074353944183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163076213977432471925577 1622307160483074353944183)
              ·
                refine ⟨2433460740724611530916275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622307160483074353944183 2433460740724611530916275)
                ·
                  refine ⟨3650191111086917296374413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433460740724611530916275 3650191111086917296374413)
                  ·
                    refine ⟨1368821666657593986140405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650191111086917296374413 1368821666657593986140405)
                    ·
                      refine ⟨128327031249149436200663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1368821666657593986140405 128327031249149436200663)
                      ·
                        rfl

theorem cell23_249916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_249916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249916 prefixEnd_249916 := by exact prefixLift 249916
  have htrace : WordTrace (prefixWord ++ tailWord_249916) baseStart_249916 baseEnd_249916 := by
    simpa [prefixWord, tailWord_249916, baseEnd_249916] using wordTrace_append hprefix tailTrace_249916
  have hstable : (prefixWord ++ tailWord_249916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249916).length < 2 ^ (prefixWord ++ tailWord_249916).sum := by decide
  have hdescent : baseEnd_249916 < baseStart_249916 := by decide
  rcases family_descends (prefixWord ++ tailWord_249916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249970 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_249970 : Nat := 118140960795 + 249970 * 2 ^ 59
def prefixEnd_249970 : Nat := 4983230072969 + 3 ^ 40 * 249970 * 2
def baseEnd_249970 : Nat := 14261639911610247213935

theorem tailTrace_249970 : CollatzResearch.WordTrace tailWord_249970 prefixEnd_249970 14261639911610247213935 := by
  unfold tailWord_249970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279288726102214080566841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6078103269605904214844909 2279288726102214080566841)
  ·
    refine ⟨1709466544576660560425131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2279288726102214080566841 1709466544576660560425131)
    ·
      refine ⟨2564199816864990840637697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709466544576660560425131 2564199816864990840637697)
      ·
        refine ⟨1923149862648743130478273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2564199816864990840637697 1923149862648743130478273)
        ·
          refine ⟨1442362396986557347858705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1923149862648743130478273 1442362396986557347858705)
          ·
            refine ⟨1081771797739918010894029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1442362396986557347858705 1081771797739918010894029)
            ·
              refine ⟨405664424152469254085261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1081771797739918010894029 405664424152469254085261)
              ·
                refine ⟨152124159057175970281973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405664424152469254085261 152124159057175970281973)
                ·
                  refine ⟨14261639911610247213935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152124159057175970281973 14261639911610247213935)
                  ·
                    rfl

theorem cell23_249970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_249970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249970 prefixEnd_249970 := by exact prefixLift 249970
  have htrace : WordTrace (prefixWord ++ tailWord_249970) baseStart_249970 baseEnd_249970 := by
    simpa [prefixWord, tailWord_249970, baseEnd_249970] using wordTrace_append hprefix tailTrace_249970
  have hstable : (prefixWord ++ tailWord_249970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249970).length < 2 ^ (prefixWord ++ tailWord_249970).sum := by decide
  have hdescent : baseEnd_249970 < baseStart_249970 := by decide
  rcases family_descends (prefixWord ++ tailWord_249970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249976 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_249976 : Nat := 118140960795 + 249976 * 2 ^ 59
def prefixEnd_249976 : Nat := 4983230072969 + 3 ^ 40 * 249976 * 2
def baseEnd_249976 : Nat := 128357840088419201450387

theorem tailTrace_249976 : CollatzResearch.WordTrace tailWord_249976 prefixEnd_249976 128357840088419201450387 := by
  unfold tailWord_249976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558686871193559673492891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6078249161591412897990521 4558686871193559673492891)
  ·
    refine ⟨6838030306790339510239337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4558686871193559673492891 6838030306790339510239337)
    ·
      refine ⟨5128522730092754632679503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6838030306790339510239337 5128522730092754632679503)
      ·
        refine ⟨7692784095139131949019255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128522730092754632679503 7692784095139131949019255)
        ·
          refine ⟨11539176142708697923528883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692784095139131949019255 11539176142708697923528883)
          ·
            refine ⟨17308764214063046885293325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539176142708697923528883 17308764214063046885293325)
            ·
              refine ⟨6490786580273642581984997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17308764214063046885293325 6490786580273642581984997)
              ·
                refine ⟨1217022483801307984122187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6490786580273642581984997 1217022483801307984122187)
                ·
                  refine ⟨1825533725701961976183281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217022483801307984122187 1825533725701961976183281)
                  ·
                    refine ⟨1369150294276471482137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1825533725701961976183281 1369150294276471482137461)
                    ·
                      refine ⟨128357840088419201450387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1369150294276471482137461 128357840088419201450387)
                      ·
                        rfl

theorem cell23_249976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_249976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249976 prefixEnd_249976 := by exact prefixLift 249976
  have htrace : WordTrace (prefixWord ++ tailWord_249976) baseStart_249976 baseEnd_249976 := by
    simpa [prefixWord, tailWord_249976, baseEnd_249976] using wordTrace_append hprefix tailTrace_249976
  have hstable : (prefixWord ++ tailWord_249976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249976).length < 2 ^ (prefixWord ++ tailWord_249976).sum := by decide
  have hdescent : baseEnd_249976 < baseStart_249976 := by decide
  rcases family_descends (prefixWord ++ tailWord_249976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249998 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_249998 : Nat := 118140960795 + 249998 * 2 ^ 59
def prefixEnd_249998 : Nat := 4983230072969 + 3 ^ 40 * 249998 * 2
def baseEnd_249998 : Nat := 128369136662818115375287

theorem tailTrace_249998 : CollatzResearch.WordTrace tailWord_249998 prefixEnd_249998 128369136662818115375287 := by
  unfold tailWord_249998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139772018538427138035831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6078784098871611402857765 1139772018538427138035831)
  ·
    refine ⟨1709658027807640707053747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139772018538427138035831 1709658027807640707053747)
    ·
      refine ⟨2564487041711461060580621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709658027807640707053747 2564487041711461060580621)
      ·
        refine ⟨961682640641797897717733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2564487041711461060580621 961682640641797897717733)
        ·
          refine ⟨180315495120337105822075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 961682640641797897717733 180315495120337105822075)
          ·
            refine ⟨270473242680505658733113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180315495120337105822075 270473242680505658733113)
            ·
              refine ⟨202854932010379244049835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270473242680505658733113 202854932010379244049835)
              ·
                refine ⟨304282398015568866074753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202854932010379244049835 304282398015568866074753)
                ·
                  refine ⟨228211798511676649556065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304282398015568866074753 228211798511676649556065)
                  ·
                    refine ⟨171158848883757487167049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228211798511676649556065 171158848883757487167049)
                    ·
                      refine ⟨128369136662818115375287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171158848883757487167049 128369136662818115375287)
                      ·
                        rfl

theorem cell23_249998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_249998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249998 prefixEnd_249998 := by exact prefixLift 249998
  have htrace : WordTrace (prefixWord ++ tailWord_249998) baseStart_249998 baseEnd_249998 := by
    simpa [prefixWord, tailWord_249998, baseEnd_249998] using wordTrace_append hprefix tailTrace_249998
  have hstable : (prefixWord ++ tailWord_249998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249998).length < 2 ^ (prefixWord ++ tailWord_249998).sum := by decide
  have hdescent : baseEnd_249998 < baseStart_249998 := by decide
  rcases family_descends (prefixWord ++ tailWord_249998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250003 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 6, 2]
def baseStart_250003 : Nat := 118140960795 + 250003 * 2 ^ 59
def prefixEnd_250003 : Nat := 4983230072969 + 3 ^ 40 * 250003 * 2
def baseEnd_250003 : Nat := 128371704066090595812763

theorem tailTrace_250003 : CollatzResearch.WordTrace tailWord_250003 prefixEnd_250003 128371704066090595812763 := by
  unfold tailWord_250003
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118358513289302958218663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6078905675526201972145775 9118358513289302958218663)
  ·
    refine ⟨13677537769933954437327995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9118358513289302958218663 13677537769933954437327995)
    ·
      refine ⟨20516306654900931655991993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13677537769933954437327995 20516306654900931655991993)
      ·
        refine ⟨15387229991175698741993995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20516306654900931655991993 15387229991175698741993995)
        ·
          refine ⟨23080844986763548112990993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387229991175698741993995 23080844986763548112990993)
          ·
            refine ⟨17310633740072661084743245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23080844986763548112990993 17310633740072661084743245)
            ·
              refine ⟨6491487652527247906778717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17310633740072661084743245 6491487652527247906778717)
              ·
                refine ⟨2434307869697717965042019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6491487652527247906778717 2434307869697717965042019)
                ·
                  refine ⟨3651461804546576947563029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434307869697717965042019 3651461804546576947563029)
                  ·
                    refine ⟨171162272088120794417017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3651461804546576947563029 171162272088120794417017)
                    ·
                      refine ⟨128371704066090595812763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171162272088120794417017 128371704066090595812763)
                      ·
                        rfl

theorem cell23_250003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6, 2].length) (baseStart_250003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250003 prefixEnd_250003 := by exact prefixLift 250003
  have htrace : WordTrace (prefixWord ++ tailWord_250003) baseStart_250003 baseEnd_250003 := by
    simpa [prefixWord, tailWord_250003, baseEnd_250003] using wordTrace_append hprefix tailTrace_250003
  have hstable : (prefixWord ++ tailWord_250003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250003).length < 2 ^ (prefixWord ++ tailWord_250003).sum := by decide
  have hdescent : baseEnd_250003 < baseStart_250003 := by decide
  rcases family_descends (prefixWord ++ tailWord_250003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250043 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 6]
def baseStart_250043 : Nat := 118140960795 + 250043 * 2 ^ 59
def prefixEnd_250043 : Nat := 4983230072969 + 3 ^ 40 * 250043 * 2
def baseEnd_250043 : Nat := 14265804810252271034731

theorem tailTrace_250043 : CollatzResearch.WordTrace tailWord_250043 prefixEnd_250043 14265804810252271034731 := by
  unfold tailWord_250043
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119817433144389789674783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6079878288762926526449855 9119817433144389789674783)
  ·
    refine ⟨13679726149716584684512175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9119817433144389789674783 13679726149716584684512175)
    ·
      refine ⟨20519589224574877026768263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13679726149716584684512175 20519589224574877026768263)
      ·
        refine ⟨30779383836862315540152395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20519589224574877026768263 30779383836862315540152395)
        ·
          refine ⟨46169075755293473310228593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30779383836862315540152395 46169075755293473310228593)
          ·
            refine ⟨34626806816470104982671445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46169075755293473310228593 34626806816470104982671445)
            ·
              refine ⟨405782892380509042765681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 34626806816470104982671445 405782892380509042765681)
              ·
                refine ⟨304337169285381782074261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405782892380509042765681 304337169285381782074261)
                ·
                  refine ⟨14265804810252271034731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304337169285381782074261 14265804810252271034731)
                  ·
                    rfl

theorem cell23_250043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 6].length) (baseStart_250043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250043 prefixEnd_250043 := by exact prefixLift 250043
  have htrace : WordTrace (prefixWord ++ tailWord_250043) baseStart_250043 baseEnd_250043 := by
    simpa [prefixWord, tailWord_250043, baseEnd_250043] using wordTrace_append hprefix tailTrace_250043
  have hstable : (prefixWord ++ tailWord_250043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250043).length < 2 ^ (prefixWord ++ tailWord_250043).sum := by decide
  have hdescent : baseEnd_250043 < baseStart_250043 := by decide
  rcases family_descends (prefixWord ++ tailWord_250043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250073 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_250073 : Nat := 118140960795 + 250073 * 2 ^ 59
def prefixEnd_250073 : Nat := 4983230072969 + 3 ^ 40 * 250073 * 2
def baseEnd_250073 : Nat := 42802549237301773979147

theorem tailTrace_250073 : CollatzResearch.WordTrace tailWord_250073 prefixEnd_250073 42802549237301773979147 := by
  unfold tailWord_250073
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120911623035704913266873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6080607748690469942177915 9120911623035704913266873)
  ·
    refine ⟨6840683717276778684950155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9120911623035704913266873 6840683717276778684950155)
    ·
      refine ⟨10261025575915168027425233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840683717276778684950155 10261025575915168027425233)
      ·
        refine ⟨7695769181936376020568925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10261025575915168027425233 7695769181936376020568925)
        ·
          refine ⟨2885913443226141007713347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7695769181936376020568925 2885913443226141007713347)
          ·
            refine ⟨4328870164839211511570021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885913443226141007713347 4328870164839211511570021)
            ·
              refine ⟨811663155907352158419379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4328870164839211511570021 811663155907352158419379)
              ·
                refine ⟨1217494733861028237629069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811663155907352158419379 1217494733861028237629069)
                ·
                  refine ⟨456560525197885589110901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217494733861028237629069 456560525197885589110901)
                  ·
                    refine ⟨42802549237301773979147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 456560525197885589110901 42802549237301773979147)
                    ·
                      rfl

theorem cell23_250073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_250073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250073 prefixEnd_250073 := by exact prefixLift 250073
  have htrace : WordTrace (prefixWord ++ tailWord_250073) baseStart_250073 baseEnd_250073 := by
    simpa [prefixWord, tailWord_250073, baseEnd_250073] using wordTrace_append hprefix tailTrace_250073
  have hstable : (prefixWord ++ tailWord_250073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250073).length < 2 ^ (prefixWord ++ tailWord_250073).sum := by decide
  have hdescent : baseEnd_250073 < baseStart_250073 := by decide
  rcases family_descends (prefixWord ++ tailWord_250073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250080 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2]
def baseStart_250080 : Nat := 118140960795 + 250080 * 2 ^ 59
def prefixEnd_250080 : Nat := 4983230072969 + 3 ^ 40 * 250080 * 2
def baseEnd_250080 : Nat := 128411242076486794549909

theorem tailTrace_250080 : CollatzResearch.WordTrace tailWord_250080 prefixEnd_250080 128411242076486794549909 := by
  unfold tailWord_250080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560583467005172554385847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6080777956006896739181129 4560583467005172554385847)
  ·
    refine ⟨6840875200507758831578771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560583467005172554385847 6840875200507758831578771)
    ·
      refine ⟨10261312800761638247368157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840875200507758831578771 10261312800761638247368157)
      ·
        refine ⟨3847992300285614342763059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10261312800761638247368157 3847992300285614342763059)
        ·
          refine ⟨5771988450428421514144589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847992300285614342763059 5771988450428421514144589)
          ·
            refine ⟨2164495668910658067804221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5771988450428421514144589 2164495668910658067804221)
            ·
              refine ⟨811685875841496775426583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164495668910658067804221 811685875841496775426583)
              ·
                refine ⟨1217528813762245163139875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811685875841496775426583 1217528813762245163139875)
                ·
                  refine ⟨1826293220643367744709813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217528813762245163139875 1826293220643367744709813)
                  ·
                    refine ⟨171214989435315726066545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1826293220643367744709813 171214989435315726066545)
                    ·
                      refine ⟨128411242076486794549909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171214989435315726066545 128411242076486794549909)
                      ·
                        rfl

theorem cell23_250080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_250080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250080 prefixEnd_250080 := by exact prefixLift 250080
  have htrace : WordTrace (prefixWord ++ tailWord_250080) baseStart_250080 baseEnd_250080 := by
    simpa [prefixWord, tailWord_250080, baseEnd_250080] using wordTrace_append hprefix tailTrace_250080
  have hstable : (prefixWord ++ tailWord_250080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250080).length < 2 ^ (prefixWord ++ tailWord_250080).sum := by decide
  have hdescent : baseEnd_250080 < baseStart_250080 := by decide
  rcases family_descends (prefixWord ++ tailWord_250080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250090 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_250090 : Nat := 118140960795 + 250090 * 2 ^ 59
def prefixEnd_250090 : Nat := 4983230072969 + 3 ^ 40 * 250090 * 2
def baseEnd_250090 : Nat := 42805458961010585141621

theorem tailTrace_250090 : CollatzResearch.WordTrace tailWord_250090 prefixEnd_250090 42805458961010585141621 := by
  unfold tailWord_250090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280382915993529204158931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6081021109316077877757149 2280382915993529204158931)
  ·
    refine ⟨3420574373990293806238397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280382915993529204158931 3420574373990293806238397)
    ·
      refine ⟨1282715390246360177339399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3420574373990293806238397 1282715390246360177339399)
      ·
        refine ⟨1924073085369540266009099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282715390246360177339399 1924073085369540266009099)
        ·
          refine ⟨2886109628054310399013649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924073085369540266009099 2886109628054310399013649)
          ·
            refine ⟨2164582221040732799260237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886109628054310399013649 2164582221040732799260237)
            ·
              refine ⟨811718332890274799722589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164582221040732799260237 811718332890274799722589)
              ·
                refine ⟨304394374833853049895971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811718332890274799722589 304394374833853049895971)
                ·
                  refine ⟨456591562250779574843957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304394374833853049895971 456591562250779574843957)
                  ·
                    refine ⟨42805458961010585141621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 456591562250779574843957 42805458961010585141621)
                    ·
                      rfl

theorem cell23_250090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_250090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250090 prefixEnd_250090 := by exact prefixLift 250090
  have htrace : WordTrace (prefixWord ++ tailWord_250090) baseStart_250090 baseEnd_250090 := by
    simpa [prefixWord, tailWord_250090, baseEnd_250090] using wordTrace_append hprefix tailTrace_250090
  have hstable : (prefixWord ++ tailWord_250090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250090).length < 2 ^ (prefixWord ++ tailWord_250090).sum := by decide
  have hdescent : baseEnd_250090 < baseStart_250090 := by decide
  rcases family_descends (prefixWord ++ tailWord_250090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250120 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_250120 : Nat := 118140960795 + 250120 * 2 ^ 59
def prefixEnd_250120 : Nat := 4983230072969 + 3 ^ 40 * 250120 * 2
def baseEnd_250120 : Nat := 42810593767555546016575

theorem tailTrace_250120 : CollatzResearch.WordTrace tailWord_250120 prefixEnd_250120 42810593767555546016575 := by
  unfold tailWord_250120
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561312926932715970113907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6081750569243621293485209 4561312926932715970113907)
  ·
    refine ⟨6841969390399073955170861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561312926932715970113907 6841969390399073955170861)
    ·
      refine ⟨2565738521399652733189073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6841969390399073955170861 2565738521399652733189073)
      ·
        refine ⟨1924303891049739549891805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2565738521399652733189073 1924303891049739549891805)
        ·
          refine ⟨721613959143652331209427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1924303891049739549891805 721613959143652331209427)
          ·
            refine ⟨1082420938715478496814141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721613959143652331209427 1082420938715478496814141)
            ·
              refine ⟨405907852018304436305303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1082420938715478496814141 405907852018304436305303)
              ·
                refine ⟨608861778027456654457955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405907852018304436305303 608861778027456654457955)
                ·
                  refine ⟨913292667041184981686933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608861778027456654457955 913292667041184981686933)
                  ·
                    refine ⟨42810593767555546016575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 913292667041184981686933 42810593767555546016575)
                    ·
                      rfl

theorem cell23_250120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_250120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250120 prefixEnd_250120 := by exact prefixLift 250120
  have htrace : WordTrace (prefixWord ++ tailWord_250120) baseStart_250120 baseEnd_250120 := by
    simpa [prefixWord, tailWord_250120, baseEnd_250120] using wordTrace_append hprefix tailTrace_250120
  have hstable : (prefixWord ++ tailWord_250120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250120).length < 2 ^ (prefixWord ++ tailWord_250120).sum := by decide
  have hdescent : baseEnd_250120 < baseStart_250120 := by decide
  rcases family_descends (prefixWord ++ tailWord_250120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250123 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_250123 : Nat := 118140960795 + 250123 * 2 ^ 59
def prefixEnd_250123 : Nat := 4983230072969 + 3 ^ 40 * 250123 * 2
def baseEnd_250123 : Nat := 128433321744630126312211

theorem tailTrace_250123 : CollatzResearch.WordTrace tailWord_250123 prefixEnd_250123 128433321744630126312211 := by
  unfold tailWord_250123
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122735272854563452587023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6081823515236375635058015 9122735272854563452587023)
  ·
    refine ⟨13684102909281845178880535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9122735272854563452587023 13684102909281845178880535)
    ·
      refine ⟨20526154363922767768320803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13684102909281845178880535 20526154363922767768320803)
      ·
        refine ⟨30789231545884151652481205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20526154363922767768320803 30789231545884151652481205)
        ·
          refine ⟨2886490457426639217420113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30789231545884151652481205 2886490457426639217420113)
          ·
            refine ⟨2164867843069979413065085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886490457426639217420113 2164867843069979413065085)
            ·
              refine ⟨811825441151242279899407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164867843069979413065085 811825441151242279899407)
              ·
                refine ⟨1217738161726863419849111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811825441151242279899407 1217738161726863419849111)
                ·
                  refine ⟨1826607242590295129773667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217738161726863419849111 1826607242590295129773667)
                  ·
                    refine ⟨2739910863885442694660501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1826607242590295129773667 2739910863885442694660501)
                    ·
                      refine ⟨128433321744630126312211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2739910863885442694660501 128433321744630126312211)
                      ·
                        rfl

theorem cell23_250123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_250123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250123 prefixEnd_250123 := by exact prefixLift 250123
  have htrace : WordTrace (prefixWord ++ tailWord_250123) baseStart_250123 baseEnd_250123 := by
    simpa [prefixWord, tailWord_250123, baseEnd_250123] using wordTrace_append hprefix tailTrace_250123
  have hstable : (prefixWord ++ tailWord_250123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250123).length < 2 ^ (prefixWord ++ tailWord_250123).sum := by decide
  have hdescent : baseEnd_250123 < baseStart_250123 := by decide
  rcases family_descends (prefixWord ++ tailWord_250123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250138 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3]
def baseStart_250138 : Nat := 118140960795 + 250138 * 2 ^ 59
def prefixEnd_250138 : Nat := 4983230072969 + 3 ^ 40 * 250138 * 2
def baseEnd_250138 : Nat := 128441023954447567624643

theorem tailTrace_250138 : CollatzResearch.WordTrace tailWord_250138 prefixEnd_250138 128441023954447567624643 := by
  unfold tailWord_250138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280820591950055253595767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6082188245200147342922045 2280820591950055253595767)
  ·
    refine ⟨3421230887925082880393651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280820591950055253595767 3421230887925082880393651)
    ·
      refine ⟨5131846331887624320590477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421230887925082880393651 5131846331887624320590477)
      ·
        refine ⟨1924442374457859120221429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5131846331887624320590477 1924442374457859120221429)
        ·
          refine ⟨180416472605424292520759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1924442374457859120221429 180416472605424292520759)
          ·
            refine ⟨270624708908136438781139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180416472605424292520759 270624708908136438781139)
            ·
              refine ⟨405937063362204658171709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270624708908136438781139 405937063362204658171709)
              ·
                refine ⟨152226398760826746814391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405937063362204658171709 152226398760826746814391)
                ·
                  refine ⟨228339598141240120221587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152226398760826746814391 228339598141240120221587)
                  ·
                    refine ⟨342509397211860180332381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228339598141240120221587 342509397211860180332381)
                    ·
                      refine ⟨128441023954447567624643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342509397211860180332381 128441023954447567624643)
                      ·
                        rfl

theorem cell23_250138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_250138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250138 prefixEnd_250138 := by exact prefixLift 250138
  have htrace : WordTrace (prefixWord ++ tailWord_250138) baseStart_250138 baseEnd_250138 := by
    simpa [prefixWord, tailWord_250138, baseEnd_250138] using wordTrace_append hprefix tailTrace_250138
  have hstable : (prefixWord ++ tailWord_250138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250138).length < 2 ^ (prefixWord ++ tailWord_250138).sum := by decide
  have hdescent : baseEnd_250138 < baseStart_250138 := by decide
  rcases family_descends (prefixWord ++ tailWord_250138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250161 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_250161 : Nat := 118140960795 + 250161 * 2 ^ 59
def prefixEnd_250161 : Nat := 4983230072969 + 3 ^ 40 * 250161 * 2
def baseEnd_250161 : Nat := 128452834009500977637037

theorem tailTrace_250161 : CollatzResearch.WordTrace tailWord_250161 prefixEnd_250161 128452834009500977637037 := by
  unfold tailWord_250161
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124121246716895942470337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6082747497811263961646891 9124121246716895942470337)
  ·
    refine ⟨6843090935037671956852753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9124121246716895942470337 6843090935037671956852753)
    ·
      refine ⟨5132318201278253967639565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6843090935037671956852753 5132318201278253967639565)
      ·
        refine ⟨1924619325479345237864837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5132318201278253967639565 1924619325479345237864837)
        ·
          refine ⟨360866123527377232099657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1924619325479345237864837 360866123527377232099657)
          ·
            refine ⟨270649592645532924074743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360866123527377232099657 270649592645532924074743)
            ·
              refine ⟨405974388968299386112115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270649592645532924074743 405974388968299386112115)
              ·
                refine ⟨608961583452449079168173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405974388968299386112115 608961583452449079168173)
                ·
                  refine ⟨228360593794668404688065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608961583452449079168173 228360593794668404688065)
                  ·
                    refine ⟨171270445346001303516049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228360593794668404688065 171270445346001303516049)
                    ·
                      refine ⟨128452834009500977637037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171270445346001303516049 128452834009500977637037)
                      ·
                        rfl

theorem cell23_250161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_250161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250161 prefixEnd_250161 := by exact prefixLift 250161
  have htrace : WordTrace (prefixWord ++ tailWord_250161) baseStart_250161 baseEnd_250161 := by
    simpa [prefixWord, tailWord_250161, baseEnd_250161] using wordTrace_append hprefix tailTrace_250161
  have hstable : (prefixWord ++ tailWord_250161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250161).length < 2 ^ (prefixWord ++ tailWord_250161).sum := by decide
  have hdescent : baseEnd_250161 < baseStart_250161 := by decide
  rcases family_descends (prefixWord ++ tailWord_250161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250163 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 7]
def baseStart_250163 : Nat := 118140960795 + 250163 * 2 ^ 59
def prefixEnd_250163 : Nat := 4983230072969 + 3 ^ 40 * 250163 * 2
def baseEnd_250163 : Nat := 42817953656936656604009

theorem tailTrace_250163 : CollatzResearch.WordTrace tailWord_250163 prefixEnd_250163 42817953656936656604009 := by
  unfold tailWord_250163
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124194192709650284043143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6082796128473100189362095 9124194192709650284043143)
  ·
    refine ⟨13686291289064475426064715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9124194192709650284043143 13686291289064475426064715)
    ·
      refine ⟨20529436933596713139097073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686291289064475426064715 20529436933596713139097073)
      ·
        refine ⟨15397077700197534854322805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20529436933596713139097073 15397077700197534854322805)
        ·
          refine ⟨1443476034393518892592763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15397077700197534854322805 1443476034393518892592763)
          ·
            refine ⟨2165214051590278338889145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443476034393518892592763 2165214051590278338889145)
            ·
              refine ⟨1623910538692708754166859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165214051590278338889145 1623910538692708754166859)
              ·
                refine ⟨2435865808039063131250289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623910538692708754166859 2435865808039063131250289)
                ·
                  refine ⟨1826899356029297348437717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2435865808039063131250289 1826899356029297348437717)
                  ·
                    refine ⟨42817953656936656604009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1826899356029297348437717 42817953656936656604009)
                    ·
                      rfl

theorem cell23_250163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_250163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250163 prefixEnd_250163 := by exact prefixLift 250163
  have htrace : WordTrace (prefixWord ++ tailWord_250163) baseStart_250163 baseEnd_250163 := by
    simpa [prefixWord, tailWord_250163, baseEnd_250163] using wordTrace_append hprefix tailTrace_250163
  have hstable : (prefixWord ++ tailWord_250163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250163).length < 2 ^ (prefixWord ++ tailWord_250163).sum := by decide
  have hdescent : baseEnd_250163 < baseStart_250163 := by decide
  rcases family_descends (prefixWord ++ tailWord_250163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250187 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 1, 3, 2]
def baseStart_250187 : Nat := 118140960795 + 250187 * 2 ^ 59
def prefixEnd_250187 : Nat := 4983230072969 + 3 ^ 40 * 250187 * 2
def baseEnd_250187 : Nat := 128466184506517875911917

theorem tailTrace_250187 : CollatzResearch.WordTrace tailWord_250187 prefixEnd_250187 128466184506517875911917 := by
  unfold tailWord_250187
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125069544622702382916815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6083379696415134921944543 9125069544622702382916815)
  ·
    refine ⟨13687604316934053574375223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9125069544622702382916815 13687604316934053574375223)
    ·
      refine ⟨20531406475401080361562835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13687604316934053574375223 20531406475401080361562835)
      ·
        refine ⟨30797109713101620542344253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20531406475401080361562835 30797109713101620542344253)
        ·
          refine ⟨11548916142413107703379095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30797109713101620542344253 11548916142413107703379095)
          ·
            refine ⟨17323374213619661555068643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548916142413107703379095 17323374213619661555068643)
            ·
              refine ⟨25985061320429492332602965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17323374213619661555068643 25985061320429492332602965)
              ·
                refine ⟨304512437348783113272691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 25985061320429492332602965 304512437348783113272691)
                ·
                  refine ⟨456768656023174669909037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304512437348783113272691 456768656023174669909037)
                  ·
                    refine ⟨171288246008690501215889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456768656023174669909037 171288246008690501215889)
                    ·
                      refine ⟨128466184506517875911917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171288246008690501215889 128466184506517875911917)
                      ·
                        rfl

theorem cell23_250187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3, 2].length) (baseStart_250187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250187 prefixEnd_250187 := by exact prefixLift 250187
  have htrace : WordTrace (prefixWord ++ tailWord_250187) baseStart_250187 baseEnd_250187 := by
    simpa [prefixWord, tailWord_250187, baseEnd_250187] using wordTrace_append hprefix tailTrace_250187
  have hstable : (prefixWord ++ tailWord_250187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250187).length < 2 ^ (prefixWord ++ tailWord_250187).sum := by decide
  have hdescent : baseEnd_250187 < baseStart_250187 := by decide
  rcases family_descends (prefixWord ++ tailWord_250187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250206 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_250206 : Nat := 118140960795 + 250206 * 2 ^ 59
def prefixEnd_250206 : Nat := 4983230072969 + 3 ^ 40 * 250206 * 2
def baseEnd_250206 : Nat := 128475940638953301574331

theorem tailTrace_250206 : CollatzResearch.WordTrace tailWord_250206 prefixEnd_250206 128475940638953301574331 := by
  unfold tailWord_250206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140720316444233578482309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6083841687702579085238981 1140720316444233578482309)
  ·
    refine ⟨213885059333293795965433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1140720316444233578482309 213885059333293795965433)
    ·
      refine ⟨160413794499970346974075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213885059333293795965433 160413794499970346974075)
      ·
        refine ⟨240620691749955520461113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160413794499970346974075 240620691749955520461113)
        ·
          refine ⟨180465518812466640345835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240620691749955520461113 180465518812466640345835)
          ·
            refine ⟨270698278218699960518753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180465518812466640345835 270698278218699960518753)
            ·
              refine ⟨203023708664024970389065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270698278218699960518753 203023708664024970389065)
              ·
                refine ⟨152267781498018727791799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203023708664024970389065 152267781498018727791799)
                ·
                  refine ⟨228401672247028091687699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152267781498018727791799 228401672247028091687699)
                  ·
                    refine ⟨342602508370542137531549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228401672247028091687699 342602508370542137531549)
                    ·
                      refine ⟨128475940638953301574331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342602508370542137531549 128475940638953301574331)
                      ·
                        rfl

theorem cell23_250206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_250206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250206 prefixEnd_250206 := by exact prefixLift 250206
  have htrace : WordTrace (prefixWord ++ tailWord_250206) baseStart_250206 baseEnd_250206 := by
    simpa [prefixWord, tailWord_250206, baseEnd_250206] using wordTrace_append hprefix tailTrace_250206
  have hstable : (prefixWord ++ tailWord_250206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250206).length < 2 ^ (prefixWord ++ tailWord_250206).sum := by decide
  have hdescent : baseEnd_250206 < baseStart_250206 := by decide
  rcases family_descends (prefixWord ++ tailWord_250206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250262 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_250262 : Nat := 118140960795 + 250262 * 2 ^ 59
def prefixEnd_250262 : Nat := 4983230072969 + 3 ^ 40 * 250262 * 2
def baseEnd_250262 : Nat := 128504695555605082474073

theorem tailTrace_250262 : CollatzResearch.WordTrace tailWord_250262 prefixEnd_250262 128504695555605082474073 := by
  unfold tailWord_250262
  simp only [CollatzResearch.WordTrace]
  refine ⟨570487813709436886993565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6085203346233993461264693 570487813709436886993565)
  ·
    refine ⟨213932930141038832622587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 570487813709436886993565 213932930141038832622587)
    ·
      refine ⟨320899395211558248933881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213932930141038832622587 320899395211558248933881)
      ·
        refine ⟨240674546408668686700411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320899395211558248933881 240674546408668686700411)
        ·
          refine ⟨361011819613003030050617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240674546408668686700411 361011819613003030050617)
          ·
            refine ⟨270758864709752272537963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361011819613003030050617 270758864709752272537963)
            ·
              refine ⟨406138297064628408806945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270758864709752272537963 406138297064628408806945)
              ·
                refine ⟨304603722798471306605209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406138297064628408806945 304603722798471306605209)
                ·
                  refine ⟨228452792098853479953907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304603722798471306605209 228452792098853479953907)
                  ·
                    refine ⟨342679188148280219930861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228452792098853479953907 342679188148280219930861)
                    ·
                      refine ⟨128504695555605082474073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342679188148280219930861 128504695555605082474073)
                      ·
                        rfl

theorem cell23_250262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_250262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250262 prefixEnd_250262 := by exact prefixLift 250262
  have htrace : WordTrace (prefixWord ++ tailWord_250262) baseStart_250262 baseEnd_250262 := by
    simpa [prefixWord, tailWord_250262, baseEnd_250262] using wordTrace_append hprefix tailTrace_250262
  have hstable : (prefixWord ++ tailWord_250262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250262).length < 2 ^ (prefixWord ++ tailWord_250262).sum := by decide
  have hdescent : baseEnd_250262 < baseStart_250262 := by decide
  rcases family_descends (prefixWord ++ tailWord_250262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250285 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_250285 : Nat := 118140960795 + 250285 * 2 ^ 59
def prefixEnd_250285 : Nat := 4983230072969 + 3 ^ 40 * 250285 * 2
def baseEnd_250285 : Nat := 128516505610658492486467

theorem tailTrace_250285 : CollatzResearch.WordTrace tailWord_250285 prefixEnd_250285 128516505610658492486467 := by
  unfold tailWord_250285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128643898267665119984309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6085762598845110079989539 9128643898267665119984309)
  ·
    refine ⟨855810365462593604998529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9128643898267665119984309 855810365462593604998529)
    ·
      refine ⟨641857774096945203748897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 855810365462593604998529 641857774096945203748897)
      ·
        refine ⟨481393330572708902811673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641857774096945203748897 481393330572708902811673)
        ·
          refine ⟨361044997929531677108755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481393330572708902811673 361044997929531677108755)
          ·
            refine ⟨541567496894297515663133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361044997929531677108755 541567496894297515663133)
            ·
              refine ⟨203087811335361568373675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541567496894297515663133 203087811335361568373675)
              ·
                refine ⟨304631717003042352560513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203087811335361568373675 304631717003042352560513)
                ·
                  refine ⟨228473787752281764420385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304631717003042352560513 228473787752281764420385)
                  ·
                    refine ⟨171355340814211323315289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228473787752281764420385 171355340814211323315289)
                    ·
                      refine ⟨128516505610658492486467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171355340814211323315289 128516505610658492486467)
                      ·
                        rfl

theorem cell23_250285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_250285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250285 prefixEnd_250285 := by exact prefixLift 250285
  have htrace : WordTrace (prefixWord ++ tailWord_250285) baseStart_250285 baseEnd_250285 := by
    simpa [prefixWord, tailWord_250285, baseEnd_250285] using wordTrace_append hprefix tailTrace_250285
  have hstable : (prefixWord ++ tailWord_250285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250285).length < 2 ^ (prefixWord ++ tailWord_250285).sum := by decide
  have hdescent : baseEnd_250285 < baseStart_250285 := by decide
  rcases family_descends (prefixWord ++ tailWord_250285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250290 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_250290 : Nat := 118140960795 + 250290 * 2 ^ 59
def prefixEnd_250290 : Nat := 4983230072969 + 3 ^ 40 * 250290 * 2
def baseEnd_250290 : Nat := 128519073013930972923943

theorem tailTrace_250290 : CollatzResearch.WordTrace tailWord_250290 prefixEnd_250290 128519073013930972923943 := by
  unfold tailWord_250290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282206565812387743479081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6085884175499700649277549 2282206565812387743479081)
  ·
    refine ⟨1711654924359290807609311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2282206565812387743479081 1711654924359290807609311)
    ·
      refine ⟨2567482386538936211413967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711654924359290807609311 2567482386538936211413967)
      ·
        refine ⟨3851223579808404317120951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567482386538936211413967 3851223579808404317120951)
        ·
          refine ⟨5776835369712606475681427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851223579808404317120951 5776835369712606475681427)
          ·
            refine ⟨8665253054568909713522141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776835369712606475681427 8665253054568909713522141)
            ·
              refine ⟨3249469895463341142570803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8665253054568909713522141 3249469895463341142570803)
              ·
                refine ⟨4874204843195011713856205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249469895463341142570803 4874204843195011713856205)
                ·
                  refine ⟨1827826816198129392696077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4874204843195011713856205 1827826816198129392696077)
                  ·
                    refine ⟨685435056074298522261029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827826816198129392696077 685435056074298522261029)
                    ·
                      refine ⟨128519073013930972923943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 685435056074298522261029 128519073013930972923943)
                      ·
                        rfl

theorem cell23_250290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_250290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250290 prefixEnd_250290 := by exact prefixLift 250290
  have htrace : WordTrace (prefixWord ++ tailWord_250290) baseStart_250290 baseEnd_250290 := by
    simpa [prefixWord, tailWord_250290, baseEnd_250290] using wordTrace_append hprefix tailTrace_250290
  have hstable : (prefixWord ++ tailWord_250290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250290).length < 2 ^ (prefixWord ++ tailWord_250290).sum := by decide
  have hdescent : baseEnd_250290 < baseStart_250290 := by decide
  rcases family_descends (prefixWord ++ tailWord_250290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250308 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 5]
def baseStart_250308 : Nat := 118140960795 + 250308 * 2 ^ 59
def prefixEnd_250308 : Nat := 4983230072969 + 3 ^ 40 * 250308 * 2
def baseEnd_250308 : Nat := 14280923962856878055429

theorem tailTrace_250308 : CollatzResearch.WordTrace tailWord_250308 prefixEnd_250308 14280923962856878055429 := by
  unfold tailWord_250308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564741388592170024035789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6086321851456226698714385 4564741388592170024035789)
  ·
    refine ⟨1711778020722063759013421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4564741388592170024035789 1711778020722063759013421)
    ·
      refine ⟨641916757770773909630033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1711778020722063759013421 641916757770773909630033)
      ·
        refine ⟨481437568328080432222525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641916757770773909630033 481437568328080432222525)
        ·
          refine ⟨180539088123030162083447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481437568328080432222525 180539088123030162083447)
          ·
            refine ⟨270808632184545243125171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180539088123030162083447 270808632184545243125171)
            ·
              refine ⟨406212948276817864687757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270808632184545243125171 406212948276817864687757)
              ·
                refine ⟨152329855603806699257909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406212948276817864687757 152329855603806699257909)
                ·
                  refine ⟨14280923962856878055429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152329855603806699257909 14280923962856878055429)
                  ·
                    rfl

theorem cell23_250308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_250308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250308 prefixEnd_250308 := by exact prefixLift 250308
  have htrace : WordTrace (prefixWord ++ tailWord_250308) baseStart_250308 baseEnd_250308 := by
    simpa [prefixWord, tailWord_250308, baseEnd_250308] using wordTrace_append hprefix tailTrace_250308
  have hstable : (prefixWord ++ tailWord_250308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250308).length < 2 ^ (prefixWord ++ tailWord_250308).sum := by decide
  have hdescent : baseEnd_250308 < baseStart_250308 := by decide
  rcases family_descends (prefixWord ++ tailWord_250308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250324 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_250324 : Nat := 118140960795 + 250324 * 2 ^ 59
def prefixEnd_250324 : Nat := 4983230072969 + 3 ^ 40 * 250324 * 2
def baseEnd_250324 : Nat := 128536531356183839898787

theorem tailTrace_250324 : CollatzResearch.WordTrace tailWord_250324 prefixEnd_250324 128536531356183839898787 := by
  unfold tailWord_250324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565033172563187390327013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6086710896750916520436017 4565033172563187390327013)
  ·
    refine ⟨855943719855597635686315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4565033172563187390327013 855943719855597635686315)
    ·
      refine ⟨1283915579783396453529473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855943719855597635686315 1283915579783396453529473)
      ·
        refine ⟨962936684837547340147105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1283915579783396453529473 962936684837547340147105)
        ·
          refine ⟨722202513628160505110329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962936684837547340147105 722202513628160505110329)
          ·
            refine ⟨541651885221120378832747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722202513628160505110329 541651885221120378832747)
            ·
              refine ⟨812477827831680568249121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541651885221120378832747 812477827831680568249121)
              ·
                refine ⟨609358370873760426186841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812477827831680568249121 609358370873760426186841)
                ·
                  refine ⟨457018778155320319640131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609358370873760426186841 457018778155320319640131)
                  ·
                    refine ⟨685528167232980479460197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 457018778155320319640131 685528167232980479460197)
                    ·
                      refine ⟨128536531356183839898787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 685528167232980479460197 128536531356183839898787)
                      ·
                        rfl

theorem cell23_250324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_250324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250324 prefixEnd_250324 := by exact prefixLift 250324
  have htrace : WordTrace (prefixWord ++ tailWord_250324) baseStart_250324 baseEnd_250324 := by
    simpa [prefixWord, tailWord_250324, baseEnd_250324] using wordTrace_append hprefix tailTrace_250324
  have hstable : (prefixWord ++ tailWord_250324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250324).length < 2 ^ (prefixWord ++ tailWord_250324).sum := by decide
  have hdescent : baseEnd_250324 < baseStart_250324 := by decide
  rcases family_descends (prefixWord ++ tailWord_250324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250330 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_250330 : Nat := 118140960795 + 250330 * 2 ^ 59
def prefixEnd_250330 : Nat := 4983230072969 + 3 ^ 40 * 250330 * 2
def baseEnd_250330 : Nat := 14282179137790090713751

theorem tailTrace_250330 : CollatzResearch.WordTrace tailWord_250330 prefixEnd_250330 14282179137790090713751 := by
  unfold tailWord_250330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282571295776159451343111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6086856788736425203581629 2282571295776159451343111)
  ·
    refine ⟨3423856943664239177014667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2282571295776159451343111 3423856943664239177014667)
    ·
      refine ⟨5135785415496358765522001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3423856943664239177014667 5135785415496358765522001)
      ·
        refine ⟨3851839061622269074141501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5135785415496358765522001 3851839061622269074141501)
        ·
          refine ⟨1444439648108350902803063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3851839061622269074141501 1444439648108350902803063)
          ·
            refine ⟨2166659472162526354204595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444439648108350902803063 2166659472162526354204595)
            ·
              refine ⟨3249989208243789531306893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166659472162526354204595 3249989208243789531306893)
              ·
                refine ⟨1218745953091421074240085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3249989208243789531306893 1218745953091421074240085)
                ·
                  refine ⟨14282179137790090713751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1218745953091421074240085 14282179137790090713751)
                  ·
                    rfl

theorem cell23_250330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_250330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250330 prefixEnd_250330 := by exact prefixLift 250330
  have htrace : WordTrace (prefixWord ++ tailWord_250330) baseStart_250330 baseEnd_250330 := by
    simpa [prefixWord, tailWord_250330, baseEnd_250330] using wordTrace_append hprefix tailTrace_250330
  have hstable : (prefixWord ++ tailWord_250330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250330).length < 2 ^ (prefixWord ++ tailWord_250330).sum := by decide
  have hdescent : baseEnd_250330 < baseStart_250330 := by decide
  rcases family_descends (prefixWord ++ tailWord_250330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250381 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 6]
def baseStart_250381 : Nat := 118140960795 + 250381 * 2 ^ 59
def prefixEnd_250381 : Nat := 4983230072969 + 3 ^ 40 * 250381 * 2
def baseEnd_250381 : Nat := 14285088861498901876225

theorem tailTrace_250381 : CollatzResearch.WordTrace tailWord_250381 prefixEnd_250381 14285088861498901876225 := by
  unfold tailWord_250381
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132145305919873515478997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6088096870613249010319331 9132145305919873515478997)
  ·
    refine ⟨214034655607497035519039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9132145305919873515478997 214034655607497035519039)
    ·
      refine ⟨321051983411245553278559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214034655607497035519039 321051983411245553278559)
      ·
        refine ⟨481577975116868329917839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321051983411245553278559 481577975116868329917839)
        ·
          refine ⟨722366962675302494876759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481577975116868329917839 722366962675302494876759)
          ·
            refine ⟨1083550444012953742315139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722366962675302494876759 1083550444012953742315139)
            ·
              refine ⟨1625325666019430613472709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083550444012953742315139 1625325666019430613472709)
              ·
                refine ⟨304748562378643240026133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1625325666019430613472709 304748562378643240026133)
                ·
                  refine ⟨14285088861498901876225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304748562378643240026133 14285088861498901876225)
                  ·
                    rfl

theorem cell23_250381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_250381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250381 prefixEnd_250381 := by exact prefixLift 250381
  have htrace : WordTrace (prefixWord ++ tailWord_250381) baseStart_250381 baseEnd_250381 := by
    simpa [prefixWord, tailWord_250381, baseEnd_250381] using wordTrace_append hprefix tailTrace_250381
  have hstable : (prefixWord ++ tailWord_250381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250381).length < 2 ^ (prefixWord ++ tailWord_250381).sum := by decide
  have hdescent : baseEnd_250381 < baseStart_250381 := by decide
  rcases family_descends (prefixWord ++ tailWord_250381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250447 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_250447 : Nat := 118140960795 + 250447 * 2 ^ 59
def prefixEnd_250447 : Nat := 4983230072969 + 3 ^ 40 * 250447 * 2
def baseEnd_250447 : Nat := 128599689476686858660721

theorem tailTrace_250447 : CollatzResearch.WordTrace tailWord_250447 prefixEnd_250447 128599689476686858660721 := by
  unfold tailWord_250447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134552523680766787381595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6089701682453844524921063 9134552523680766787381595)
  ·
    refine ⟨13701828785521150181072393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9134552523680766787381595 13701828785521150181072393)
    ·
      refine ⟨10276371589140862635804295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13701828785521150181072393 10276371589140862635804295)
      ·
        refine ⟨15414557383711293953706443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276371589140862635804295 15414557383711293953706443)
        ·
          refine ⟨23121836075566940930559665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15414557383711293953706443 23121836075566940930559665)
          ·
            refine ⟨17341377056675205697919749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23121836075566940930559665 17341377056675205697919749)
            ·
              refine ⟨3251508198126601068359953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17341377056675205697919749 3251508198126601068359953)
              ·
                refine ⟨2438631148594950801269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251508198126601068359953 2438631148594950801269965)
                ·
                  refine ⟨914486680723106550476237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438631148594950801269965 914486680723106550476237)
                  ·
                    refine ⟨342932505271164956428589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914486680723106550476237 342932505271164956428589)
                    ·
                      refine ⟨128599689476686858660721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342932505271164956428589 128599689476686858660721)
                      ·
                        rfl

theorem cell23_250447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_250447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250447 prefixEnd_250447 := by exact prefixLift 250447
  have htrace : WordTrace (prefixWord ++ tailWord_250447) baseStart_250447 baseEnd_250447 := by
    simpa [prefixWord, tailWord_250447, baseEnd_250447] using wordTrace_append hprefix tailTrace_250447
  have hstable : (prefixWord ++ tailWord_250447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250447).length < 2 ^ (prefixWord ++ tailWord_250447).sum := by decide
  have hdescent : baseEnd_250447 < baseStart_250447 := by decide
  rcases family_descends (prefixWord ++ tailWord_250447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250464 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_250464 : Nat := 118140960795 + 250464 * 2 ^ 59
def prefixEnd_250464 : Nat := 4983230072969 + 3 ^ 40 * 250464 * 2
def baseEnd_250464 : Nat := 128608418647813292148143

theorem tailTrace_250464 : CollatzResearch.WordTrace tailWord_250464 prefixEnd_250464 128608418647813292148143 := by
  unfold tailWord_250464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567586282309589345375223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6090115043079452460500297 4567586282309589345375223)
  ·
    refine ⟨6851379423464384018062835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567586282309589345375223 6851379423464384018062835)
    ·
      refine ⟨10277069135196576027094253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6851379423464384018062835 10277069135196576027094253)
      ·
        refine ⟨3853900925698716010160345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10277069135196576027094253 3853900925698716010160345)
        ·
          refine ⟨2890425694274037007620259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853900925698716010160345 2890425694274037007620259)
          ·
            refine ⟨4335638541411055511430389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890425694274037007620259 4335638541411055511430389)
            ·
              refine ⟨406466113257286454196599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4335638541411055511430389 406466113257286454196599)
              ·
                refine ⟨609699169885929681294899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406466113257286454196599 609699169885929681294899)
                ·
                  refine ⟨914548754828894521942349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609699169885929681294899 914548754828894521942349)
                  ·
                    refine ⟨342955783060835445728381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914548754828894521942349 342955783060835445728381)
                    ·
                      refine ⟨128608418647813292148143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 342955783060835445728381 128608418647813292148143)
                      ·
                        rfl

theorem cell23_250464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_250464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250464 prefixEnd_250464 := by exact prefixLift 250464
  have htrace : WordTrace (prefixWord ++ tailWord_250464) baseStart_250464 baseEnd_250464 := by
    simpa [prefixWord, tailWord_250464, baseEnd_250464] using wordTrace_append hprefix tailTrace_250464
  have hstable : (prefixWord ++ tailWord_250464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250464).length < 2 ^ (prefixWord ++ tailWord_250464).sum := by decide
  have hdescent : baseEnd_250464 < baseStart_250464 := by decide
  rcases family_descends (prefixWord ++ tailWord_250464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250482 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_250482 : Nat := 118140960795 + 250482 * 2 ^ 59
def prefixEnd_250482 : Nat := 4983230072969 + 3 ^ 40 * 250482 * 2
def baseEnd_250482 : Nat := 128617661299594221723061

theorem tailTrace_250482 : CollatzResearch.WordTrace tailWord_250482 prefixEnd_250482 128617661299594221723061 := by
  unfold tailWord_250482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283957269638491941226425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6090552719035978509937133 2283957269638491941226425)
  ·
    refine ⟨1712967952228868955919819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2283957269638491941226425 1712967952228868955919819)
    ·
      refine ⟨2569451928343303433879729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712967952228868955919819 2569451928343303433879729)
      ·
        refine ⟨1927088946257477575409797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2569451928343303433879729 1927088946257477575409797)
        ·
          refine ⟨361329177423277045389337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1927088946257477575409797 361329177423277045389337)
          ·
            refine ⟨270996883067457784042003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361329177423277045389337 270996883067457784042003)
            ·
              refine ⟨406495324601186676063005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270996883067457784042003 406495324601186676063005)
              ·
                refine ⟨152435746725445003523627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406495324601186676063005 152435746725445003523627)
                ·
                  refine ⟨228653620088167505285441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152435746725445003523627 228653620088167505285441)
                  ·
                    refine ⟨171490215066125628964081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228653620088167505285441 171490215066125628964081)
                    ·
                      refine ⟨128617661299594221723061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171490215066125628964081 128617661299594221723061)
                      ·
                        rfl

theorem cell23_250482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_250482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250482 prefixEnd_250482 := by exact prefixLift 250482
  have htrace : WordTrace (prefixWord ++ tailWord_250482) baseStart_250482 baseEnd_250482 := by
    simpa [prefixWord, tailWord_250482, baseEnd_250482] using wordTrace_append hprefix tailTrace_250482
  have hstable : (prefixWord ++ tailWord_250482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250482).length < 2 ^ (prefixWord ++ tailWord_250482).sum := by decide
  have hdescent : baseEnd_250482 < baseStart_250482 := by decide
  rcases family_descends (prefixWord ++ tailWord_250482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250524 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_250524 : Nat := 118140960795 + 250524 * 2 ^ 59
def prefixEnd_250524 : Nat := 4983230072969 + 3 ^ 40 * 250524 * 2
def baseEnd_250524 : Nat := 128639227487083057397867

theorem tailTrace_250524 : CollatzResearch.WordTrace tailWord_250524 prefixEnd_250524 128639227487083057397867 := by
  unfold tailWord_250524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568680472200904468967313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6091573962934539291956417 4568680472200904468967313)
  ·
    refine ⟨3426510354150678351725485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4568680472200904468967313 3426510354150678351725485)
    ·
      refine ⟨1284941382806504381897057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3426510354150678351725485 1284941382806504381897057)
      ·
        refine ⟨963706037104878286422793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1284941382806504381897057 963706037104878286422793)
        ·
          refine ⟨722779527828658714817095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963706037104878286422793 722779527828658714817095)
          ·
            refine ⟨1084169291742988072225643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722779527828658714817095 1084169291742988072225643)
            ·
              refine ⟨1626253937614482108338465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084169291742988072225643 1626253937614482108338465)
              ·
                refine ⟨1219690453210861581253849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626253937614482108338465 1219690453210861581253849)
                ·
                  refine ⟨914767839908146185940387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219690453210861581253849 914767839908146185940387)
                  ·
                    refine ⟨1372151759862219278910581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914767839908146185940387 1372151759862219278910581)
                    ·
                      refine ⟨128639227487083057397867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1372151759862219278910581 128639227487083057397867)
                      ·
                        rfl

theorem cell23_250524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_250524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250524 prefixEnd_250524 := by exact prefixLift 250524
  have htrace : WordTrace (prefixWord ++ tailWord_250524) baseStart_250524 baseEnd_250524 := by
    simpa [prefixWord, tailWord_250524, baseEnd_250524] using wordTrace_append hprefix tailTrace_250524
  have hstable : (prefixWord ++ tailWord_250524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250524).length < 2 ^ (prefixWord ++ tailWord_250524).sum := by decide
  have hdescent : baseEnd_250524 < baseStart_250524 := by decide
  rcases family_descends (prefixWord ++ tailWord_250524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250542 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_250542 : Nat := 118140960795 + 250542 * 2 ^ 59
def prefixEnd_250542 : Nat := 4983230072969 + 3 ^ 40 * 250542 * 2
def baseEnd_250542 : Nat := 128648470138863986972785

theorem tailTrace_250542 : CollatzResearch.WordTrace tailWord_250542 prefixEnd_250542 128648470138863986972785 := by
  unfold tailWord_250542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142252182292074751511235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6092011638891065341393253 1142252182292074751511235)
  ·
    refine ⟨1713378273438112127266853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142252182292074751511235 1713378273438112127266853)
    ·
      refine ⟨321258426269646023862535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1713378273438112127266853 321258426269646023862535)
      ·
        refine ⟨481887639404469035793803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321258426269646023862535 481887639404469035793803)
        ·
          refine ⟨722831459106703553690705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481887639404469035793803 722831459106703553690705)
          ·
            refine ⟨542123594330027665268029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722831459106703553690705 542123594330027665268029)
            ·
              refine ⟨203296347873760374475511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542123594330027665268029 203296347873760374475511)
              ·
                refine ⟨304944521810640561713267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203296347873760374475511 304944521810640561713267)
                ·
                  refine ⟨457416782715960842569901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304944521810640561713267 457416782715960842569901)
                  ·
                    refine ⟨171531293518485315963713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457416782715960842569901 171531293518485315963713)
                    ·
                      refine ⟨128648470138863986972785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171531293518485315963713 128648470138863986972785)
                      ·
                        rfl

theorem cell23_250542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_250542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250542 prefixEnd_250542 := by exact prefixLift 250542
  have htrace : WordTrace (prefixWord ++ tailWord_250542) baseStart_250542 baseEnd_250542 := by
    simpa [prefixWord, tailWord_250542, baseEnd_250542] using wordTrace_append hprefix tailTrace_250542
  have hstable : (prefixWord ++ tailWord_250542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250542).length < 2 ^ (prefixWord ++ tailWord_250542).sum := by decide
  have hdescent : baseEnd_250542 < baseStart_250542 := by decide
  rcases family_descends (prefixWord ++ tailWord_250542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250544 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 5]
def baseStart_250544 : Nat := 118140960795 + 250544 * 2 ^ 59
def prefixEnd_250544 : Nat := 4983230072969 + 3 ^ 40 * 250544 * 2
def baseEnd_250544 : Nat := 14294388566685886571975

theorem tailTrace_250544 : CollatzResearch.WordTrace tailWord_250544 prefixEnd_250544 14294388566685886571975 := by
  unfold tailWord_250544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569045202164676176831343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6092060269552901569108457 4569045202164676176831343)
  ·
    refine ⟨6853567803247014265247015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4569045202164676176831343 6853567803247014265247015)
    ·
      refine ⟨10280351704870521397870523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853567803247014265247015 10280351704870521397870523)
      ·
        refine ⟨15420527557305782096805785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280351704870521397870523 15420527557305782096805785)
        ·
          refine ⟨11565395667979336572604339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15420527557305782096805785 11565395667979336572604339)
          ·
            refine ⟨17348093501969004858906509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565395667979336572604339 17348093501969004858906509)
            ·
              refine ⟨6505535063238376822089941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17348093501969004858906509 6505535063238376822089941)
              ·
                refine ⟨152473478044649456767733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6505535063238376822089941 152473478044649456767733)
                ·
                  refine ⟨14294388566685886571975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152473478044649456767733 14294388566685886571975)
                  ·
                    rfl

theorem cell23_250544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 5].length) (baseStart_250544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250544 prefixEnd_250544 := by exact prefixLift 250544
  have htrace : WordTrace (prefixWord ++ tailWord_250544) baseStart_250544 baseEnd_250544 := by
    simpa [prefixWord, tailWord_250544, baseEnd_250544] using wordTrace_append hprefix tailTrace_250544
  have hstable : (prefixWord ++ tailWord_250544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250544).length < 2 ^ (prefixWord ++ tailWord_250544).sum := by decide
  have hdescent : baseEnd_250544 < baseStart_250544 := by decide
  rcases family_descends (prefixWord ++ tailWord_250544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250554 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_250554 : Nat := 118140960795 + 250554 * 2 ^ 59
def prefixEnd_250554 : Nat := 4983230072969 + 3 ^ 40 * 250554 * 2
def baseEnd_250554 : Nat := 128654631906717940022729

theorem tailTrace_250554 : CollatzResearch.WordTrace tailWord_250554 prefixEnd_250554 128654631906717940022729 := by
  unfold tailWord_250554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284613783573281015381679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6092303422862082707684477 2284613783573281015381679)
  ·
    refine ⟨3426920675359921523072519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284613783573281015381679 3426920675359921523072519)
    ·
      refine ⟨5140381013039882284608779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426920675359921523072519 5140381013039882284608779)
      ·
        refine ⟨7710571519559823426913169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140381013039882284608779 7710571519559823426913169)
        ·
          refine ⟨5782928639669867570184877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710571519559823426913169 5782928639669867570184877)
          ·
            refine ⟨2168598239876200338819329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5782928639669867570184877 2168598239876200338819329)
            ·
              refine ⟨1626448679907150254114497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168598239876200338819329 1626448679907150254114497)
              ·
                refine ⟨1219836509930362690585873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626448679907150254114497 1219836509930362690585873)
                ·
                  refine ⟨914877382447772017939405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219836509930362690585873 914877382447772017939405)
                  ·
                    refine ⟨343079018417914506727277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914877382447772017939405 343079018417914506727277)
                    ·
                      refine ⟨128654631906717940022729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343079018417914506727277 128654631906717940022729)
                      ·
                        rfl

theorem cell23_250554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_250554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250554 prefixEnd_250554 := by exact prefixLift 250554
  have htrace : WordTrace (prefixWord ++ tailWord_250554) baseStart_250554 baseEnd_250554 := by
    simpa [prefixWord, tailWord_250554, baseEnd_250554] using wordTrace_append hprefix tailTrace_250554
  have hstable : (prefixWord ++ tailWord_250554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250554).length < 2 ^ (prefixWord ++ tailWord_250554).sum := by decide
  have hdescent : baseEnd_250554 < baseStart_250554 := by decide
  rcases family_descends (prefixWord ++ tailWord_250554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250567 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_250567 : Nat := 118140960795 + 250567 * 2 ^ 59
def prefixEnd_250567 : Nat := 4983230072969 + 3 ^ 40 * 250567 * 2
def baseEnd_250567 : Nat := 128661307155226389160169

theorem tailTrace_250567 : CollatzResearch.WordTrace tailWord_250567 prefixEnd_250567 128661307155226389160169 := by
  unfold tailWord_250567
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138929283246027281749955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6092619522164018187833303 9138929283246027281749955)
  ·
    refine ⟨13708393924869040922624933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138929283246027281749955 13708393924869040922624933)
    ·
      refine ⟨2570323860912945172992175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13708393924869040922624933 2570323860912945172992175)
      ·
        refine ⟨3855485791369417759488263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570323860912945172992175 3855485791369417759488263)
        ·
          refine ⟨5783228687054126639232395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855485791369417759488263 5783228687054126639232395)
          ·
            refine ⟨8674843030581189958848593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783228687054126639232395 8674843030581189958848593)
            ·
              refine ⟨6506132272935892469136445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674843030581189958848593 6506132272935892469136445)
              ·
                refine ⟨2439799602350959675926167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6506132272935892469136445 2439799602350959675926167)
                ·
                  refine ⟨3659699403526439513889251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439799602350959675926167 3659699403526439513889251)
                  ·
                    refine ⟨5489549105289659270833877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659699403526439513889251 5489549105289659270833877)
                    ·
                      refine ⟨128661307155226389160169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5489549105289659270833877 128661307155226389160169)
                      ·
                        rfl

theorem cell23_250567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_250567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250567 prefixEnd_250567 := by exact prefixLift 250567
  have htrace : WordTrace (prefixWord ++ tailWord_250567) baseStart_250567 baseEnd_250567 := by
    simpa [prefixWord, tailWord_250567, baseEnd_250567] using wordTrace_append hprefix tailTrace_250567
  have hstable : (prefixWord ++ tailWord_250567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250567).length < 2 ^ (prefixWord ++ tailWord_250567).sum := by decide
  have hdescent : baseEnd_250567 < baseStart_250567 := by decide
  rcases family_descends (prefixWord ++ tailWord_250567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250591 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 2, 5]
def baseStart_250591 : Nat := 118140960795 + 250591 * 2 ^ 59
def prefixEnd_250591 : Nat := 4983230072969 + 3 ^ 40 * 250591 * 2
def baseEnd_250591 : Nat := 42891210230311431753353

theorem tailTrace_250591 : CollatzResearch.WordTrace tailWord_250591 prefixEnd_250591 42891210230311431753353 := by
  unfold tailWord_250591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139804635159079380623627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6093203090106052920415751 9139804635159079380623627)
  ·
    refine ⟨13709706952738619070935441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9139804635159079380623627 13709706952738619070935441)
    ·
      refine ⟨10282280214553964303201581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13709706952738619070935441 10282280214553964303201581)
      ·
        refine ⟨3855855080457736613700593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10282280214553964303201581 3855855080457736613700593)
        ·
          refine ⟨2891891310343302460275445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3855855080457736613700593 2891891310343302460275445)
          ·
            refine ⟨271114810344684605650823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2891891310343302460275445 271114810344684605650823)
            ·
              refine ⟨406672215517026908476235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271114810344684605650823 406672215517026908476235)
              ·
                refine ⟨610008323275540362714353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406672215517026908476235 610008323275540362714353)
                ·
                  refine ⟨457506242456655272035765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610008323275540362714353 457506242456655272035765)
                  ·
                    refine ⟨42891210230311431753353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 457506242456655272035765 42891210230311431753353)
                    ·
                      rfl

theorem cell23_250591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_250591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250591 prefixEnd_250591 := by exact prefixLift 250591
  have htrace : WordTrace (prefixWord ++ tailWord_250591) baseStart_250591 baseEnd_250591 := by
    simpa [prefixWord, tailWord_250591, baseEnd_250591] using wordTrace_append hprefix tailTrace_250591
  have hstable : (prefixWord ++ tailWord_250591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250591).length < 2 ^ (prefixWord ++ tailWord_250591).sum := by decide
  have hdescent : baseEnd_250591 < baseStart_250591 := by decide
  rcases family_descends (prefixWord ++ tailWord_250591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250604 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_250604 : Nat := 118140960795 + 250604 * 2 ^ 59
def prefixEnd_250604 : Nat := 4983230072969 + 3 ^ 40 * 250604 * 2
def baseEnd_250604 : Nat := 42893435313147581465833

theorem tailTrace_250604 : CollatzResearch.WordTrace tailWord_250604 prefixEnd_250604 42893435313147581465833 := by
  unfold tailWord_250604
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570139392055991300423433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6093519189407988400564577 4570139392055991300423433)
  ·
    refine ⟨3427604544041993475317575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4570139392055991300423433 3427604544041993475317575)
    ·
      refine ⟨5141406816062990212976363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427604544041993475317575 5141406816062990212976363)
      ·
        refine ⟨7712110224094485319464545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141406816062990212976363 7712110224094485319464545)
        ·
          refine ⟨5784082668070863989598409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7712110224094485319464545 5784082668070863989598409)
          ·
            refine ⟨4338062001053147992198807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784082668070863989598409 4338062001053147992198807)
            ·
              refine ⟨6507093001579721988298211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338062001053147992198807 6507093001579721988298211)
              ·
                refine ⟨9760639502369582982447317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507093001579721988298211 9760639502369582982447317)
                ·
                  refine ⟨228764988336787101151109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9760639502369582982447317 228764988336787101151109)
                  ·
                    refine ⟨42893435313147581465833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228764988336787101151109 42893435313147581465833)
                    ·
                      rfl

theorem cell23_250604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_250604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250604 prefixEnd_250604 := by exact prefixLift 250604
  have htrace : WordTrace (prefixWord ++ tailWord_250604) baseStart_250604 baseEnd_250604 := by
    simpa [prefixWord, tailWord_250604, baseEnd_250604] using wordTrace_append hprefix tailTrace_250604
  have hstable : (prefixWord ++ tailWord_250604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250604).length < 2 ^ (prefixWord ++ tailWord_250604).sum := by decide
  have hdescent : baseEnd_250604 < baseStart_250604 := by decide
  rcases family_descends (prefixWord ++ tailWord_250604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250621 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_250621 : Nat := 118140960795 + 250621 * 2 ^ 59
def prefixEnd_250621 : Nat := 4983230072969 + 3 ^ 40 * 250621 * 2
def baseEnd_250621 : Nat := 42896345036856392628307

theorem tailTrace_250621 : CollatzResearch.WordTrace tailWord_250621 prefixEnd_250621 42896345036856392628307 := by
  unfold tailWord_250621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140898825050394504215717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6093932550033596336143811 9140898825050394504215717)
  ·
    refine ⟨1713918529696948969540447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9140898825050394504215717 1713918529696948969540447)
    ·
      refine ⟨2570877794545423454310671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713918529696948969540447 2570877794545423454310671)
      ·
        refine ⟨3856316691818135181466007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570877794545423454310671 3856316691818135181466007)
        ·
          refine ⟨5784475037727202772199011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856316691818135181466007 5784475037727202772199011)
          ·
            refine ⟨8676712556590804158298517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784475037727202772199011 8676712556590804158298517)
            ·
              refine ⟨406720901090193944920243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8676712556590804158298517 406720901090193944920243)
              ·
                refine ⟨610081351635290917380365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406720901090193944920243 610081351635290917380365)
                ·
                  refine ⟨228780506863234094017637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610081351635290917380365 228780506863234094017637)
                  ·
                    refine ⟨42896345036856392628307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228780506863234094017637 42896345036856392628307)
                    ·
                      rfl

theorem cell23_250621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_250621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250621 prefixEnd_250621 := by exact prefixLift 250621
  have htrace : WordTrace (prefixWord ++ tailWord_250621) baseStart_250621 baseEnd_250621 := by
    simpa [prefixWord, tailWord_250621, baseEnd_250621] using wordTrace_append hprefix tailTrace_250621
  have hstable : (prefixWord ++ tailWord_250621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250621).length < 2 ^ (prefixWord ++ tailWord_250621).sum := by decide
  have hdescent : baseEnd_250621 < baseStart_250621 := by decide
  rcases family_descends (prefixWord ++ tailWord_250621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250631 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_250631 : Nat := 118140960795 + 250631 * 2 ^ 59
def prefixEnd_250631 : Nat := 4983230072969 + 3 ^ 40 * 250631 * 2
def baseEnd_250631 : Nat := 128694169917114138759875

theorem tailTrace_250631 : CollatzResearch.WordTrace tailWord_250631 prefixEnd_250631 128694169917114138759875 := by
  unfold tailWord_250631
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141263555014166212079747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6094175703342777474719831 9141263555014166212079747)
  ·
    refine ⟨13711895332521249318119621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141263555014166212079747 13711895332521249318119621)
    ·
      refine ⟨2570980374847734247147429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13711895332521249318119621 2570980374847734247147429)
      ·
        refine ⟨482058820283950171340143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2570980374847734247147429 482058820283950171340143)
        ·
          refine ⟨723088230425925257010215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482058820283950171340143 723088230425925257010215)
          ·
            refine ⟨1084632345638887885515323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723088230425925257010215 1084632345638887885515323)
            ·
              refine ⟨1626948518458331828272985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084632345638887885515323 1626948518458331828272985)
              ·
                refine ⟨1220211388843748871204739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626948518458331828272985 1220211388843748871204739)
                ·
                  refine ⟨1830317083265623306807109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220211388843748871204739 1830317083265623306807109)
                  ·
                    refine ⟨343184453112304370026333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830317083265623306807109 343184453112304370026333)
                    ·
                      refine ⟨128694169917114138759875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343184453112304370026333 128694169917114138759875)
                      ·
                        rfl

theorem cell23_250631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_250631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250631 prefixEnd_250631 := by exact prefixLift 250631
  have htrace : WordTrace (prefixWord ++ tailWord_250631) baseStart_250631 baseEnd_250631 := by
    simpa [prefixWord, tailWord_250631, baseEnd_250631] using wordTrace_append hprefix tailTrace_250631
  have hstable : (prefixWord ++ tailWord_250631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250631).length < 2 ^ (prefixWord ++ tailWord_250631).sum := by decide
  have hdescent : baseEnd_250631 < baseStart_250631 := by decide
  rcases family_descends (prefixWord ++ tailWord_250631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250655 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 1, 4]
def baseStart_250655 : Nat := 118140960795 + 250655 * 2 ^ 59
def prefixEnd_250655 : Nat := 4983230072969 + 3 ^ 40 * 250655 * 2
def baseEnd_250655 : Nat := 42902164484274014953255

theorem tailTrace_250655 : CollatzResearch.WordTrace tailWord_250655 prefixEnd_250655 42902164484274014953255 := by
  unfold tailWord_250655
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142138906927218310953419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6094759271284812207302279 9142138906927218310953419)
  ·
    refine ⟨13713208360390827466430129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9142138906927218310953419 13713208360390827466430129)
    ·
      refine ⟨10284906270293120599822597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13713208360390827466430129 10284906270293120599822597)
      ·
        refine ⟨1928419925679960112466737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10284906270293120599822597 1928419925679960112466737)
        ·
          refine ⟨1446314944259970084350053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928419925679960112466737 1446314944259970084350053)
          ·
            refine ⟨271184052048744390815635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1446314944259970084350053 271184052048744390815635)
            ·
              refine ⟨406776078073116586223453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271184052048744390815635 406776078073116586223453)
              ·
                refine ⟨152541029277418719833795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406776078073116586223453 152541029277418719833795)
                ·
                  refine ⟨228811543916128079750693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152541029277418719833795 228811543916128079750693)
                  ·
                    refine ⟨42902164484274014953255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228811543916128079750693 42902164484274014953255)
                    ·
                      rfl

theorem cell23_250655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 4].length) (baseStart_250655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250655 prefixEnd_250655 := by exact prefixLift 250655
  have htrace : WordTrace (prefixWord ++ tailWord_250655) baseStart_250655 baseEnd_250655 := by
    simpa [prefixWord, tailWord_250655, baseEnd_250655] using wordTrace_append hprefix tailTrace_250655
  have hstable : (prefixWord ++ tailWord_250655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250655).length < 2 ^ (prefixWord ++ tailWord_250655).sum := by decide
  have hdescent : baseEnd_250655 < baseStart_250655 := by decide
  rcases family_descends (prefixWord ++ tailWord_250655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250684 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_250684 : Nat := 118140960795 + 250684 * 2 ^ 59
def prefixEnd_250684 : Nat := 4983230072969 + 3 ^ 40 * 250684 * 2
def baseEnd_250684 : Nat := 128721384391802431397131

theorem tailTrace_250684 : CollatzResearch.WordTrace tailWord_250684 prefixEnd_250684 128721384391802431397131 := by
  unfold tailWord_250684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571598311911078131879553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6095464415881437509172737 4571598311911078131879553)
  ·
    refine ⟨3428698733933308598909665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4571598311911078131879553 3428698733933308598909665)
    ·
      refine ⟨2571524050449981449182249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3428698733933308598909665 2571524050449981449182249)
      ·
        refine ⟨1928643037837486086886687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2571524050449981449182249 1928643037837486086886687)
        ·
          refine ⟨2892964556756229130330031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928643037837486086886687 2892964556756229130330031)
          ·
            refine ⟨4339446835134343695495047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892964556756229130330031 4339446835134343695495047)
            ·
              refine ⟨6509170252701515543242571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339446835134343695495047 6509170252701515543242571)
              ·
                refine ⟨9763755379052273314863857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509170252701515543242571 9763755379052273314863857)
                ·
                  refine ⟨7322816534289204986147893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9763755379052273314863857 7322816534289204986147893)
                  ·
                    refine ⟨686514050089612967451365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7322816534289204986147893 686514050089612967451365)
                    ·
                      refine ⟨128721384391802431397131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 686514050089612967451365 128721384391802431397131)
                      ·
                        rfl

theorem cell23_250684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_250684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250684 prefixEnd_250684 := by exact prefixLift 250684
  have htrace : WordTrace (prefixWord ++ tailWord_250684) baseStart_250684 baseEnd_250684 := by
    simpa [prefixWord, tailWord_250684, baseEnd_250684] using wordTrace_append hprefix tailTrace_250684
  have hstable : (prefixWord ++ tailWord_250684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250684).length < 2 ^ (prefixWord ++ tailWord_250684).sum := by decide
  have hdescent : baseEnd_250684 < baseStart_250684 := by decide
  rcases family_descends (prefixWord ++ tailWord_250684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250685 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 6]
def baseStart_250685 : Nat := 118140960795 + 250685 * 2 ^ 59
def prefixEnd_250685 : Nat := 4983230072969 + 3 ^ 40 * 250685 * 2
def baseEnd_250685 : Nat := 14302433096939658609403

theorem tailTrace_250685 : CollatzResearch.WordTrace tailWord_250685 prefixEnd_250685 14302433096939658609403 := by
  unfold tailWord_250685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143233096818533434545509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095488731212355623030339 9143233096818533434545509)
  ·
    refine ⟨1714356205653475018977283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9143233096818533434545509 1714356205653475018977283)
    ·
      refine ⟨2571534308480212528465925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714356205653475018977283 2571534308480212528465925)
      ·
        refine ⟨482162682840039849087361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2571534308480212528465925 482162682840039849087361)
        ·
          refine ⟨361622012130029886815521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482162682840039849087361 361622012130029886815521)
          ·
            refine ⟨271216509097522415111641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361622012130029886815521 271216509097522415111641)
            ·
              refine ⟨203412381823141811333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271216509097522415111641 203412381823141811333731)
              ·
                refine ⟨305118572734712717000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203412381823141811333731 305118572734712717000597)
                ·
                  refine ⟨14302433096939658609403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 305118572734712717000597 14302433096939658609403)
                  ·
                    rfl

theorem cell23_250685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_250685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250685 prefixEnd_250685 := by exact prefixLift 250685
  have htrace : WordTrace (prefixWord ++ tailWord_250685) baseStart_250685 baseEnd_250685 := by
    simpa [prefixWord, tailWord_250685, baseEnd_250685] using wordTrace_append hprefix tailTrace_250685
  have hstable : (prefixWord ++ tailWord_250685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250685).length < 2 ^ (prefixWord ++ tailWord_250685).sum := by decide
  have hdescent : baseEnd_250685 < baseStart_250685 := by decide
  rcases family_descends (prefixWord ++ tailWord_250685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250704 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_250704 : Nat := 118140960795 + 250704 * 2 ^ 59
def prefixEnd_250704 : Nat := 4983230072969 + 3 ^ 40 * 250704 * 2
def baseEnd_250704 : Nat := 128731654004892353147039

theorem tailTrace_250704 : CollatzResearch.WordTrace tailWord_250704 prefixEnd_250704 128731654004892353147039 := by
  unfold tailWord_250704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571963041874849839743583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6095950722499799786324777 4571963041874849839743583)
  ·
    refine ⟨6857944562812274759615375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571963041874849839743583 6857944562812274759615375)
    ·
      refine ⟨10286916844218412139423063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857944562812274759615375 10286916844218412139423063)
      ·
        refine ⟨15430375266327618209134595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10286916844218412139423063 15430375266327618209134595)
        ·
          refine ⟨23145562899491427313701893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15430375266327618209134595 23145562899491427313701893)
          ·
            refine ⟨4339793043654642621319105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23145562899491427313701893 4339793043654642621319105)
            ·
              refine ⟨3254844782740981965989329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4339793043654642621319105 3254844782740981965989329)
              ·
                refine ⟨2441133587055736474491997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254844782740981965989329 2441133587055736474491997)
                ·
                  refine ⟨915425095145901177934499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2441133587055736474491997 915425095145901177934499)
                  ·
                    refine ⟨1373137642718851766901749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915425095145901177934499 1373137642718851766901749)
                    ·
                      refine ⟨128731654004892353147039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1373137642718851766901749 128731654004892353147039)
                      ·
                        rfl

theorem cell23_250704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_250704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250704 prefixEnd_250704 := by exact prefixLift 250704
  have htrace : WordTrace (prefixWord ++ tailWord_250704) baseStart_250704 baseEnd_250704 := by
    simpa [prefixWord, tailWord_250704, baseEnd_250704] using wordTrace_append hprefix tailTrace_250704
  have hstable : (prefixWord ++ tailWord_250704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250704).length < 2 ^ (prefixWord ++ tailWord_250704).sum := by decide
  have hdescent : baseEnd_250704 < baseStart_250704 := by decide
  rcases family_descends (prefixWord ++ tailWord_250704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250705 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_250705 : Nat := 118140960795 + 250705 * 2 ^ 59
def prefixEnd_250705 : Nat := 4983230072969 + 3 ^ 40 * 250705 * 2
def baseEnd_250705 : Nat := 128732167485546849234535

theorem tailTrace_250705 : CollatzResearch.WordTrace tailWord_250705 prefixEnd_250705 128732167485546849234535 := by
  unfold tailWord_250705
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143962556746076850273569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095975037830717900182379 9143962556746076850273569)
  ·
    refine ⟨6857971917559557637705177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9143962556746076850273569 6857971917559557637705177)
    ·
      refine ⟨5143478938169668228278883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857971917559557637705177 5143478938169668228278883)
      ·
        refine ⟨7715218407254502342418325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143478938169668228278883 7715218407254502342418325)
        ·
          refine ⟨361650862840054797300859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7715218407254502342418325 361650862840054797300859)
          ·
            refine ⟨542476294260082195951289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361650862840054797300859 542476294260082195951289)
            ·
              refine ⟨406857220695061646963467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542476294260082195951289 406857220695061646963467)
              ·
                refine ⟨610285831042592470445201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406857220695061646963467 610285831042592470445201)
                ·
                  refine ⟨457714373281944352833901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610285831042592470445201 457714373281944352833901)
                  ·
                    refine ⟨171642889980729132312713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457714373281944352833901 171642889980729132312713)
                    ·
                      refine ⟨128732167485546849234535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171642889980729132312713 128732167485546849234535)
                      ·
                        rfl

theorem cell23_250705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_250705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250705 prefixEnd_250705 := by exact prefixLift 250705
  have htrace : WordTrace (prefixWord ++ tailWord_250705) baseStart_250705 baseEnd_250705 := by
    simpa [prefixWord, tailWord_250705, baseEnd_250705] using wordTrace_append hprefix tailTrace_250705
  have hstable : (prefixWord ++ tailWord_250705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250705).length < 2 ^ (prefixWord ++ tailWord_250705).sum := by decide
  have hdescent : baseEnd_250705 < baseStart_250705 := by decide
  rcases family_descends (prefixWord ++ tailWord_250705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250711 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 1, 6]
def baseStart_250711 : Nat := 118140960795 + 250711 * 2 ^ 59
def prefixEnd_250711 : Nat := 4983230072969 + 3 ^ 40 * 250711 * 2
def baseEnd_250711 : Nat := 42911749456491275253169

theorem tailTrace_250711 : CollatzResearch.WordTrace tailWord_250711 prefixEnd_250711 42911749456491275253169 := by
  unfold tailWord_250711
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144181394724339874991987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6096120929816226583327991 9144181394724339874991987)
  ·
    refine ⟨13716272092086509812487981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144181394724339874991987 13716272092086509812487981)
    ·
      refine ⟨5143602034532441179682993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13716272092086509812487981 5143602034532441179682993)
      ·
        refine ⟨3857701525899330884762245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5143602034532441179682993 3857701525899330884762245)
        ·
          refine ⟨723319036106124540892921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3857701525899330884762245 723319036106124540892921)
          ·
            refine ⟨542489277079593405669691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723319036106124540892921 542489277079593405669691)
            ·
              refine ⟨813733915619390108504537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542489277079593405669691 813733915619390108504537)
              ·
                refine ⟨610300436714542581378403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813733915619390108504537 610300436714542581378403)
                ·
                  refine ⟨915450655071813872067605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610300436714542581378403 915450655071813872067605)
                  ·
                    refine ⟨42911749456491275253169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 915450655071813872067605 42911749456491275253169)
                    ·
                      rfl

theorem cell23_250711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_250711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250711 prefixEnd_250711 := by exact prefixLift 250711
  have htrace : WordTrace (prefixWord ++ tailWord_250711) baseStart_250711 baseEnd_250711 := by
    simpa [prefixWord, tailWord_250711, baseEnd_250711] using wordTrace_append hprefix tailTrace_250711
  have hstable : (prefixWord ++ tailWord_250711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250711).length < 2 ^ (prefixWord ++ tailWord_250711).sum := by decide
  have hdescent : baseEnd_250711 < baseStart_250711 := by decide
  rcases family_descends (prefixWord ++ tailWord_250711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250724 : List Nat := [2, 3, 1, 1, 4, 12]
def baseStart_250724 : Nat := 118140960795 + 250724 * 2 ^ 59
def prefixEnd_250724 : Nat := 4983230072969 + 3 ^ 40 * 250724 * 2
def baseEnd_250724 : Nat := 529802154806511419329

theorem tailTrace_250724 : CollatzResearch.WordTrace tailWord_250724 prefixEnd_250724 529802154806511419329 := by
  unfold tailWord_250724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572327771838621547607613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6096437029118162063476817 4572327771838621547607613)
  ·
    refine ⟨1714622914439483080352855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4572327771838621547607613 1714622914439483080352855)
    ·
      refine ⟨2571934371659224620529283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714622914439483080352855 2571934371659224620529283)
      ·
        refine ⟨3857901557488836930793925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571934371659224620529283 3857901557488836930793925)
        ·
          refine ⟨723356542029156924523861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3857901557488836930793925 723356542029156924523861)
          ·
            refine ⟨529802154806511419329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 723356542029156924523861 529802154806511419329)
            ·
              rfl

theorem cell23_250724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 12].length) (baseStart_250724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250724 prefixEnd_250724 := by exact prefixLift 250724
  have htrace : WordTrace (prefixWord ++ tailWord_250724) baseStart_250724 baseEnd_250724 := by
    simpa [prefixWord, tailWord_250724, baseEnd_250724] using wordTrace_append hprefix tailTrace_250724
  have hstable : (prefixWord ++ tailWord_250724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250724).length < 2 ^ (prefixWord ++ tailWord_250724).sum := by decide
  have hdescent : baseEnd_250724 < baseStart_250724 := by decide
  rcases family_descends (prefixWord ++ tailWord_250724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250728 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_250728 : Nat := 118140960795 + 250728 * 2 ^ 59
def prefixEnd_250728 : Nat := 4983230072969 + 3 ^ 40 * 250728 * 2
def baseEnd_250728 : Nat := 42914659180200086415643

theorem tailTrace_250728 : CollatzResearch.WordTrace tailWord_250728 prefixEnd_250728 42914659180200086415643 := by
  unfold tailWord_250728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572400717831375889180419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6096534290441834518907225 4572400717831375889180419)
  ·
    refine ⟨6858601076747063833770629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572400717831375889180419 6858601076747063833770629)
    ·
      refine ⟨1285987701890074468831993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6858601076747063833770629 1285987701890074468831993)
      ·
        refine ⟨964490776417555851623995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285987701890074468831993 964490776417555851623995)
        ·
          refine ⟨1446736164626333777435993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964490776417555851623995 1446736164626333777435993)
          ·
            refine ⟨1085052123469750333076995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446736164626333777435993 1085052123469750333076995)
            ·
              refine ⟨1627578185204625499615493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085052123469750333076995 1627578185204625499615493)
              ·
                refine ⟨305170909725867281177905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1627578185204625499615493 305170909725867281177905)
                ·
                  refine ⟨228878182294400460883429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305170909725867281177905 228878182294400460883429)
                  ·
                    refine ⟨42914659180200086415643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228878182294400460883429 42914659180200086415643)
                    ·
                      rfl

theorem cell23_250728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_250728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250728 prefixEnd_250728 := by exact prefixLift 250728
  have htrace : WordTrace (prefixWord ++ tailWord_250728) baseStart_250728 baseEnd_250728 := by
    simpa [prefixWord, tailWord_250728, baseEnd_250728] using wordTrace_append hprefix tailTrace_250728
  have hstable : (prefixWord ++ tailWord_250728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250728).length < 2 ^ (prefixWord ++ tailWord_250728).sum := by decide
  have hdescent : baseEnd_250728 < baseStart_250728 := by decide
  rcases family_descends (prefixWord ++ tailWord_250728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250741 : List Nat := [1, 3, 4, 1, 1, 2, 3, 8]
def baseStart_250741 : Nat := 118140960795 + 250741 * 2 ^ 59
def prefixEnd_250741 : Nat := 4983230072969 + 3 ^ 40 * 250741 * 2
def baseEnd_250741 : Nat := 4768542695892915125347

theorem tailTrace_250741 : CollatzResearch.WordTrace tailWord_250741 prefixEnd_250741 4768542695892915125347 := by
  unfold tailWord_250741
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145275584615654998584077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6096850389743769999056051 9145275584615654998584077)
  ·
    refine ⟨3429478344230870624469029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9145275584615654998584077 3429478344230870624469029)
    ·
      refine ⟨643027189543288242087943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3429478344230870624469029 643027189543288242087943)
      ·
        refine ⟨964540784314932363131915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643027189543288242087943 964540784314932363131915)
        ·
          refine ⟨1446811176472398544697873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964540784314932363131915 1446811176472398544697873)
          ·
            refine ⟨1085108382354298908523405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446811176472398544697873 1085108382354298908523405)
            ·
              refine ⟨406915643382862090696277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085108382354298908523405 406915643382862090696277)
              ·
                refine ⟨4768542695892915125347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 406915643382862090696277 4768542695892915125347)
                ·
                  rfl

theorem cell23_250741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 8].length) (baseStart_250741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250741 prefixEnd_250741 := by exact prefixLift 250741
  have htrace : WordTrace (prefixWord ++ tailWord_250741) baseStart_250741 baseEnd_250741 := by
    simpa [prefixWord, tailWord_250741, baseEnd_250741] using wordTrace_append hprefix tailTrace_250741
  have hstable : (prefixWord ++ tailWord_250741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250741).length < 2 ^ (prefixWord ++ tailWord_250741).sum := by decide
  have hdescent : baseEnd_250741 < baseStart_250741 := by decide
  rcases family_descends (prefixWord ++ tailWord_250741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250751 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_250751 : Nat := 118140960795 + 250751 * 2 ^ 59
def prefixEnd_250751 : Nat := 4983230072969 + 3 ^ 40 * 250751 * 2
def baseEnd_250751 : Nat := 128755787595653669259323

theorem tailTrace_250751 : CollatzResearch.WordTrace tailWord_250751 prefixEnd_250751 128755787595653669259323 := by
  unfold tailWord_250751
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145640314579426706448107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6097093543052951137632071 9145640314579426706448107)
  ·
    refine ⟨13718460471869140059672161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9145640314579426706448107 13718460471869140059672161)
    ·
      refine ⟨10288845353901855044754121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13718460471869140059672161 10288845353901855044754121)
      ·
        refine ⟨7716634015426391283565591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10288845353901855044754121 7716634015426391283565591)
        ·
          refine ⟨11574951023139586925348387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716634015426391283565591 11574951023139586925348387)
          ·
            refine ⟨17362426534709380388022581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574951023139586925348387 17362426534709380388022581)
            ·
              refine ⟨1627727487629004411377117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17362426534709380388022581 1627727487629004411377117)
              ·
                refine ⟨610397807860876654266419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627727487629004411377117 610397807860876654266419)
                ·
                  refine ⟨915596711791314981399629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610397807860876654266419 915596711791314981399629)
                  ·
                    refine ⟨343348766921743118024861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915596711791314981399629 343348766921743118024861)
                    ·
                      refine ⟨128755787595653669259323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343348766921743118024861 128755787595653669259323)
                      ·
                        rfl

theorem cell23_250751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_250751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250751 prefixEnd_250751 := by exact prefixLift 250751
  have htrace : WordTrace (prefixWord ++ tailWord_250751) baseStart_250751 baseEnd_250751 := by
    simpa [prefixWord, tailWord_250751, baseEnd_250751] using wordTrace_append hprefix tailTrace_250751
  have hstable : (prefixWord ++ tailWord_250751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250751).length < 2 ^ (prefixWord ++ tailWord_250751).sum := by decide
  have hdescent : baseEnd_250751 < baseStart_250751 := by decide
  rcases family_descends (prefixWord ++ tailWord_250751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250785 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_250785 : Nat := 118140960795 + 250785 * 2 ^ 59
def prefixEnd_250785 : Nat := 4983230072969 + 3 ^ 40 * 250785 * 2
def baseEnd_250785 : Nat := 128773245937906536234167

theorem tailTrace_250785 : CollatzResearch.WordTrace tailWord_250785 prefixEnd_250785 128773245937906536234167 := by
  unfold tailWord_250785
  simp only [CollatzResearch.WordTrace]
  refine ⟨9146880396456250513185809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6097920264304167008790539 9146880396456250513185809)
  ·
    refine ⟨6860160297342187884889357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9146880396456250513185809 6860160297342187884889357)
    ·
      refine ⟨2572560111503320456833509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6860160297342187884889357 2572560111503320456833509)
      ·
        refine ⟨482355020906872585656283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2572560111503320456833509 482355020906872585656283)
        ·
          refine ⟨723532531360308878484425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482355020906872585656283 723532531360308878484425)
          ·
            refine ⟨542649398520231658863319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723532531360308878484425 542649398520231658863319)
            ·
              refine ⟨813974097780347488294979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542649398520231658863319 813974097780347488294979)
              ·
                refine ⟨1220961146670521232442469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813974097780347488294979 1220961146670521232442469)
                ·
                  refine ⟨228930215000722731082963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1220961146670521232442469 228930215000722731082963)
                  ·
                    refine ⟨343395322501084096624445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228930215000722731082963 343395322501084096624445)
                    ·
                      refine ⟨128773245937906536234167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343395322501084096624445 128773245937906536234167)
                      ·
                        rfl

theorem cell23_250785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_250785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250785 prefixEnd_250785 := by exact prefixLift 250785
  have htrace : WordTrace (prefixWord ++ tailWord_250785) baseStart_250785 baseEnd_250785 := by
    simpa [prefixWord, tailWord_250785, baseEnd_250785] using wordTrace_append hprefix tailTrace_250785
  have hstable : (prefixWord ++ tailWord_250785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250785).length < 2 ^ (prefixWord ++ tailWord_250785).sum := by decide
  have hdescent : baseEnd_250785 < baseStart_250785 := by decide
  rcases family_descends (prefixWord ++ tailWord_250785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250806 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_250806 : Nat := 118140960795 + 250806 * 2 ^ 59
def prefixEnd_250806 : Nat := 4983230072969 + 3 ^ 40 * 250806 * 2
def baseEnd_250806 : Nat := 128784029031650954071571

theorem tailTrace_250806 : CollatzResearch.WordTrace tailWord_250806 prefixEnd_250806 128784029031650954071571 := by
  unfold tailWord_250806
  simp only [CollatzResearch.WordTrace]
  refine ⟨571727895586260693731267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6098430886253447399800181 571727895586260693731267)
  ·
    refine ⟨857591843379391040596901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 571727895586260693731267 857591843379391040596901)
    ·
      refine ⟨160798470633635820111919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 857591843379391040596901 160798470633635820111919)
      ·
        refine ⟨241197705950453730167879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160798470633635820111919 241197705950453730167879)
        ·
          refine ⟨361796558925680595251819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241197705950453730167879 361796558925680595251819)
          ·
            refine ⟨542694838388520892877729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361796558925680595251819 542694838388520892877729)
            ·
              refine ⟨407021128791390669658297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542694838388520892877729 407021128791390669658297)
              ·
                refine ⟨305265846593543002243723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407021128791390669658297 305265846593543002243723)
                ·
                  refine ⟨457898769890314503365585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305265846593543002243723 457898769890314503365585)
                  ·
                    refine ⟨343424077417735877524189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457898769890314503365585 343424077417735877524189)
                    ·
                      refine ⟨128784029031650954071571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343424077417735877524189 128784029031650954071571)
                      ·
                        rfl

theorem cell23_250806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_250806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250806 prefixEnd_250806 := by exact prefixLift 250806
  have htrace : WordTrace (prefixWord ++ tailWord_250806) baseStart_250806 baseEnd_250806 := by
    simpa [prefixWord, tailWord_250806, baseEnd_250806] using wordTrace_append hprefix tailTrace_250806
  have hstable : (prefixWord ++ tailWord_250806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250806).length < 2 ^ (prefixWord ++ tailWord_250806).sum := by decide
  have hdescent : baseEnd_250806 < baseStart_250806 := by decide
  rcases family_descends (prefixWord ++ tailWord_250806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250915 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 2, 4, 2]
def baseStart_250915 : Nat := 118140960795 + 250915 * 2 ^ 59
def prefixEnd_250915 : Nat := 4983230072969 + 3 ^ 40 * 250915 * 2
def baseEnd_250915 : Nat := 128839998422991027608569

theorem tailTrace_250915 : CollatzResearch.WordTrace tailWord_250915 prefixEnd_250915 128839998422991027608569 := by
  unfold tailWord_250915
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151621885985282715418199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6101081257323521810278799 9151621885985282715418199)
  ·
    refine ⟨13727432828977924073127299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9151621885985282715418199 13727432828977924073127299)
    ·
      refine ⟨20591149243466886109690949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727432828977924073127299 20591149243466886109690949)
      ·
        refine ⟨3860840483150041145567053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20591149243466886109690949 3860840483150041145567053)
        ·
          refine ⟨1447815181181265429587645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3860840483150041145567053 1447815181181265429587645)
          ·
            refine ⟨542930692942974536095367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1447815181181265429587645 542930692942974536095367)
            ·
              refine ⟨814396039414461804143051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542930692942974536095367 814396039414461804143051)
              ·
                refine ⟨1221594059121692706214577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814396039414461804143051 1221594059121692706214577)
                ·
                  refine ⟨916195544341269529660933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1221594059121692706214577 916195544341269529660933)
                  ·
                    refine ⟨171786664563988036811425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916195544341269529660933 171786664563988036811425)
                    ·
                      refine ⟨128839998422991027608569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171786664563988036811425 128839998422991027608569)
                      ·
                        rfl

theorem cell23_250915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_250915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250915 prefixEnd_250915 := by exact prefixLift 250915
  have htrace : WordTrace (prefixWord ++ tailWord_250915) baseStart_250915 baseEnd_250915 := by
    simpa [prefixWord, tailWord_250915, baseEnd_250915] using wordTrace_append hprefix tailTrace_250915
  have hstable : (prefixWord ++ tailWord_250915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250915).length < 2 ^ (prefixWord ++ tailWord_250915).sum := by decide
  have hdescent : baseEnd_250915 < baseStart_250915 := by decide
  rcases family_descends (prefixWord ++ tailWord_250915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250932 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_250932 : Nat := 118140960795 + 250932 * 2 ^ 59
def prefixEnd_250932 : Nat := 4983230072969 + 3 ^ 40 * 250932 * 2
def baseEnd_250932 : Nat := 128848727594117461095991

theorem tailTrace_250932 : CollatzResearch.WordTrace tailWord_250932 prefixEnd_250932 128848727594117461095991 := by
  unfold tailWord_250932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576120963461847309393525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6101494617949129745858033 4576120963461847309393525)
  ·
    refine ⟨429011340324548185255643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4576120963461847309393525 429011340324548185255643)
    ·
      refine ⟨643517010486822277883465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429011340324548185255643 643517010486822277883465)
      ·
        refine ⟨482637757865116708412599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643517010486822277883465 482637757865116708412599)
        ·
          refine ⟨723956636797675062618899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482637757865116708412599 723956636797675062618899)
          ·
            refine ⟨1085934955196512593928349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723956636797675062618899 1085934955196512593928349)
            ·
              refine ⟨407225608198692222723131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085934955196512593928349 407225608198692222723131)
              ·
                refine ⟨610838412298038334084697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407225608198692222723131 610838412298038334084697)
                ·
                  refine ⟨458128809223528750563523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610838412298038334084697 458128809223528750563523)
                  ·
                    refine ⟨687193213835293125845285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458128809223528750563523 687193213835293125845285)
                    ·
                      refine ⟨128848727594117461095991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 687193213835293125845285 128848727594117461095991)
                      ·
                        rfl

theorem cell23_250932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_250932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250932 prefixEnd_250932 := by exact prefixLift 250932
  have htrace : WordTrace (prefixWord ++ tailWord_250932) baseStart_250932 baseEnd_250932 := by
    simpa [prefixWord, tailWord_250932, baseEnd_250932] using wordTrace_append hprefix tailTrace_250932
  have hstable : (prefixWord ++ tailWord_250932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250932).length < 2 ^ (prefixWord ++ tailWord_250932).sum := by decide
  have hdescent : baseEnd_250932 < baseStart_250932 := by decide
  rcases family_descends (prefixWord ++ tailWord_250932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250985 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_250985 : Nat := 118140960795 + 250985 * 2 ^ 59
def prefixEnd_250985 : Nat := 4983230072969 + 3 ^ 40 * 250985 * 2
def baseEnd_250985 : Nat := 42958647356268584577749

theorem tailTrace_250985 : CollatzResearch.WordTrace tailWord_250985 prefixEnd_250985 42958647356268584577749 := by
  unfold tailWord_250985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154174995731684670466409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6102783330487789780310939 9154174995731684670466409)
  ·
    refine ⟨6865631246798763502849807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9154174995731684670466409 6865631246798763502849807)
    ·
      refine ⟨10298446870198145254274711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865631246798763502849807 10298446870198145254274711)
      ·
        refine ⟨15447670305297217881412067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298446870198145254274711 15447670305297217881412067)
        ·
          refine ⟨23171505457945826822118101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447670305297217881412067 23171505457945826822118101)
          ·
            refine ⟨543082159170605316143393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23171505457945826822118101 543082159170605316143393)
            ·
              refine ⟨407311619377953987107545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543082159170605316143393 407311619377953987107545)
              ·
                refine ⟨305483714533465490330659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407311619377953987107545 305483714533465490330659)
                ·
                  refine ⟨458225571800198235495989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305483714533465490330659 458225571800198235495989)
                  ·
                    refine ⟨42958647356268584577749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458225571800198235495989 42958647356268584577749)
                    ·
                      rfl

theorem cell23_250985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_250985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_250985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_250985 prefixEnd_250985 := by exact prefixLift 250985
  have htrace : WordTrace (prefixWord ++ tailWord_250985) baseStart_250985 baseEnd_250985 := by
    simpa [prefixWord, tailWord_250985, baseEnd_250985] using wordTrace_append hprefix tailTrace_250985
  have hstable : (prefixWord ++ tailWord_250985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250985).length < 2 ^ (prefixWord ++ tailWord_250985).sum := by decide
  have hdescent : baseEnd_250985 < baseStart_250985 := by decide
  rcases family_descends (prefixWord ++ tailWord_250985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251005 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_251005 : Nat := 118140960795 + 251005 * 2 ^ 59
def prefixEnd_251005 : Nat := 4983230072969 + 3 ^ 40 * 251005 * 2
def baseEnd_251005 : Nat := 128886211681895675483155

theorem tailTrace_251005 : CollatzResearch.WordTrace tailWord_251005 prefixEnd_251005 128886211681895675483155 := by
  unfold tailWord_251005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154904455659228086194469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6103269637106152057462979 9154904455659228086194469)
  ·
    refine ⟨1716544585436105266161463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9154904455659228086194469 1716544585436105266161463)
    ·
      refine ⟨2574816878154157899242195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716544585436105266161463 2574816878154157899242195)
      ·
        refine ⟨3862225317231236848863293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574816878154157899242195 3862225317231236848863293)
        ·
          refine ⟨1448334493961713818323735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3862225317231236848863293 1448334493961713818323735)
          ·
            refine ⟨2172501740942570727485603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448334493961713818323735 2172501740942570727485603)
            ·
              refine ⟨3258752611413856091228405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172501740942570727485603 3258752611413856091228405)
              ·
                refine ⟨305508057320049008552663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3258752611413856091228405 305508057320049008552663)
                ·
                  refine ⟨458262085980073512828995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305508057320049008552663 458262085980073512828995)
                  ·
                    refine ⟨687393128970110269243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458262085980073512828995 687393128970110269243493)
                    ·
                      refine ⟨128886211681895675483155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 687393128970110269243493 128886211681895675483155)
                      ·
                        rfl

theorem cell23_251005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_251005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251005 prefixEnd_251005 := by exact prefixLift 251005
  have htrace : WordTrace (prefixWord ++ tailWord_251005) baseStart_251005 baseEnd_251005 := by
    simpa [prefixWord, tailWord_251005, baseEnd_251005] using wordTrace_append hprefix tailTrace_251005
  have hstable : (prefixWord ++ tailWord_251005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251005).length < 2 ^ (prefixWord ++ tailWord_251005).sum := by decide
  have hdescent : baseEnd_251005 < baseStart_251005 := by decide
  rcases family_descends (prefixWord ++ tailWord_251005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251008 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_251008 : Nat := 118140960795 + 251008 * 2 ^ 59
def prefixEnd_251008 : Nat := 4983230072969 + 3 ^ 40 * 251008 * 2
def baseEnd_251008 : Nat := 128887752123859163745641

theorem tailTrace_251008 : CollatzResearch.WordTrace tailWord_251008 prefixEnd_251008 128887752123859163745641 := by
  unfold tailWord_251008
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577506937324179799276839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6103342583098906399035785 4577506937324179799276839)
  ·
    refine ⟨6866260405986269698915259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577506937324179799276839 6866260405986269698915259)
    ·
      refine ⟨10299390608979404548372889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6866260405986269698915259 10299390608979404548372889)
      ·
        refine ⟨7724542956734553411279667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10299390608979404548372889 7724542956734553411279667)
        ·
          refine ⟨11586814435101830116919501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724542956734553411279667 11586814435101830116919501)
          ·
            refine ⟨4345055413163186293844813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11586814435101830116919501 4345055413163186293844813)
            ·
              refine ⟨1629395779936194860191805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4345055413163186293844813 1629395779936194860191805)
              ·
                refine ⟨611023417476073072571927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629395779936194860191805 611023417476073072571927)
                ·
                  refine ⟨916535126214109608857891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611023417476073072571927 916535126214109608857891)
                  ·
                    refine ⟨1374802689321164413286837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 916535126214109608857891 1374802689321164413286837)
                    ·
                      refine ⟨128887752123859163745641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1374802689321164413286837 128887752123859163745641)
                      ·
                        rfl

theorem cell23_251008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_251008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251008 prefixEnd_251008 := by exact prefixLift 251008
  have htrace : WordTrace (prefixWord ++ tailWord_251008) baseStart_251008 baseEnd_251008 := by
    simpa [prefixWord, tailWord_251008, baseEnd_251008] using wordTrace_append hprefix tailTrace_251008
  have hstable : (prefixWord ++ tailWord_251008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251008).length < 2 ^ (prefixWord ++ tailWord_251008).sum := by decide
  have hdescent : baseEnd_251008 < baseStart_251008 := by decide
  rcases family_descends (prefixWord ++ tailWord_251008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251015 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 2, 4]
def baseStart_251015 : Nat := 118140960795 + 251015 * 2 ^ 59
def prefixEnd_251015 : Nat := 4983230072969 + 3 ^ 40 * 251015 * 2
def baseEnd_251015 : Nat := 42963782162813545452703

theorem tailTrace_251015 : CollatzResearch.WordTrace tailWord_251015 prefixEnd_251015 42963782162813545452703 := by
  unfold tailWord_251015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155269185622999794058499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6103512790415333196038999 9155269185622999794058499)
  ·
    refine ⟨13732903778434499691087749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9155269185622999794058499 13732903778434499691087749)
    ·
      refine ⟨2574919458456468692078953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13732903778434499691087749 2574919458456468692078953)
      ·
        refine ⟨1931189593842351519059215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2574919458456468692078953 1931189593842351519059215)
        ·
          refine ⟨2896784390763527278588823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931189593842351519059215 2896784390763527278588823)
          ·
            refine ⟨4345176586145290917883235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896784390763527278588823 4345176586145290917883235)
            ·
              refine ⟨6517764879217936376824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345176586145290917883235 6517764879217936376824853)
              ·
                refine ⟨305520228713340767663665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6517764879217936376824853 305520228713340767663665)
                ·
                  refine ⟨229140171535005575747749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305520228713340767663665 229140171535005575747749)
                  ·
                    refine ⟨42963782162813545452703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229140171535005575747749 42963782162813545452703)
                    ·
                      rfl

theorem cell23_251015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_251015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251015 prefixEnd_251015 := by exact prefixLift 251015
  have htrace : WordTrace (prefixWord ++ tailWord_251015) baseStart_251015 baseEnd_251015 := by
    simpa [prefixWord, tailWord_251015, baseEnd_251015] using wordTrace_append hprefix tailTrace_251015
  have hstable : (prefixWord ++ tailWord_251015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251015).length < 2 ^ (prefixWord ++ tailWord_251015).sum := by decide
  have hdescent : baseEnd_251015 < baseStart_251015 := by decide
  rcases family_descends (prefixWord ++ tailWord_251015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251016 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_251016 : Nat := 118140960795 + 251016 * 2 ^ 59
def prefixEnd_251016 : Nat := 4983230072969 + 3 ^ 40 * 251016 * 2
def baseEnd_251016 : Nat := 128891859969095132445605

theorem tailTrace_251016 : CollatzResearch.WordTrace tailWord_251016 prefixEnd_251016 128891859969095132445605 := by
  unfold tailWord_251016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577652829309688482422451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6103537105746251309896601 4577652829309688482422451)
  ·
    refine ⟨6866479243964532723633677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577652829309688482422451 6866479243964532723633677)
    ·
      refine ⟨2574929716486699771362629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6866479243964532723633677 2574929716486699771362629)
      ·
        refine ⟨482799321841256207130493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2574929716486699771362629 482799321841256207130493)
        ·
          refine ⟨181049745690471077673935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482799321841256207130493 181049745690471077673935)
          ·
            refine ⟨271574618535706616510903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181049745690471077673935 271574618535706616510903)
            ·
              refine ⟨407361927803559924766355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271574618535706616510903 407361927803559924766355)
              ·
                refine ⟨611042891705339887149533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407361927803559924766355 611042891705339887149533)
                ·
                  refine ⟨229141084389502457681075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611042891705339887149533 229141084389502457681075)
                  ·
                    refine ⟨343711626584253686521613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229141084389502457681075 343711626584253686521613)
                    ·
                      refine ⟨128891859969095132445605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343711626584253686521613 128891859969095132445605)
                      ·
                        rfl

theorem cell23_251016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_251016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251016 prefixEnd_251016 := by exact prefixLift 251016
  have htrace : WordTrace (prefixWord ++ tailWord_251016) baseStart_251016 baseEnd_251016 := by
    simpa [prefixWord, tailWord_251016, baseEnd_251016] using wordTrace_append hprefix tailTrace_251016
  have hstable : (prefixWord ++ tailWord_251016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251016).length < 2 ^ (prefixWord ++ tailWord_251016).sum := by decide
  have hdescent : baseEnd_251016 < baseStart_251016 := by decide
  rcases family_descends (prefixWord ++ tailWord_251016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251018 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_251018 : Nat := 118140960795 + 251018 * 2 ^ 59
def prefixEnd_251018 : Nat := 4983230072969 + 3 ^ 40 * 251018 * 2
def baseEnd_251018 : Nat := 128892886930404124620595

theorem tailTrace_251018 : CollatzResearch.WordTrace tailWord_251018 prefixEnd_251018 128892886930404124620595 := by
  unfold tailWord_251018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288844651153032826604427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6103585736408087537611805 2288844651153032826604427)
  ·
    refine ⟨3433266976729549239906641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288844651153032826604427 3433266976729549239906641)
    ·
      refine ⟨2574950232547161929929981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3433266976729549239906641 2574950232547161929929981)
      ·
        refine ⟨965606337205185723723743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2574950232547161929929981 965606337205185723723743)
        ·
          refine ⟨1448409505807778585585615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965606337205185723723743 1448409505807778585585615)
          ·
            refine ⟨2172614258711667878378423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448409505807778585585615 2172614258711667878378423)
            ·
              refine ⟨3258921388067501817567635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172614258711667878378423 3258921388067501817567635)
              ·
                refine ⟨4888382082101252726351453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258921388067501817567635 4888382082101252726351453)
                ·
                  refine ⟨1833143280787969772381795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4888382082101252726351453 1833143280787969772381795)
                  ·
                    refine ⟨2749714921181954658572693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1833143280787969772381795 2749714921181954658572693)
                    ·
                      refine ⟨128892886930404124620595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2749714921181954658572693 128892886930404124620595)
                      ·
                        rfl

theorem cell23_251018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_251018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251018 prefixEnd_251018 := by exact prefixLift 251018
  have htrace : WordTrace (prefixWord ++ tailWord_251018) baseStart_251018 baseEnd_251018 := by
    simpa [prefixWord, tailWord_251018, baseEnd_251018] using wordTrace_append hprefix tailTrace_251018
  have hstable : (prefixWord ++ tailWord_251018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251018).length < 2 ^ (prefixWord ++ tailWord_251018).sum := by decide
  have hdescent : baseEnd_251018 < baseStart_251018 := by decide
  rcases family_descends (prefixWord ++ tailWord_251018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251032 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_251032 : Nat := 118140960795 + 251032 * 2 ^ 59
def prefixEnd_251032 : Nat := 4983230072969 + 3 ^ 40 * 251032 * 2
def baseEnd_251032 : Nat := 42966691886522356615177

theorem tailTrace_251032 : CollatzResearch.WordTrace tailWord_251032 prefixEnd_251032 42966691886522356615177 := by
  unfold tailWord_251032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577944613280705848713675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6103926151040941131618233 4577944613280705848713675)
  ·
    refine ⟨6866916919921058773070513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577944613280705848713675 6866916919921058773070513)
    ·
      refine ⟨5150187689940794079802885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6866916919921058773070513 5150187689940794079802885)
      ·
        refine ⟨965660191863898889963041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5150187689940794079802885 965660191863898889963041)
        ·
          refine ⟨724245143897924167472281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965660191863898889963041 724245143897924167472281)
          ·
            refine ⟨543183857923443125604211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724245143897924167472281 543183857923443125604211)
            ·
              refine ⟨814775786885164688406317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543183857923443125604211 814775786885164688406317)
              ·
                refine ⟨305540920081936758152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814775786885164688406317 305540920081936758152369)
                ·
                  refine ⟨229155690061452568614277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305540920081936758152369 229155690061452568614277)
                  ·
                    refine ⟨42966691886522356615177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229155690061452568614277 42966691886522356615177)
                    ·
                      rfl

theorem cell23_251032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_251032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251032 prefixEnd_251032 := by exact prefixLift 251032
  have htrace : WordTrace (prefixWord ++ tailWord_251032) baseStart_251032 baseEnd_251032 := by
    simpa [prefixWord, tailWord_251032, baseEnd_251032] using wordTrace_append hprefix tailTrace_251032
  have hstable : (prefixWord ++ tailWord_251032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251032).length < 2 ^ (prefixWord ++ tailWord_251032).sum := by decide
  have hdescent : baseEnd_251032 < baseStart_251032 := by decide
  rcases family_descends (prefixWord ++ tailWord_251032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251039 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_251039 : Nat := 118140960795 + 251039 * 2 ^ 59
def prefixEnd_251039 : Nat := 4983230072969 + 3 ^ 40 * 251039 * 2
def baseEnd_251039 : Nat := 128903670024148542457999

theorem tailTrace_251039 : CollatzResearch.WordTrace tailWord_251039 prefixEnd_251039 128903670024148542457999 := by
  unfold tailWord_251039
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156144537536051892932171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6104096358357367928621447 9156144537536051892932171)
  ·
    refine ⟨13734216806304077839398257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156144537536051892932171 13734216806304077839398257)
    ·
      refine ⟨10300662604728058379548693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13734216806304077839398257 10300662604728058379548693)
      ·
        refine ⟨482843559596627736541345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10300662604728058379548693 482843559596627736541345)
        ·
          refine ⟨362132669697470802406009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482843559596627736541345 362132669697470802406009)
          ·
            refine ⟨271599502273103101804507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362132669697470802406009 271599502273103101804507)
            ·
              refine ⟨407399253409654652706761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271599502273103101804507 407399253409654652706761)
              ·
                refine ⟨305549440057240989530071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407399253409654652706761 305549440057240989530071)
                ·
                  refine ⟨458324160085861484295107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305549440057240989530071 458324160085861484295107)
                  ·
                    refine ⟨687486240128792226442661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458324160085861484295107 687486240128792226442661)
                    ·
                      refine ⟨128903670024148542457999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 687486240128792226442661 128903670024148542457999)
                      ·
                        rfl

theorem cell23_251039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_251039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251039 prefixEnd_251039 := by exact prefixLift 251039
  have htrace : WordTrace (prefixWord ++ tailWord_251039) baseStart_251039 baseEnd_251039 := by
    simpa [prefixWord, tailWord_251039, baseEnd_251039] using wordTrace_append hprefix tailTrace_251039
  have hstable : (prefixWord ++ tailWord_251039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251039).length < 2 ^ (prefixWord ++ tailWord_251039).sum := by decide
  have hdescent : baseEnd_251039 < baseStart_251039 := by decide
  rcases family_descends (prefixWord ++ tailWord_251039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251055 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 3]
def baseStart_251055 : Nat := 118140960795 + 251055 * 2 ^ 59
def prefixEnd_251055 : Nat := 4983230072969 + 3 ^ 40 * 251055 * 2
def baseEnd_251055 : Nat := 128911885714620479857925

theorem tailTrace_251055 : CollatzResearch.WordTrace tailWord_251055 prefixEnd_251055 128911885714620479857925 := by
  unfold tailWord_251055
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156728105478086625514619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6104485403652057750343079 9156728105478086625514619)
  ·
    refine ⟨13735092158217129938271929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156728105478086625514619 13735092158217129938271929)
    ·
      refine ⟨10301319118662847453703947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13735092158217129938271929 10301319118662847453703947)
      ·
        refine ⟨15451978677994271180555921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301319118662847453703947 15451978677994271180555921)
        ·
          refine ⟨11588984008495703385416941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15451978677994271180555921 11588984008495703385416941)
          ·
            refine ⟨4345869003185888769531353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11588984008495703385416941 4345869003185888769531353)
            ·
              refine ⟨3259401752389416577148515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345869003185888769531353 3259401752389416577148515)
              ·
                refine ⟨4889102628584124865722773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259401752389416577148515 4889102628584124865722773)
                ·
                  refine ⟨229176685714880853080755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4889102628584124865722773 229176685714880853080755)
                  ·
                    refine ⟨343765028572321279621133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229176685714880853080755 343765028572321279621133)
                    ·
                      refine ⟨128911885714620479857925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343765028572321279621133 128911885714620479857925)
                      ·
                        rfl

theorem cell23_251055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_251055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251055 prefixEnd_251055 := by exact prefixLift 251055
  have htrace : WordTrace (prefixWord ++ tailWord_251055) baseStart_251055 baseEnd_251055 := by
    simpa [prefixWord, tailWord_251055, baseEnd_251055] using wordTrace_append hprefix tailTrace_251055
  have hstable : (prefixWord ++ tailWord_251055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251055).length < 2 ^ (prefixWord ++ tailWord_251055).sum := by decide
  have hdescent : baseEnd_251055 < baseStart_251055 := by decide
  rcases family_descends (prefixWord ++ tailWord_251055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251062 : List Nat := [5, 1, 3, 2, 1, 11]
def baseStart_251062 : Nat := 118140960795 + 251062 * 2 ^ 59
def prefixEnd_251062 : Nat := 4983230072969 + 3 ^ 40 * 251062 * 2
def baseEnd_251062 : Nat := 530516378926757006051

theorem tailTrace_251062 : CollatzResearch.WordTrace tailWord_251062 prefixEnd_251062 530516378926757006051 := by
  unfold tailWord_251062
  simp only [CollatzResearch.WordTrace]
  refine ⟨572311463528295426313715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6104655610968484547346293 572311463528295426313715)
  ·
    refine ⟨858467195292443139470573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572311463528295426313715 858467195292443139470573)
    ·
      refine ⟨321925198234666177301465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 858467195292443139470573 321925198234666177301465)
      ·
        refine ⟨241443898675999632976099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321925198234666177301465 241443898675999632976099)
        ·
          refine ⟨362165848013999449464149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241443898675999632976099 362165848013999449464149)
          ·
            refine ⟨530516378926757006051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 362165848013999449464149 530516378926757006051)
            ·
              rfl

theorem cell23_251062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 11].length) (baseStart_251062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251062 prefixEnd_251062 := by exact prefixLift 251062
  have htrace : WordTrace (prefixWord ++ tailWord_251062) baseStart_251062 baseEnd_251062 := by
    simpa [prefixWord, tailWord_251062, baseEnd_251062] using wordTrace_append hprefix tailTrace_251062
  have hstable : (prefixWord ++ tailWord_251062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251062).length < 2 ^ (prefixWord ++ tailWord_251062).sum := by decide
  have hdescent : baseEnd_251062 < baseStart_251062 := by decide
  rcases family_descends (prefixWord ++ tailWord_251062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251073 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_251073 : Nat := 118140960795 + 251073 * 2 ^ 59
def prefixEnd_251073 : Nat := 4983230072969 + 3 ^ 40 * 251073 * 2
def baseEnd_251073 : Nat := 128921128366401409432843

theorem tailTrace_251073 : CollatzResearch.WordTrace tailWord_251073 prefixEnd_251073 128921128366401409432843 := by
  unfold tailWord_251073
  simp only [CollatzResearch.WordTrace]
  refine ⟨9157384619412875699669873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6104923079608583799779915 9157384619412875699669873)
  ·
    refine ⟨6868038464559656774752405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9157384619412875699669873 6868038464559656774752405)
    ·
      refine ⟨321939303026233911316519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6868038464559656774752405 321939303026233911316519)
      ·
        refine ⟨482908954539350866974779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321939303026233911316519 482908954539350866974779)
        ·
          refine ⟨724363431809026300462169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482908954539350866974779 724363431809026300462169)
          ·
            refine ⟨543272573856769725346627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724363431809026300462169 543272573856769725346627)
            ·
              refine ⟨814908860785154588019941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543272573856769725346627 814908860785154588019941)
              ·
                refine ⟨152795411397216485253739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814908860785154588019941 152795411397216485253739)
                ·
                  refine ⟨229193117095824727880609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152795411397216485253739 229193117095824727880609)
                  ·
                    refine ⟨171894837821868545910457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229193117095824727880609 171894837821868545910457)
                    ·
                      refine ⟨128921128366401409432843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171894837821868545910457 128921128366401409432843)
                      ·
                        rfl

theorem cell23_251073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_251073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251073 prefixEnd_251073 := by exact prefixLift 251073
  have htrace : WordTrace (prefixWord ++ tailWord_251073) baseStart_251073 baseEnd_251073 := by
    simpa [prefixWord, tailWord_251073, baseEnd_251073] using wordTrace_append hprefix tailTrace_251073
  have hstable : (prefixWord ++ tailWord_251073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251073).length < 2 ^ (prefixWord ++ tailWord_251073).sum := by decide
  have hdescent : baseEnd_251073 < baseStart_251073 := by decide
  rcases family_descends (prefixWord ++ tailWord_251073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251082 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_251082 : Nat := 118140960795 + 251082 * 2 ^ 59
def prefixEnd_251082 : Nat := 4983230072969 + 3 ^ 40 * 251082 * 2
def baseEnd_251082 : Nat := 128925749692291874220301

theorem tailTrace_251082 : CollatzResearch.WordTrace tailWord_251082 prefixEnd_251082 128925749692291874220301 := by
  unfold tailWord_251082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289428219095067559186875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6105141917586846824498333 2289428219095067559186875)
  ·
    refine ⟨3434142328642601338780313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289428219095067559186875 3434142328642601338780313)
    ·
      refine ⟨2575606746481951004085235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3434142328642601338780313 2575606746481951004085235)
      ·
        refine ⟨3863410119722926506127853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575606746481951004085235 3863410119722926506127853)
        ·
          refine ⟨1448778794896097439797945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3863410119722926506127853 1448778794896097439797945)
          ·
            refine ⟨1086584096172073079848459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448778794896097439797945 1086584096172073079848459)
            ·
              refine ⟨1629876144258109619772689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086584096172073079848459 1629876144258109619772689)
              ·
                refine ⟨1222407108193582214829517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629876144258109619772689 1222407108193582214829517)
                ·
                  refine ⟨458402665572593330561069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222407108193582214829517 458402665572593330561069)
                  ·
                    refine ⟨171900999589722498960401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458402665572593330561069 171900999589722498960401)
                    ·
                      refine ⟨128925749692291874220301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171900999589722498960401 128925749692291874220301)
                      ·
                        rfl

theorem cell23_251082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_251082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251082 prefixEnd_251082 := by exact prefixLift 251082
  have htrace : WordTrace (prefixWord ++ tailWord_251082) baseStart_251082 baseEnd_251082 := by
    simpa [prefixWord, tailWord_251082, baseEnd_251082] using wordTrace_append hprefix tailTrace_251082
  have hstable : (prefixWord ++ tailWord_251082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251082).length < 2 ^ (prefixWord ++ tailWord_251082).sum := by decide
  have hdescent : baseEnd_251082 < baseStart_251082 := by decide
  rcases family_descends (prefixWord ++ tailWord_251082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251112 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_251112 : Nat := 118140960795 + 251112 * 2 ^ 59
def prefixEnd_251112 : Nat := 4983230072969 + 3 ^ 40 * 251112 * 2
def baseEnd_251112 : Nat := 128941154111926756845163

theorem tailTrace_251112 : CollatzResearch.WordTrace tailWord_251112 prefixEnd_251112 128941154111926756845163 := by
  unfold tailWord_251112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579403533135792680169795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6105871377514390240226393 4579403533135792680169795)
  ·
    refine ⟨6869105299703689020254693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4579403533135792680169795 6869105299703689020254693)
    ·
      refine ⟨1287957243694441691297755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6869105299703689020254693 1287957243694441691297755)
      ·
        refine ⟨1931935865541662536946633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287957243694441691297755 1931935865541662536946633)
        ·
          refine ⟨1448951899156246902709975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931935865541662536946633 1448951899156246902709975)
          ·
            refine ⟨2173427848734370354064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448951899156246902709975 2173427848734370354064963)
            ·
              refine ⟨3260141773101555531097445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173427848734370354064963 3260141773101555531097445)
              ·
                refine ⟨611276582456541662080771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3260141773101555531097445 611276582456541662080771)
                ·
                  refine ⟨916914873684812493121157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611276582456541662080771 916914873684812493121157)
                  ·
                    refine ⟨171921538815902342460217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916914873684812493121157 171921538815902342460217)
                    ·
                      refine ⟨128941154111926756845163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171921538815902342460217 128941154111926756845163)
                      ·
                        rfl

theorem cell23_251112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_251112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251112 prefixEnd_251112 := by exact prefixLift 251112
  have htrace : WordTrace (prefixWord ++ tailWord_251112) baseStart_251112 baseEnd_251112 := by
    simpa [prefixWord, tailWord_251112, baseEnd_251112] using wordTrace_append hprefix tailTrace_251112
  have hstable : (prefixWord ++ tailWord_251112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251112).length < 2 ^ (prefixWord ++ tailWord_251112).sum := by decide
  have hdescent : baseEnd_251112 < baseStart_251112 := by decide
  rcases family_descends (prefixWord ++ tailWord_251112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251116 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_251116 : Nat := 118140960795 + 251116 * 2 ^ 59
def prefixEnd_251116 : Nat := 4983230072969 + 3 ^ 40 * 251116 * 2
def baseEnd_251116 : Nat := 128943208034544741195145

theorem tailTrace_251116 : CollatzResearch.WordTrace tailWord_251116 prefixEnd_251116 128943208034544741195145 := by
  unfold tailWord_251116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579476479128547021742601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6105968638838062695656801 4579476479128547021742601)
  ·
    refine ⟨3434607359346410266306951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4579476479128547021742601 3434607359346410266306951)
    ·
      refine ⟨5151911039019615399460427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434607359346410266306951 5151911039019615399460427)
      ·
        refine ⟨7727866558529423099190641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151911039019615399460427 7727866558529423099190641)
        ·
          refine ⟨5795899918897067324392981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7727866558529423099190641 5795899918897067324392981)
          ·
            refine ⟨271682808698300030830921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5795899918897067324392981 271682808698300030830921)
            ·
              refine ⟨203762106523725023123191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271682808698300030830921 203762106523725023123191)
              ·
                refine ⟨305643159785587534684787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203762106523725023123191 305643159785587534684787)
                ·
                  refine ⟨458464739678381302027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305643159785587534684787 458464739678381302027181)
                  ·
                    refine ⟨171924277379392988260193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458464739678381302027181 171924277379392988260193)
                    ·
                      refine ⟨128943208034544741195145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171924277379392988260193 128943208034544741195145)
                      ·
                        rfl

theorem cell23_251116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_251116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251116 prefixEnd_251116 := by exact prefixLift 251116
  have htrace : WordTrace (prefixWord ++ tailWord_251116) baseStart_251116 baseEnd_251116 := by
    simpa [prefixWord, tailWord_251116, baseEnd_251116] using wordTrace_append hprefix tailTrace_251116
  have hstable : (prefixWord ++ tailWord_251116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251116).length < 2 ^ (prefixWord ++ tailWord_251116).sum := by decide
  have hdescent : baseEnd_251116 < baseStart_251116 := by decide
  rcases family_descends (prefixWord ++ tailWord_251116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251135 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 7]
def baseStart_251135 : Nat := 118140960795 + 251135 * 2 ^ 59
def prefixEnd_251135 : Nat := 4983230072969 + 3 ^ 40 * 251135 * 2
def baseEnd_251135 : Nat := 14328107129664462984173

theorem tailTrace_251135 : CollatzResearch.WordTrace tailWord_251135 prefixEnd_251135 14328107129664462984173 := by
  unfold tailWord_251135
  simp only [CollatzResearch.WordTrace]
  refine ⟨9159645945188260288426859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6106430630125506858951239 9159645945188260288426859)
  ·
    refine ⟨13739468917782390432640289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9159645945188260288426859 13739468917782390432640289)
    ·
      refine ⟨10304601688336792824480217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13739468917782390432640289 10304601688336792824480217)
      ·
        refine ⟨7728451266252594618360163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10304601688336792824480217 7728451266252594618360163)
        ·
          refine ⟨11592676899378891927540245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728451266252594618360163 11592676899378891927540245)
          ·
            refine ⟨543406729658385559103449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11592676899378891927540245 543406729658385559103449)
            ·
              refine ⟨407555047243789169327587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543406729658385559103449 407555047243789169327587)
              ·
                refine ⟨611332570865683753991381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407555047243789169327587 611332570865683753991381)
                ·
                  refine ⟨14328107129664462984173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 611332570865683753991381 14328107129664462984173)
                  ·
                    rfl

theorem cell23_251135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 7].length) (baseStart_251135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251135 prefixEnd_251135 := by exact prefixLift 251135
  have htrace : WordTrace (prefixWord ++ tailWord_251135) baseStart_251135 baseEnd_251135 := by
    simpa [prefixWord, tailWord_251135, baseEnd_251135] using wordTrace_append hprefix tailTrace_251135
  have hstable : (prefixWord ++ tailWord_251135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251135).length < 2 ^ (prefixWord ++ tailWord_251135).sum := by decide
  have hdescent : baseEnd_251135 < baseStart_251135 := by decide
  rcases family_descends (prefixWord ++ tailWord_251135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251145 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_251145 : Nat := 118140960795 + 251145 * 2 ^ 59
def prefixEnd_251145 : Nat := 4983230072969 + 3 ^ 40 * 251145 * 2
def baseEnd_251145 : Nat := 128958098973525127732511

theorem tailTrace_251145 : CollatzResearch.WordTrace tailWord_251145 prefixEnd_251145 128958098973525127732511 := by
  unfold tailWord_251145
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160010675152031996290889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6106673783434687997527259 9160010675152031996290889)
  ·
    refine ⟨6870008006364023997218167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9160010675152031996290889 6870008006364023997218167)
    ·
      refine ⟨10305012009546035995827251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870008006364023997218167 10305012009546035995827251)
      ·
        refine ⟨15457518014319053993740877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305012009546035995827251 15457518014319053993740877)
        ·
          refine ⟨5796569255369645247652829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15457518014319053993740877 5796569255369645247652829)
          ·
            refine ⟨2173713470763616967869811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5796569255369645247652829 2173713470763616967869811)
            ·
              refine ⟨3260570206145425451804717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173713470763616967869811 3260570206145425451804717)
              ·
                refine ⟨1222713827304534544426769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3260570206145425451804717 1222713827304534544426769)
                ·
                  refine ⟨917035370478400908320077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222713827304534544426769 917035370478400908320077)
                  ·
                    refine ⟨343888263929400340620029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917035370478400908320077 343888263929400340620029)
                    ·
                      refine ⟨128958098973525127732511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343888263929400340620029 128958098973525127732511)
                      ·
                        rfl

theorem cell23_251145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_251145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251145 prefixEnd_251145 := by exact prefixLift 251145
  have htrace : WordTrace (prefixWord ++ tailWord_251145) baseStart_251145 baseEnd_251145 := by
    simpa [prefixWord, tailWord_251145, baseEnd_251145] using wordTrace_append hprefix tailTrace_251145
  have hstable : (prefixWord ++ tailWord_251145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251145).length < 2 ^ (prefixWord ++ tailWord_251145).sum := by decide
  have hdescent : baseEnd_251145 < baseStart_251145 := by decide
  rcases family_descends (prefixWord ++ tailWord_251145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251197 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_251197 : Nat := 118140960795 + 251197 * 2 ^ 59
def prefixEnd_251197 : Nat := 4983230072969 + 3 ^ 40 * 251197 * 2
def baseEnd_251197 : Nat := 128984799967558924282273

theorem tailTrace_251197 : CollatzResearch.WordTrace tailWord_251197 prefixEnd_251197 128984799967558924282273 := by
  unfold tailWord_251197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161907270963644877183845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6107938180642429918122563 9161907270963644877183845)
  ·
    refine ⟨1717857613305683414471971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9161907270963644877183845 1717857613305683414471971)
    ·
      refine ⟨2576786419958525121707957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717857613305683414471971 2576786419958525121707957)
      ·
        refine ⟨241573726871111730160121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2576786419958525121707957 241573726871111730160121)
        ·
          refine ⟨181180295153333797620091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241573726871111730160121 181180295153333797620091)
          ·
            refine ⟨271770442730000696430137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181180295153333797620091 271770442730000696430137)
            ·
              refine ⟨203827832047500522322603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271770442730000696430137 203827832047500522322603)
              ·
                refine ⟨305741748071250783483905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203827832047500522322603 305741748071250783483905)
                ·
                  refine ⟨229306311053438087612929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305741748071250783483905 229306311053438087612929)
                  ·
                    refine ⟨171979733290078565709697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229306311053438087612929 171979733290078565709697)
                    ·
                      refine ⟨128984799967558924282273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 171979733290078565709697 128984799967558924282273)
                      ·
                        rfl

theorem cell23_251197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_251197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251197 prefixEnd_251197 := by exact prefixLift 251197
  have htrace : WordTrace (prefixWord ++ tailWord_251197) baseStart_251197 baseEnd_251197 := by
    simpa [prefixWord, tailWord_251197, baseEnd_251197] using wordTrace_append hprefix tailTrace_251197
  have hstable : (prefixWord ++ tailWord_251197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251197).length < 2 ^ (prefixWord ++ tailWord_251197).sum := by decide
  have hdescent : baseEnd_251197 < baseStart_251197 := by decide
  rcases family_descends (prefixWord ++ tailWord_251197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_251205 : Nat := 118140960795 + 251205 * 2 ^ 59
def prefixEnd_251205 : Nat := 4983230072969 + 3 ^ 40 * 251205 * 2
def baseEnd_251205 : Nat := 128988907812794892982235

theorem tailTrace_251205 : CollatzResearch.WordTrace tailWord_251205 prefixEnd_251205 128988907812794892982235 := by
  unfold tailWord_251205
  simp only [CollatzResearch.WordTrace]
  refine ⟨9162199054934662243475069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6108132703289774828983379 9162199054934662243475069)
  ·
    refine ⟨3435824645600498341303151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9162199054934662243475069 3435824645600498341303151)
    ·
      refine ⟨5153736968400747511954727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3435824645600498341303151 5153736968400747511954727)
      ·
        refine ⟨7730605452601121267932091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5153736968400747511954727 7730605452601121267932091)
        ·
          refine ⟨11595908178901681901898137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730605452601121267932091 11595908178901681901898137)
          ·
            refine ⟨8696931134176261426423603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11595908178901681901898137 8696931134176261426423603)
            ·
              refine ⟨13045396701264392139635405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696931134176261426423603 13045396701264392139635405)
              ·
                refine ⟨4892023762974147052363277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13045396701264392139635405 4892023762974147052363277)
                ·
                  refine ⟨1834508911115305144636229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4892023762974147052363277 1834508911115305144636229)
                  ·
                    refine ⟨343970420834119714619293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834508911115305144636229 343970420834119714619293)
                    ·
                      refine ⟨128988907812794892982235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 343970420834119714619293 128988907812794892982235)
                      ·
                        rfl

theorem cell23_251205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_251205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251205 prefixEnd_251205 := by exact prefixLift 251205
  have htrace : WordTrace (prefixWord ++ tailWord_251205) baseStart_251205 baseEnd_251205 := by
    simpa [prefixWord, tailWord_251205, baseEnd_251205] using wordTrace_append hprefix tailTrace_251205
  have hstable : (prefixWord ++ tailWord_251205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251205).length < 2 ^ (prefixWord ++ tailWord_251205).sum := by decide
  have hdescent : baseEnd_251205 < baseStart_251205 := by decide
  rcases family_descends (prefixWord ++ tailWord_251205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251255 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 5, 5]
def baseStart_251255 : Nat := 118140960795 + 251255 * 2 ^ 59
def prefixEnd_251255 : Nat := 4983230072969 + 3 ^ 40 * 251255 * 2
def baseEnd_251255 : Nat := 43004860615173232452335

theorem tailTrace_251255 : CollatzResearch.WordTrace tailWord_251255 prefixEnd_251255 43004860615173232452335 := by
  unfold tailWord_251255
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164022704753520782795219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6109348469835680521863479 9164022704753520782795219)
  ·
    refine ⟨13746034057130281174192829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9164022704753520782795219 13746034057130281174192829)
    ·
      refine ⟨5154762771423855440322311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13746034057130281174192829 5154762771423855440322311)
      ·
        refine ⟨7732144157135783160483467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154762771423855440322311 7732144157135783160483467)
        ·
          refine ⟨11598216235703674740725201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732144157135783160483467 11598216235703674740725201)
          ·
            refine ⟨8698662176777756055543901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11598216235703674740725201 8698662176777756055543901)
            ·
              refine ⟨3261998316291658520828963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8698662176777756055543901 3261998316291658520828963)
              ·
                refine ⟨4892997474437487781243445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261998316291658520828963 4892997474437487781243445)
                ·
                  refine ⟨458718513228514479491573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892997474437487781243445 458718513228514479491573)
                  ·
                    refine ⟨43004860615173232452335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458718513228514479491573 43004860615173232452335)
                    ·
                      rfl

theorem cell23_251255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_251255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251255 prefixEnd_251255 := by exact prefixLift 251255
  have htrace : WordTrace (prefixWord ++ tailWord_251255) baseStart_251255 baseEnd_251255 := by
    simpa [prefixWord, tailWord_251255, baseEnd_251255] using wordTrace_append hprefix tailTrace_251255
  have hstable : (prefixWord ++ tailWord_251255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251255).length < 2 ^ (prefixWord ++ tailWord_251255).sum := by decide
  have hdescent : baseEnd_251255 < baseStart_251255 := by decide
  rcases family_descends (prefixWord ++ tailWord_251255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251272 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_251272 : Nat := 118140960795 + 251272 * 2 ^ 59
def prefixEnd_251272 : Nat := 4983230072969 + 3 ^ 40 * 251272 * 2
def baseEnd_251272 : Nat := 43007770338882043614809

theorem tailTrace_251272 : CollatzResearch.WordTrace tailWord_251272 prefixEnd_251272 43007770338882043614809 := by
  unfold tailWord_251272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582321372845966343082035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6109761830461288457442713 4582321372845966343082035)
  ·
    refine ⟨6873482059268949514623053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4582321372845966343082035 6873482059268949514623053)
    ·
      refine ⟨2577555772225856067983645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6873482059268949514623053 2577555772225856067983645)
      ·
        refine ⟨966583414584696025493867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2577555772225856067983645 966583414584696025493867)
        ·
          refine ⟨1449875121877044038240801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966583414584696025493867 1449875121877044038240801)
          ·
            refine ⟨1087406341407783028680601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449875121877044038240801 1087406341407783028680601)
            ·
              refine ⟨815554756055837271510451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087406341407783028680601 815554756055837271510451)
              ·
                refine ⟨1223332134083755907265677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815554756055837271510451 1223332134083755907265677)
                ·
                  refine ⟨458749550281408465224629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223332134083755907265677 458749550281408465224629)
                  ·
                    refine ⟨43007770338882043614809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458749550281408465224629 43007770338882043614809)
                    ·
                      rfl

theorem cell23_251272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_251272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251272 prefixEnd_251272 := by exact prefixLift 251272
  have htrace : WordTrace (prefixWord ++ tailWord_251272) baseStart_251272 baseEnd_251272 := by
    simpa [prefixWord, tailWord_251272, baseEnd_251272] using wordTrace_append hprefix tailTrace_251272
  have hstable : (prefixWord ++ tailWord_251272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251272).length < 2 ^ (prefixWord ++ tailWord_251272).sum := by decide
  have hdescent : baseEnd_251272 < baseStart_251272 := by decide
  rcases family_descends (prefixWord ++ tailWord_251272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251289 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 1, 5]
def baseStart_251289 : Nat := 118140960795 + 251289 * 2 ^ 59
def prefixEnd_251289 : Nat := 4983230072969 + 3 ^ 40 * 251289 * 2
def baseEnd_251289 : Nat := 43010680062590854777283

theorem tailTrace_251289 : CollatzResearch.WordTrace tailWord_251289 prefixEnd_251289 43010680062590854777283 := by
  unfold tailWord_251289
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165262786630344589532921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6110175191086896393021947 9165262786630344589532921)
  ·
    refine ⟨6873947089972758442149691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9165262786630344589532921 6873947089972758442149691)
    ·
      refine ⟨10310920634959137663224537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873947089972758442149691 10310920634959137663224537)
      ·
        refine ⟨7733190476219353247418403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10310920634959137663224537 7733190476219353247418403)
        ·
          refine ⟨11599785714329029871127605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733190476219353247418403 11599785714329029871127605)
          ·
            refine ⟨1087479910718346550418213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11599785714329029871127605 1087479910718346550418213)
            ·
              refine ⟨203902483259689978203415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1087479910718346550418213 203902483259689978203415)
              ·
                refine ⟨305853724889534967305123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203902483259689978203415 305853724889534967305123)
                ·
                  refine ⟨458780587334302450957685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305853724889534967305123 458780587334302450957685)
                  ·
                    refine ⟨43010680062590854777283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458780587334302450957685 43010680062590854777283)
                    ·
                      rfl

theorem cell23_251289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_251289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251289 prefixEnd_251289 := by exact prefixLift 251289
  have htrace : WordTrace (prefixWord ++ tailWord_251289) baseStart_251289 baseEnd_251289 := by
    simpa [prefixWord, tailWord_251289, baseEnd_251289] using wordTrace_append hprefix tailTrace_251289
  have hstable : (prefixWord ++ tailWord_251289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251289).length < 2 ^ (prefixWord ++ tailWord_251289).sum := by decide
  have hdescent : baseEnd_251289 < baseStart_251289 := by decide
  rcases family_descends (prefixWord ++ tailWord_251289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251305 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_251305 : Nat := 118140960795 + 251305 * 2 ^ 59
def prefixEnd_251305 : Nat := 4983230072969 + 3 ^ 40 * 251305 * 2
def baseEnd_251305 : Nat := 129040255878244501731775

theorem tailTrace_251305 : CollatzResearch.WordTrace tailWord_251305 prefixEnd_251305 129040255878244501731775 := by
  unfold tailWord_251305
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165846354572379322115369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6110564236381586214743579 9165846354572379322115369)
  ·
    refine ⟨6874384765929284491586527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9165846354572379322115369 6874384765929284491586527)
    ·
      refine ⟨10311577148893926737379791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874384765929284491586527 10311577148893926737379791)
      ·
        refine ⟨15467365723340890106069687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311577148893926737379791 15467365723340890106069687)
        ·
          refine ⟨23201048585011335159104531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15467365723340890106069687 23201048585011335159104531)
          ·
            refine ⟨34801572877517002738656797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23201048585011335159104531 34801572877517002738656797)
            ·
              refine ⟨13050589829068876026996299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34801572877517002738656797 13050589829068876026996299)
              ·
                refine ⟨19575884743603314040494449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050589829068876026996299 19575884743603314040494449)
                ·
                  refine ⟨14681913557702485530370837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19575884743603314040494449 14681913557702485530370837)
                  ·
                    refine ⟨688214698017304009236133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14681913557702485530370837 688214698017304009236133)
                    ·
                      refine ⟨129040255878244501731775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 688214698017304009236133 129040255878244501731775)
                      ·
                        rfl

theorem cell23_251305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_251305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251305 prefixEnd_251305 := by exact prefixLift 251305
  have htrace : WordTrace (prefixWord ++ tailWord_251305) baseStart_251305 baseEnd_251305 := by
    simpa [prefixWord, tailWord_251305, baseEnd_251305] using wordTrace_append hprefix tailTrace_251305
  have hstable : (prefixWord ++ tailWord_251305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251305).length < 2 ^ (prefixWord ++ tailWord_251305).sum := by decide
  have hdescent : baseEnd_251305 < baseStart_251305 := by decide
  rcases family_descends (prefixWord ++ tailWord_251305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251312 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_251312 : Nat := 118140960795 + 251312 * 2 ^ 59
def prefixEnd_251312 : Nat := 4983230072969 + 3 ^ 40 * 251312 * 2
def baseEnd_251312 : Nat := 129043850242825974344243

theorem tailTrace_251312 : CollatzResearch.WordTrace tailWord_251312 prefixEnd_251312 129043850242825974344243 := by
  unfold tailWord_251312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583050832773509758810095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6110734443698013011746793 4583050832773509758810095)
  ·
    refine ⟨6874576249160264638215143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583050832773509758810095 6874576249160264638215143)
    ·
      refine ⟨10311864373740396957322715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874576249160264638215143 10311864373740396957322715)
      ·
        refine ⟨15467796560610595435984073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311864373740396957322715 15467796560610595435984073)
        ·
          refine ⟨11600847420457946576988055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15467796560610595435984073 11600847420457946576988055)
          ·
            refine ⟨17401271130686919865482083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600847420457946576988055 17401271130686919865482083)
            ·
              refine ⟨26101906696030379798223125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401271130686919865482083 26101906696030379798223125)
              ·
                refine ⟨1223526876376424053041709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26101906696030379798223125 1223526876376424053041709)
                ·
                  refine ⟨458822578641159019890641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223526876376424053041709 458822578641159019890641)
                  ·
                    refine ⟨344116933980869264917981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 458822578641159019890641 344116933980869264917981)
                    ·
                      refine ⟨129043850242825974344243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344116933980869264917981 129043850242825974344243)
                      ·
                        rfl

theorem cell23_251312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_251312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251312 prefixEnd_251312 := by exact prefixLift 251312
  have htrace : WordTrace (prefixWord ++ tailWord_251312) baseStart_251312 baseEnd_251312 := by
    simpa [prefixWord, tailWord_251312, baseEnd_251312] using wordTrace_append hprefix tailTrace_251312
  have hstable : (prefixWord ++ tailWord_251312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251312).length < 2 ^ (prefixWord ++ tailWord_251312).sum := by decide
  have hdescent : baseEnd_251312 < baseStart_251312 := by decide
  rcases family_descends (prefixWord ++ tailWord_251312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251343 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 1, 2, 2]
def baseStart_251343 : Nat := 118140960795 + 251343 * 2 ^ 59
def prefixEnd_251343 : Nat := 4983230072969 + 3 ^ 40 * 251343 * 2
def baseEnd_251343 : Nat := 129059768143115353056601

theorem tailTrace_251343 : CollatzResearch.WordTrace tailWord_251343 prefixEnd_251343 129059768143115353056601 := by
  unfold tailWord_251343
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167232328434711811998683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6111488218956474541332455 9167232328434711811998683)
  ·
    refine ⟨13750848492652067717998025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9167232328434711811998683 13750848492652067717998025)
    ·
      refine ⟨10313136369489050788498519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13750848492652067717998025 10313136369489050788498519)
      ·
        refine ⟨15469704554233576182747779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10313136369489050788498519 15469704554233576182747779)
        ·
          refine ⟨23204556831350364274121669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15469704554233576182747779 23204556831350364274121669)
          ·
            refine ⟨4350854405878193301397813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23204556831350364274121669 4350854405878193301397813)
            ·
              refine ⟨407892600551080622006045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4350854405878193301397813 407892600551080622006045)
              ·
                refine ⟨152959725206655233252267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407892600551080622006045 152959725206655233252267)
                ·
                  refine ⟨229439587809982849878401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152959725206655233252267 229439587809982849878401)
                  ·
                    refine ⟨172079690857487137408801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229439587809982849878401 172079690857487137408801)
                    ·
                      refine ⟨129059768143115353056601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172079690857487137408801 129059768143115353056601)
                      ·
                        rfl

theorem cell23_251343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 2, 2].length) (baseStart_251343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251343 prefixEnd_251343 := by exact prefixLift 251343
  have htrace : WordTrace (prefixWord ++ tailWord_251343) baseStart_251343 baseEnd_251343 := by
    simpa [prefixWord, tailWord_251343, baseEnd_251343] using wordTrace_append hprefix tailTrace_251343
  have hstable : (prefixWord ++ tailWord_251343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251343).length < 2 ^ (prefixWord ++ tailWord_251343).sum := by decide
  have hdescent : baseEnd_251343 < baseStart_251343 := by decide
  rcases family_descends (prefixWord ++ tailWord_251343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251345 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_251345 : Nat := 118140960795 + 251345 * 2 ^ 59
def prefixEnd_251345 : Nat := 4983230072969 + 3 ^ 40 * 251345 * 2
def baseEnd_251345 : Nat := 43020265034808115077197

theorem tailTrace_251345 : CollatzResearch.WordTrace tailWord_251345 prefixEnd_251345 43020265034808115077197 := by
  unfold tailWord_251345
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167305274427466153571489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6111536849618310769047659 9167305274427466153571489)
  ·
    refine ⟨6875478955820599615178617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9167305274427466153571489 6875478955820599615178617)
    ·
      refine ⟨5156609216865449711383963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6875478955820599615178617 5156609216865449711383963)
      ·
        refine ⟨7734913825298174567075945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156609216865449711383963 7734913825298174567075945)
        ·
          refine ⟨5801185368973630925306959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7734913825298174567075945 5801185368973630925306959)
          ·
            refine ⟨8701778053460446387960439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801185368973630925306959 8701778053460446387960439)
            ·
              refine ⟨13052667080190669581940659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701778053460446387960439 13052667080190669581940659)
              ·
                refine ⟨19579000620286004372910989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13052667080190669581940659 19579000620286004372910989)
                ·
                  refine ⟨7342125232607251639841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19579000620286004372910989 7342125232607251639841621)
                  ·
                    refine ⟨43020265034808115077197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7342125232607251639841621 43020265034808115077197)
                    ·
                      rfl

theorem cell23_251345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_251345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251345 prefixEnd_251345 := by exact prefixLift 251345
  have htrace : WordTrace (prefixWord ++ tailWord_251345) baseStart_251345 baseEnd_251345 := by
    simpa [prefixWord, tailWord_251345, baseEnd_251345] using wordTrace_append hprefix tailTrace_251345
  have hstable : (prefixWord ++ tailWord_251345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251345).length < 2 ^ (prefixWord ++ tailWord_251345).sum := by decide
  have hdescent : baseEnd_251345 < baseStart_251345 := by decide
  rcases family_descends (prefixWord ++ tailWord_251345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251359 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 3]
def baseStart_251359 : Nat := 118140960795 + 251359 * 2 ^ 59
def prefixEnd_251359 : Nat := 4983230072969 + 3 ^ 40 * 251359 * 2
def baseEnd_251359 : Nat := 129067983833587290456527

theorem tailTrace_251359 : CollatzResearch.WordTrace tailWord_251359 prefixEnd_251359 129067983833587290456527 := by
  unfold tailWord_251359
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167815896376746544581131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6111877264251164363054087 9167815896376746544581131)
  ·
    refine ⟨13751723844565119816871697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9167815896376746544581131 13751723844565119816871697)
    ·
      refine ⟨10313792883423839862653773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13751723844565119816871697 10313792883423839862653773)
      ·
        refine ⟨3867672331283939948495165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10313792883423839862653773 3867672331283939948495165)
        ·
          refine ⟨1450377124231477480685687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3867672331283939948495165 1450377124231477480685687)
          ·
            refine ⟨2175565686347216221028531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450377124231477480685687 2175565686347216221028531)
            ·
              refine ⟨3263348529520824331542797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175565686347216221028531 3263348529520824331542797)
              ·
                refine ⟨1223755698570309124328549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263348529520824331542797 1223755698570309124328549)
                ·
                  refine ⟨229454193481932960811603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223755698570309124328549 229454193481932960811603)
                  ·
                    refine ⟨344181290222899441217405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229454193481932960811603 344181290222899441217405)
                    ·
                      refine ⟨129067983833587290456527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344181290222899441217405 129067983833587290456527)
                      ·
                        rfl

theorem cell23_251359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_251359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251359 prefixEnd_251359 := by exact prefixLift 251359
  have htrace : WordTrace (prefixWord ++ tailWord_251359) baseStart_251359 baseEnd_251359 := by
    simpa [prefixWord, tailWord_251359, baseEnd_251359] using wordTrace_append hprefix tailTrace_251359
  have hstable : (prefixWord ++ tailWord_251359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251359).length < 2 ^ (prefixWord ++ tailWord_251359).sum := by decide
  have hdescent : baseEnd_251359 < baseStart_251359 := by decide
  rcases family_descends (prefixWord ++ tailWord_251359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251370 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_251370 : Nat := 118140960795 + 251370 * 2 ^ 59
def prefixEnd_251370 : Nat := 4983230072969 + 3 ^ 40 * 251370 * 2
def baseEnd_251370 : Nat := 43024544040262249139659

theorem tailTrace_251370 : CollatzResearch.WordTrace tailWord_251370 prefixEnd_251370 43024544040262249139659 := by
  unfold tailWord_251370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292054274834223855807891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6112144732891263615487709 2292054274834223855807891)
  ·
    refine ⟨3438081412251335783711837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292054274834223855807891 3438081412251335783711837)
    ·
      refine ⟨1289280529594250918891939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3438081412251335783711837 1289280529594250918891939)
      ·
        refine ⟨1933920794391376378337909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289280529594250918891939 1933920794391376378337909)
        ·
          refine ⟨181305074474191535469179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1933920794391376378337909 181305074474191535469179)
          ·
            refine ⟨271957611711287303203769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181305074474191535469179 271957611711287303203769)
            ·
              refine ⟨203968208783465477402827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271957611711287303203769 203968208783465477402827)
              ·
                refine ⟨305952313175198216104241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203968208783465477402827 305952313175198216104241)
                ·
                  refine ⟨229464234881398662078181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305952313175198216104241 229464234881398662078181)
                  ·
                    refine ⟨43024544040262249139659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229464234881398662078181 43024544040262249139659)
                    ·
                      rfl

theorem cell23_251370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_251370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251370 prefixEnd_251370 := by exact prefixLift 251370
  have htrace : WordTrace (prefixWord ++ tailWord_251370) baseStart_251370 baseEnd_251370 := by
    simpa [prefixWord, tailWord_251370, baseEnd_251370] using wordTrace_append hprefix tailTrace_251370
  have hstable : (prefixWord ++ tailWord_251370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251370).length < 2 ^ (prefixWord ++ tailWord_251370).sum := by decide
  have hdescent : baseEnd_251370 < baseStart_251370 := by decide
  rcases family_descends (prefixWord ++ tailWord_251370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251376 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3]
def baseStart_251376 : Nat := 118140960795 + 251376 * 2 ^ 59
def prefixEnd_251376 : Nat := 4983230072969 + 3 ^ 40 * 251376 * 2
def baseEnd_251376 : Nat := 129076713004713723943949

theorem tailTrace_251376 : CollatzResearch.WordTrace tailWord_251376 prefixEnd_251376 129076713004713723943949 := by
  unfold tailWord_251376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584217968657579223974991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6112290624876772298633321 4584217968657579223974991)
  ·
    refine ⟨6876326952986368835962487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4584217968657579223974991 6876326952986368835962487)
    ·
      refine ⟨10314490429479553253943731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6876326952986368835962487 10314490429479553253943731)
      ·
        refine ⟨15471735644219329880915597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10314490429479553253943731 15471735644219329880915597)
        ·
          refine ⟨5801900866582248705343349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15471735644219329880915597 5801900866582248705343349)
          ·
            refine ⟨543928206242085816125939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5801900866582248705343349 543928206242085816125939)
            ·
              refine ⟨815892309363128724188909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543928206242085816125939 815892309363128724188909)
              ·
                refine ⟨305959616011173271570841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815892309363128724188909 305959616011173271570841)
                ·
                  refine ⟨229469712008379953678131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305959616011173271570841 229469712008379953678131)
                  ·
                    refine ⟨344204568012569930517197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229469712008379953678131 344204568012569930517197)
                    ·
                      refine ⟨129076713004713723943949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344204568012569930517197 129076713004713723943949)
                      ·
                        rfl

theorem cell23_251376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_251376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251376 prefixEnd_251376 := by exact prefixLift 251376
  have htrace : WordTrace (prefixWord ++ tailWord_251376) baseStart_251376 baseEnd_251376 := by
    simpa [prefixWord, tailWord_251376, baseEnd_251376] using wordTrace_append hprefix tailTrace_251376
  have hstable : (prefixWord ++ tailWord_251376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251376).length < 2 ^ (prefixWord ++ tailWord_251376).sum := by decide
  have hdescent : baseEnd_251376 < baseStart_251376 := by decide
  rcases family_descends (prefixWord ++ tailWord_251376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251599 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_251599 : Nat := 118140960795 + 251599 * 2 ^ 59
def prefixEnd_251599 : Nat := 4983230072969 + 3 ^ 40 * 251599 * 2
def baseEnd_251599 : Nat := 129191219190666351455423

theorem tailTrace_251599 : CollatzResearch.WordTrace tailWord_251599 prefixEnd_251599 129191219190666351455423 := by
  unfold tailWord_251599
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176569415507267533317851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6117712943671511688878567 9176569415507267533317851)
  ·
    refine ⟨13764854123260901299976777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176569415507267533317851 13764854123260901299976777)
    ·
      refine ⟨10323640592445675974982583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13764854123260901299976777 10323640592445675974982583)
      ·
        refine ⟨15485460888668513962473875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10323640592445675974982583 15485460888668513962473875)
        ·
          refine ⟨23228191333002770943710813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15485460888668513962473875 23228191333002770943710813)
          ·
            refine ⟨8710571749876039103891555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23228191333002770943710813 8710571749876039103891555)
            ·
              refine ⟨13065857624814058655837333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710571749876039103891555 13065857624814058655837333)
              ·
                refine ⟨612462076163158999492375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13065857624814058655837333 612462076163158999492375)
                ·
                  refine ⟨918693114244738499238563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612462076163158999492375 918693114244738499238563)
                  ·
                    refine ⟨1378039671367107748857845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 918693114244738499238563 1378039671367107748857845)
                    ·
                      refine ⟨129191219190666351455423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1378039671367107748857845 129191219190666351455423)
                      ·
                        rfl

theorem cell23_251599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_251599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251599 prefixEnd_251599 := by exact prefixLift 251599
  have htrace : WordTrace (prefixWord ++ tailWord_251599) baseStart_251599 baseEnd_251599 := by
    simpa [prefixWord, tailWord_251599, baseEnd_251599] using wordTrace_append hprefix tailTrace_251599
  have hstable : (prefixWord ++ tailWord_251599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251599).length < 2 ^ (prefixWord ++ tailWord_251599).sum := by decide
  have hdescent : baseEnd_251599 < baseStart_251599 := by decide
  rcases family_descends (prefixWord ++ tailWord_251599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251616 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_251616 : Nat := 118140960795 + 251616 * 2 ^ 59
def prefixEnd_251616 : Nat := 4983230072969 + 3 ^ 40 * 251616 * 2
def baseEnd_251616 : Nat := 129199948361792784942845

theorem tailTrace_251616 : CollatzResearch.WordTrace tailWord_251616 prefixEnd_251616 129199948361792784942845 := by
  unfold tailWord_251616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588594728222839718343351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6118126304297119624457801 4588594728222839718343351)
  ·
    refine ⟨6882892092334259577515027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4588594728222839718343351 6882892092334259577515027)
    ·
      refine ⟨10324338138501389366272541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6882892092334259577515027 10324338138501389366272541)
      ·
        refine ⟨3871626801938021012352203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10324338138501389366272541 3871626801938021012352203)
        ·
          refine ⟨5807440202907031518528305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871626801938021012352203 5807440202907031518528305)
          ·
            refine ⟨4355580152180273638896229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5807440202907031518528305 4355580152180273638896229)
            ·
              refine ⟨816671278533801307293043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4355580152180273638896229 816671278533801307293043)
              ·
                refine ⟨1225006917800701960939565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816671278533801307293043 1225006917800701960939565)
                ·
                  refine ⟨459377594175263235352337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225006917800701960939565 459377594175263235352337)
                  ·
                    refine ⟨344533195631447426514253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459377594175263235352337 344533195631447426514253)
                    ·
                      refine ⟨129199948361792784942845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344533195631447426514253 129199948361792784942845)
                      ·
                        rfl

theorem cell23_251616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_251616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251616 prefixEnd_251616 := by exact prefixLift 251616
  have htrace : WordTrace (prefixWord ++ tailWord_251616) baseStart_251616 baseEnd_251616 := by
    simpa [prefixWord, tailWord_251616, baseEnd_251616] using wordTrace_append hprefix tailTrace_251616
  have hstable : (prefixWord ++ tailWord_251616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251616).length < 2 ^ (prefixWord ++ tailWord_251616).sum := by decide
  have hdescent : baseEnd_251616 < baseStart_251616 := by decide
  rcases family_descends (prefixWord ++ tailWord_251616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251617 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_251617 : Nat := 118140960795 + 251617 * 2 ^ 59
def prefixEnd_251617 : Nat := 4983230072969 + 3 ^ 40 * 251617 * 2
def baseEnd_251617 : Nat := 129200461842447281030341

theorem tailTrace_251617 : CollatzResearch.WordTrace tailWord_251617 prefixEnd_251617 129200461842447281030341 := by
  unfold tailWord_251617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177225929442056607473105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6118150619628037738315403 9177225929442056607473105)
  ·
    refine ⟨6882919447081542455604829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9177225929442056607473105 6882919447081542455604829)
    ·
      refine ⟨2581094792655578420851811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6882919447081542455604829 2581094792655578420851811)
      ·
        refine ⟨3871642188983367631277717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581094792655578420851811 3871642188983367631277717)
        ·
          refine ⟨181483227608595357716143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3871642188983367631277717 181483227608595357716143)
          ·
            refine ⟨272224841412893036574215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181483227608595357716143 272224841412893036574215)
            ·
              refine ⟨408337262119339554861323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272224841412893036574215 408337262119339554861323)
              ·
                refine ⟨612505893179009332291985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408337262119339554861323 612505893179009332291985)
                ·
                  refine ⟨459379419884256999218989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612505893179009332291985 459379419884256999218989)
                  ·
                    refine ⟨172267282456596374707121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459379419884256999218989 172267282456596374707121)
                    ·
                      refine ⟨129200461842447281030341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172267282456596374707121 129200461842447281030341)
                      ·
                        rfl

theorem cell23_251617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_251617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251617 prefixEnd_251617 := by exact prefixLift 251617
  have htrace : WordTrace (prefixWord ++ tailWord_251617) baseStart_251617 baseEnd_251617 := by
    simpa [prefixWord, tailWord_251617, baseEnd_251617] using wordTrace_append hprefix tailTrace_251617
  have hstable : (prefixWord ++ tailWord_251617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251617).length < 2 ^ (prefixWord ++ tailWord_251617).sum := by decide
  have hdescent : baseEnd_251617 < baseStart_251617 := by decide
  rcases family_descends (prefixWord ++ tailWord_251617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251626 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_251626 : Nat := 118140960795 + 251626 * 2 ^ 59
def prefixEnd_251626 : Nat := 4983230072969 + 3 ^ 40 * 251626 * 2
def baseEnd_251626 : Nat := 129205083168337745817799

theorem tailTrace_251626 : CollatzResearch.WordTrace tailWord_251626 prefixEnd_251626 129205083168337745817799 := by
  unfold tailWord_251626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294388546602362786137683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6118369457606300763033821 2294388546602362786137683)
  ·
    refine ⟨3441582819903544179206525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294388546602362786137683 3441582819903544179206525)
    ·
      refine ⟨1290593557463829067202447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3441582819903544179206525 1290593557463829067202447)
      ·
        refine ⟨1935890336195743600803671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290593557463829067202447 1935890336195743600803671)
        ·
          refine ⟨2903835504293615401205507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935890336195743600803671 2903835504293615401205507)
          ·
            refine ⟨4355753256440423101808261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903835504293615401205507 4355753256440423101808261)
            ·
              refine ⟨816703735582579331589049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4355753256440423101808261 816703735582579331589049)
              ·
                refine ⟨612527801686934498691787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816703735582579331589049 612527801686934498691787)
                ·
                  refine ⟨918791702530401748037681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612527801686934498691787 918791702530401748037681)
                  ·
                    refine ⟨689093776897801311028261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 918791702530401748037681 689093776897801311028261)
                    ·
                      refine ⟨129205083168337745817799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 689093776897801311028261 129205083168337745817799)
                      ·
                        rfl

theorem cell23_251626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_251626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251626 prefixEnd_251626 := by exact prefixLift 251626
  have htrace : WordTrace (prefixWord ++ tailWord_251626) baseStart_251626 baseEnd_251626 := by
    simpa [prefixWord, tailWord_251626, baseEnd_251626] using wordTrace_append hprefix tailTrace_251626
  have hstable : (prefixWord ++ tailWord_251626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251626).length < 2 ^ (prefixWord ++ tailWord_251626).sum := by decide
  have hdescent : baseEnd_251626 < baseStart_251626 := by decide
  rcases family_descends (prefixWord ++ tailWord_251626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251633 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_251633 : Nat := 118140960795 + 251633 * 2 ^ 59
def prefixEnd_251633 : Nat := 4983230072969 + 3 ^ 40 * 251633 * 2
def baseEnd_251633 : Nat := 129208677532919218430267

theorem tailTrace_251633 : CollatzResearch.WordTrace tailWord_251633 prefixEnd_251633 129208677532919218430267 := by
  unfold tailWord_251633
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177809497384091340055553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6118539664922727560037035 9177809497384091340055553)
  ·
    refine ⟨6883357123038068505041665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9177809497384091340055553 6883357123038068505041665)
    ·
      refine ⟨5162517842278551378781249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6883357123038068505041665 5162517842278551378781249)
      ·
        refine ⟨3871888381708913534085937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5162517842278551378781249 3871888381708913534085937)
        ·
          refine ⟨2903916286281685150564453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3871888381708913534085937 2903916286281685150564453)
          ·
            refine ⟨544484303677815965730835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2903916286281685150564453 544484303677815965730835)
            ·
              refine ⟨816726455516723948596253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544484303677815965730835 816726455516723948596253)
              ·
                refine ⟨306272420818771480723595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 816726455516723948596253 306272420818771480723595)
                ·
                  refine ⟨459408631228157221085393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306272420818771480723595 459408631228157221085393)
                  ·
                    refine ⟨344556473421117915814045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459408631228157221085393 344556473421117915814045)
                    ·
                      refine ⟨129208677532919218430267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344556473421117915814045 129208677532919218430267)
                      ·
                        rfl

theorem cell23_251633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_251633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251633 prefixEnd_251633 := by exact prefixLift 251633
  have htrace : WordTrace (prefixWord ++ tailWord_251633) baseStart_251633 baseEnd_251633 := by
    simpa [prefixWord, tailWord_251633, baseEnd_251633] using wordTrace_append hprefix tailTrace_251633
  have hstable : (prefixWord ++ tailWord_251633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251633).length < 2 ^ (prefixWord ++ tailWord_251633).sum := by decide
  have hdescent : baseEnd_251633 < baseStart_251633 := by decide
  rcases family_descends (prefixWord ++ tailWord_251633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251649 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_251649 : Nat := 118140960795 + 251649 * 2 ^ 59
def prefixEnd_251649 : Nat := 4983230072969 + 3 ^ 40 * 251649 * 2
def baseEnd_251649 : Nat := 43072297741130385276731

theorem tailTrace_251649 : CollatzResearch.WordTrace tailWord_251649 prefixEnd_251649 43072297741130385276731 := by
  unfold tailWord_251649
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178393065326126072638001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6118928710217417381758667 9178393065326126072638001)
  ·
    refine ⟨6883794798994594554478501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9178393065326126072638001 6883794798994594554478501)
    ·
      refine ⟨1290711524811486478964719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6883794798994594554478501 1290711524811486478964719)
      ·
        refine ⟨1936067287217229718447079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290711524811486478964719 1936067287217229718447079)
        ·
          refine ⟨2904100930825844577670619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936067287217229718447079 2904100930825844577670619)
          ·
            refine ⟨4356151396238766866505929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904100930825844577670619 4356151396238766866505929)
            ·
              refine ⟨3267113547179075149879447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356151396238766866505929 3267113547179075149879447)
              ·
                refine ⟨4900670320768612724819171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267113547179075149879447 4900670320768612724819171)
                ·
                  refine ⟨7351005481152919087228757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900670320768612724819171 7351005481152919087228757)
                  ·
                    refine ⟨43072297741130385276731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7351005481152919087228757 43072297741130385276731)
                    ·
                      rfl

theorem cell23_251649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_251649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251649 prefixEnd_251649 := by exact prefixLift 251649
  have htrace : WordTrace (prefixWord ++ tailWord_251649) baseStart_251649 baseEnd_251649 := by
    simpa [prefixWord, tailWord_251649, baseEnd_251649] using wordTrace_append hprefix tailTrace_251649
  have hstable : (prefixWord ++ tailWord_251649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251649).length < 2 ^ (prefixWord ++ tailWord_251649).sum := by decide
  have hdescent : baseEnd_251649 < baseStart_251649 := by decide
  rcases family_descends (prefixWord ++ tailWord_251649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251724 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_251724 : Nat := 118140960795 + 251724 * 2 ^ 59
def prefixEnd_251724 : Nat := 4983230072969 + 3 ^ 40 * 251724 * 2
def baseEnd_251724 : Nat := 129255404272478362392349

theorem tailTrace_251724 : CollatzResearch.WordTrace tailWord_251724 prefixEnd_251724 129255404272478362392349 := by
  unfold tailWord_251724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590564270027206940809113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6120752360036275921078817 4590564270027206940809113)
  ·
    refine ⟨3442923202520405205606835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4590564270027206940809113 3442923202520405205606835)
    ·
      refine ⟨5164384803780607808410253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442923202520405205606835 5164384803780607808410253)
      ·
        refine ⟨1936644301417727928153845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5164384803780607808410253 1936644301417727928153845)
        ·
          refine ⟨181560403257911993264423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1936644301417727928153845 181560403257911993264423)
          ·
            refine ⟨272340604886867989896635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181560403257911993264423 272340604886867989896635)
            ·
              refine ⟨408510907330301984844953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272340604886867989896635 408510907330301984844953)
              ·
                refine ⟨306383180497726488633715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408510907330301984844953 306383180497726488633715)
                ·
                  refine ⟨459574770746589732950573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306383180497726488633715 459574770746589732950573)
                  ·
                    refine ⟨172340539029971149856465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459574770746589732950573 172340539029971149856465)
                    ·
                      refine ⟨129255404272478362392349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172340539029971149856465 129255404272478362392349)
                      ·
                        rfl

theorem cell23_251724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_251724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251724 prefixEnd_251724 := by exact prefixLift 251724
  have htrace : WordTrace (prefixWord ++ tailWord_251724) baseStart_251724 baseEnd_251724 := by
    simpa [prefixWord, tailWord_251724, baseEnd_251724] using wordTrace_append hprefix tailTrace_251724
  have hstable : (prefixWord ++ tailWord_251724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251724).length < 2 ^ (prefixWord ++ tailWord_251724).sum := by decide
  have hdescent : baseEnd_251724 < baseStart_251724 := by decide
  rcases family_descends (prefixWord ++ tailWord_251724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251736 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_251736 : Nat := 118140960795 + 251736 * 2 ^ 59
def prefixEnd_251736 : Nat := 4983230072969 + 3 ^ 40 * 251736 * 2
def baseEnd_251736 : Nat := 129261566040332315442293

theorem tailTrace_251736 : CollatzResearch.WordTrace tailWord_251736 prefixEnd_251736 129261566040332315442293 := by
  unfold tailWord_251736
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590783108005469965527531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6121044144007293287370041 4590783108005469965527531)
  ·
    refine ⟨6886174662008204948291297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4590783108005469965527531 6886174662008204948291297)
    ·
      refine ⟨5164630996506153711218473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6886174662008204948291297 5164630996506153711218473)
      ·
        refine ⟨3873473247379615283413855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5164630996506153711218473 3873473247379615283413855)
        ·
          refine ⟨5810209871069422925120783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873473247379615283413855 5810209871069422925120783)
          ·
            refine ⟨8715314806604134387681175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810209871069422925120783 8715314806604134387681175)
            ·
              refine ⟨13072972209906201581521763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715314806604134387681175 13072972209906201581521763)
              ·
                refine ⟨19609458314859302372282645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072972209906201581521763 19609458314859302372282645)
                ·
                  refine ⟨919193358509029798700749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19609458314859302372282645 919193358509029798700749)
                  ·
                    refine ⟨344697509440886174512781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919193358509029798700749 344697509440886174512781)
                    ·
                      refine ⟨129261566040332315442293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344697509440886174512781 129261566040332315442293)
                      ·
                        rfl

theorem cell23_251736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_251736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251736 prefixEnd_251736 := by exact prefixLift 251736
  have htrace : WordTrace (prefixWord ++ tailWord_251736) baseStart_251736 baseEnd_251736 := by
    simpa [prefixWord, tailWord_251736, baseEnd_251736] using wordTrace_append hprefix tailTrace_251736
  have hstable : (prefixWord ++ tailWord_251736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251736).length < 2 ^ (prefixWord ++ tailWord_251736).sum := by decide
  have hdescent : baseEnd_251736 < baseStart_251736 := by decide
  rcases family_descends (prefixWord ++ tailWord_251736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251776 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_251776 : Nat := 118140960795 + 251776 * 2 ^ 59
def prefixEnd_251776 : Nat := 4983230072969 + 3 ^ 40 * 251776 * 2
def baseEnd_251776 : Nat := 129282105266512158942109

theorem tailTrace_251776 : CollatzResearch.WordTrace tailWord_251776 prefixEnd_251776 129282105266512158942109 := by
  unfold tailWord_251776
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591512567933013381255591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6122016757244017841674121 4591512567933013381255591)
  ·
    refine ⟨6887268851899520071883387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591512567933013381255591 6887268851899520071883387)
    ·
      refine ⟨10330903277849280107825081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887268851899520071883387 10330903277849280107825081)
      ·
        refine ⟨7748177458386960080868811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10330903277849280107825081 7748177458386960080868811)
        ·
          refine ⟨11622266187580440121303217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748177458386960080868811 11622266187580440121303217)
          ·
            refine ⟨8716699640685330090977413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11622266187580440121303217 8716699640685330090977413)
            ·
              refine ⟨1634381182628499392058265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8716699640685330090977413 1634381182628499392058265)
              ·
                refine ⟨1225785886971374544043699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634381182628499392058265 1225785886971374544043699)
                ·
                  refine ⟨1838678830457061816065549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225785886971374544043699 1838678830457061816065549)
                  ·
                    refine ⟨689504561421398181024581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838678830457061816065549 689504561421398181024581)
                    ·
                      refine ⟨129282105266512158942109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 689504561421398181024581 129282105266512158942109)
                      ·
                        rfl

theorem cell23_251776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_251776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251776 prefixEnd_251776 := by exact prefixLift 251776
  have htrace : WordTrace (prefixWord ++ tailWord_251776) baseStart_251776 baseEnd_251776 := by
    simpa [prefixWord, tailWord_251776, baseEnd_251776] using wordTrace_append hprefix tailTrace_251776
  have hstable : (prefixWord ++ tailWord_251776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251776).length < 2 ^ (prefixWord ++ tailWord_251776).sum := by decide
  have hdescent : baseEnd_251776 < baseStart_251776 := by decide
  rcases family_descends (prefixWord ++ tailWord_251776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251790 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_251790 : Nat := 118140960795 + 251790 * 2 ^ 59
def prefixEnd_251790 : Nat := 4983230072969 + 3 ^ 40 * 251790 * 2
def baseEnd_251790 : Nat := 43096431331891701389015

theorem tailTrace_251790 : CollatzResearch.WordTrace tailWord_251790 prefixEnd_251790 43096431331891701389015 := by
  unfold tailWord_251790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147941969726913394190103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6122357171876871435680549 1147941969726913394190103)
  ·
    refine ⟨1721912954590370091285155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147941969726913394190103 1721912954590370091285155)
    ·
      refine ⟨2582869431885555136927733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721912954590370091285155 2582869431885555136927733)
      ·
        refine ⟨242144009239270794086975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2582869431885555136927733 242144009239270794086975)
        ·
          refine ⟨363216013858906191130463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242144009239270794086975 363216013858906191130463)
          ·
            refine ⟨544824020788359286695695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363216013858906191130463 544824020788359286695695)
            ·
              refine ⟨817236031182538930043543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544824020788359286695695 817236031182538930043543)
              ·
                refine ⟨1225854046773808395065315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817236031182538930043543 1225854046773808395065315)
                ·
                  refine ⟨1838781070160712592597973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225854046773808395065315 1838781070160712592597973)
                  ·
                    refine ⟨43096431331891701389015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1838781070160712592597973 43096431331891701389015)
                    ·
                      rfl

theorem cell23_251790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_251790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251790 prefixEnd_251790 := by exact prefixLift 251790
  have htrace : WordTrace (prefixWord ++ tailWord_251790) baseStart_251790 baseEnd_251790 := by
    simpa [prefixWord, tailWord_251790, baseEnd_251790] using wordTrace_append hprefix tailTrace_251790
  have hstable : (prefixWord ++ tailWord_251790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251790).length < 2 ^ (prefixWord ++ tailWord_251790).sum := by decide
  have hdescent : baseEnd_251790 < baseStart_251790 := by decide
  rcases family_descends (prefixWord ++ tailWord_251790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251793 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_251793 : Nat := 118140960795 + 251793 * 2 ^ 59
def prefixEnd_251793 : Nat := 4983230072969 + 3 ^ 40 * 251793 * 2
def baseEnd_251793 : Nat := 129290834437638592429531

theorem tailTrace_251793 : CollatzResearch.WordTrace tailWord_251793 prefixEnd_251793 129290834437638592429531 := by
  unfold tailWord_251793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183645176804438665880033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6122430117869625777253355 9183645176804438665880033)
  ·
    refine ⟨6887733882603328999410025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9183645176804438665880033 6887733882603328999410025)
    ·
      refine ⟨5165800411952496749557519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6887733882603328999410025 5165800411952496749557519)
      ·
        refine ⟨7748700617928745124336279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165800411952496749557519 7748700617928745124336279)
        ·
          refine ⟨11623050926893117686504419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748700617928745124336279 11623050926893117686504419)
          ·
            refine ⟨17434576390339676529756629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623050926893117686504419 17434576390339676529756629)
            ·
              refine ⟨408622884148586168666171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17434576390339676529756629 408622884148586168666171)
              ·
                refine ⟨612934326222879252999257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408622884148586168666171 612934326222879252999257)
                ·
                  refine ⟨459700744667159439749443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612934326222879252999257 459700744667159439749443)
                  ·
                    refine ⟨689551117000739159624165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 459700744667159439749443 689551117000739159624165)
                    ·
                      refine ⟨129290834437638592429531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 689551117000739159624165 129290834437638592429531)
                      ·
                        rfl

theorem cell23_251793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_251793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251793 prefixEnd_251793 := by exact prefixLift 251793
  have htrace : WordTrace (prefixWord ++ tailWord_251793) baseStart_251793 baseEnd_251793 := by
    simpa [prefixWord, tailWord_251793, baseEnd_251793] using wordTrace_append hprefix tailTrace_251793
  have hstable : (prefixWord ++ tailWord_251793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251793).length < 2 ^ (prefixWord ++ tailWord_251793).sum := by decide
  have hdescent : baseEnd_251793 < baseStart_251793 := by decide
  rcases family_descends (prefixWord ++ tailWord_251793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251813 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_251813 : Nat := 118140960795 + 251813 * 2 ^ 59
def prefixEnd_251813 : Nat := 4983230072969 + 3 ^ 40 * 251813 * 2
def baseEnd_251813 : Nat := 129301104050728514179439

theorem tailTrace_251813 : CollatzResearch.WordTrace tailWord_251813 prefixEnd_251813 129301104050728514179439 := by
  unfold tailWord_251813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9184374636731982081608093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6122916424487988054405395 9184374636731982081608093)
  ·
    refine ⟨3444140488774493280603035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9184374636731982081608093 3444140488774493280603035)
    ·
      refine ⟨5166210733161739920904553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3444140488774493280603035 5166210733161739920904553)
      ·
        refine ⟨3874658049871304940678415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5166210733161739920904553 3874658049871304940678415)
        ·
          refine ⟨5811987074806957411017623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874658049871304940678415 5811987074806957411017623)
          ·
            refine ⟨8717980612210436116526435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811987074806957411017623 8717980612210436116526435)
            ·
              refine ⟨13076970918315654174789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717980612210436116526435 13076970918315654174789653)
              ·
                refine ⟨612983011796046289443265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13076970918315654174789653 612983011796046289443265)
                ·
                  refine ⟨459737258847034717082449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612983011796046289443265 459737258847034717082449)
                  ·
                    refine ⟨344802944135276037811837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459737258847034717082449 344802944135276037811837)
                    ·
                      refine ⟨129301104050728514179439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 344802944135276037811837 129301104050728514179439)
                      ·
                        rfl

theorem cell23_251813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_251813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251813 prefixEnd_251813 := by exact prefixLift 251813
  have htrace : WordTrace (prefixWord ++ tailWord_251813) baseStart_251813 baseEnd_251813 := by
    simpa [prefixWord, tailWord_251813, baseEnd_251813] using wordTrace_append hprefix tailTrace_251813
  have hstable : (prefixWord ++ tailWord_251813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251813).length < 2 ^ (prefixWord ++ tailWord_251813).sum := by decide
  have hdescent : baseEnd_251813 < baseStart_251813 := by decide
  rcases family_descends (prefixWord ++ tailWord_251813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251863 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 1, 5]
def baseStart_251863 : Nat := 118140960795 + 251863 * 2 ^ 59
def prefixEnd_251863 : Nat := 4983230072969 + 3 ^ 40 * 251863 * 2
def baseEnd_251863 : Nat := 43108926027817772851403

theorem tailTrace_251863 : CollatzResearch.WordTrace tailWord_251863 prefixEnd_251863 43108926027817772851403 := by
  unfold tailWord_251863
  simp only [CollatzResearch.WordTrace]
  refine ⟨9186198286550840620928243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6124132191033893747285495 9186198286550840620928243)
  ·
    refine ⟨13779297429826260931392365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9186198286550840620928243 13779297429826260931392365)
    ·
      refine ⟨5167236536184847849272137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13779297429826260931392365 5167236536184847849272137)
      ·
        refine ⟨3875427402138635886954103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5167236536184847849272137 3875427402138635886954103)
        ·
          refine ⟨5813141103207953830431155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875427402138635886954103 5813141103207953830431155)
          ·
            refine ⟨8719711654811930745646733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813141103207953830431155 8719711654811930745646733)
            ·
              refine ⟨3269891870554474029617525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8719711654811930745646733 3269891870554474029617525)
              ·
                refine ⟨306552362864481940276643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3269891870554474029617525 306552362864481940276643)
                ·
                  refine ⟨459828544296722910414965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306552362864481940276643 459828544296722910414965)
                  ·
                    refine ⟨43108926027817772851403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 459828544296722910414965 43108926027817772851403)
                    ·
                      rfl

theorem cell23_251863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_251863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251863 prefixEnd_251863 := by exact prefixLift 251863
  have htrace : WordTrace (prefixWord ++ tailWord_251863) baseStart_251863 baseEnd_251863 := by
    simpa [prefixWord, tailWord_251863, baseEnd_251863] using wordTrace_append hprefix tailTrace_251863
  have hstable : (prefixWord ++ tailWord_251863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251863).length < 2 ^ (prefixWord ++ tailWord_251863).sum := by decide
  have hdescent : baseEnd_251863 < baseStart_251863 := by decide
  rcases family_descends (prefixWord ++ tailWord_251863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251977 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 1, 3, 2]
def baseStart_251977 : Nat := 118140960795 + 251977 * 2 ^ 59
def prefixEnd_251977 : Nat := 4983230072969 + 3 ^ 40 * 251977 * 2
def baseEnd_251977 : Nat := 129385314878065872528685

theorem tailTrace_251977 : CollatzResearch.WordTrace tailWord_251977 prefixEnd_251977 129385314878065872528685 := by
  unfold tailWord_251977
  simp only [CollatzResearch.WordTrace]
  refine ⟨9190356208137838090578185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6126904138758558727052123 9190356208137838090578185)
  ·
    refine ⟨6892767156103378567933639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9190356208137838090578185 6892767156103378567933639)
    ·
      refine ⟨10339150734155067851900459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6892767156103378567933639 10339150734155067851900459)
      ·
        refine ⟨15508726101232601777850689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10339150734155067851900459 15508726101232601777850689)
        ·
          refine ⟨11631544575924451333388017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15508726101232601777850689 11631544575924451333388017)
          ·
            refine ⟨8723658431943338500041013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631544575924451333388017 8723658431943338500041013)
            ·
              refine ⟨817842977994687984378845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8723658431943338500041013 817842977994687984378845)
              ·
                refine ⟨306691116748007994142067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 817842977994687984378845 306691116748007994142067)
                ·
                  refine ⟨460036675122011991213101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306691116748007994142067 460036675122011991213101)
                  ·
                    refine ⟨172513753170754496704913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460036675122011991213101 172513753170754496704913)
                    ·
                      refine ⟨129385314878065872528685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172513753170754496704913 129385314878065872528685)
                      ·
                        rfl

theorem cell23_251977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3, 2].length) (baseStart_251977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251977 prefixEnd_251977 := by exact prefixLift 251977
  have htrace : WordTrace (prefixWord ++ tailWord_251977) baseStart_251977 baseEnd_251977 := by
    simpa [prefixWord, tailWord_251977, baseEnd_251977] using wordTrace_append hprefix tailTrace_251977
  have hstable : (prefixWord ++ tailWord_251977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251977).length < 2 ^ (prefixWord ++ tailWord_251977).sum := by decide
  have hdescent : baseEnd_251977 < baseStart_251977 := by decide
  rcases family_descends (prefixWord ++ tailWord_251977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251998 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_251998 : Nat := 118140960795 + 251998 * 2 ^ 59
def prefixEnd_251998 : Nat := 4983230072969 + 3 ^ 40 * 251998 * 2
def baseEnd_251998 : Nat := 129396097971810290366089

theorem tailTrace_251998 : CollatzResearch.WordTrace tailWord_251998 prefixEnd_251998 129396097971810290366089 := by
  unfold tailWord_251998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148890267632719834636581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6127414760707839118061765 1148890267632719834636581)
  ·
    refine ⟨215416925181134968994359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1148890267632719834636581 215416925181134968994359)
    ·
      refine ⟨323125387771702453491539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215416925181134968994359 323125387771702453491539)
      ·
        refine ⟨484688081657553680237309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323125387771702453491539 484688081657553680237309)
        ·
          refine ⟨181758030621582630088991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484688081657553680237309 181758030621582630088991)
          ·
            refine ⟨272637045932373945133487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181758030621582630088991 272637045932373945133487)
            ·
              refine ⟨408955568898560917700231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272637045932373945133487 408955568898560917700231)
              ·
                refine ⟨613433353347841376550347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408955568898560917700231 613433353347841376550347)
                ·
                  refine ⟨920150030021762064825521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613433353347841376550347 920150030021762064825521)
                  ·
                    refine ⟨690112522516321548619141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 920150030021762064825521 690112522516321548619141)
                    ·
                      refine ⟨129396097971810290366089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 690112522516321548619141 129396097971810290366089)
                      ·
                        rfl

theorem cell23_251998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_251998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_251998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_251998 prefixEnd_251998 := by exact prefixLift 251998
  have htrace : WordTrace (prefixWord ++ tailWord_251998) baseStart_251998 baseEnd_251998 := by
    simpa [prefixWord, tailWord_251998, baseEnd_251998] using wordTrace_append hprefix tailTrace_251998
  have hstable : (prefixWord ++ tailWord_251998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251998).length < 2 ^ (prefixWord ++ tailWord_251998).sum := by decide
  have hdescent : baseEnd_251998 < baseStart_251998 := by decide
  rcases family_descends (prefixWord ++ tailWord_251998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252060 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_252060 : Nat := 118140960795 + 252060 * 2 ^ 59
def prefixEnd_252060 : Nat := 4983230072969 + 3 ^ 40 * 252060 * 2
def baseEnd_252060 : Nat := 43142644590796349263601

theorem tailTrace_252060 : CollatzResearch.WordTrace tailWord_252060 prefixEnd_252060 43142644590796349263601 := by
  unfold tailWord_252060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596691733418571632924817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6128922311224762177233089 4596691733418571632924817)
  ·
    refine ⟨3447518800063928724693613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4596691733418571632924817 3447518800063928724693613)
    ·
      refine ⟨1292819550023973271760105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3447518800063928724693613 1292819550023973271760105)
      ·
        refine ⟨969614662517979953820079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292819550023973271760105 969614662517979953820079)
        ·
          refine ⟨1454421993776969930730119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969614662517979953820079 1454421993776969930730119)
          ·
            refine ⟨2181632990665454896095179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454421993776969930730119 2181632990665454896095179)
            ·
              refine ⟨3272449485998182344142769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181632990665454896095179 3272449485998182344142769)
              ·
                refine ⟨2454337114498636758107077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272449485998182344142769 2454337114498636758107077)
                ·
                  refine ⟨460188208968494392145077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454337114498636758107077 460188208968494392145077)
                  ·
                    refine ⟨43142644590796349263601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 460188208968494392145077 43142644590796349263601)
                    ·
                      rfl

theorem cell23_252060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_252060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252060 prefixEnd_252060 := by exact prefixLift 252060
  have htrace : WordTrace (prefixWord ++ tailWord_252060) baseStart_252060 baseEnd_252060 := by
    simpa [prefixWord, tailWord_252060, baseEnd_252060] using wordTrace_append hprefix tailTrace_252060
  have hstable : (prefixWord ++ tailWord_252060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252060).length < 2 ^ (prefixWord ++ tailWord_252060).sum := by decide
  have hdescent : baseEnd_252060 < baseStart_252060 := by decide
  rcases family_descends (prefixWord ++ tailWord_252060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252077 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_252077 : Nat := 118140960795 + 252077 * 2 ^ 59
def prefixEnd_252077 : Nat := 4983230072969 + 3 ^ 40 * 252077 * 2
def baseEnd_252077 : Nat := 43145554314505160426075

theorem tailTrace_252077 : CollatzResearch.WordTrace tailWord_252077 prefixEnd_252077 43145554314505160426075 := by
  unfold tailWord_252077
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194003507775555169218485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6129335671850370112812323 9194003507775555169218485)
  ·
    refine ⟨861937828853958297114233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9194003507775555169218485 861937828853958297114233)
    ·
      refine ⟨646453371640468722835675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861937828853958297114233 646453371640468722835675)
      ·
        refine ⟨969680057460703084253513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646453371640468722835675 969680057460703084253513)
        ·
          refine ⟨727260043095527313190135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969680057460703084253513 727260043095527313190135)
          ·
            refine ⟨1090890064643290969785203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727260043095527313190135 1090890064643290969785203)
            ·
              refine ⟨1636335096964936454677805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090890064643290969785203 1636335096964936454677805)
              ·
                refine ⟨613625661361851170504177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1636335096964936454677805 613625661361851170504177)
                ·
                  refine ⟨460219246021388377878133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613625661361851170504177 460219246021388377878133)
                  ·
                    refine ⟨43145554314505160426075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 460219246021388377878133 43145554314505160426075)
                    ·
                      rfl

theorem cell23_252077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_252077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252077 prefixEnd_252077 := by exact prefixLift 252077
  have htrace : WordTrace (prefixWord ++ tailWord_252077) baseStart_252077 baseEnd_252077 := by
    simpa [prefixWord, tailWord_252077, baseEnd_252077] using wordTrace_append hprefix tailTrace_252077
  have hstable : (prefixWord ++ tailWord_252077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252077).length < 2 ^ (prefixWord ++ tailWord_252077).sum := by decide
  have hdescent : baseEnd_252077 < baseStart_252077 := by decide
  rcases family_descends (prefixWord ++ tailWord_252077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252098 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_252098 : Nat := 118140960795 + 252098 * 2 ^ 59
def prefixEnd_252098 : Nat := 4983230072969 + 3 ^ 40 * 252098 * 2
def baseEnd_252098 : Nat := 14383049559695544346181

theorem tailTrace_252098 : CollatzResearch.WordTrace tailWord_252098 prefixEnd_252098 14383049559695544346181 := by
  unfold tailWord_252098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298692360174868938933237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6129846293799650503821965 2298692360174868938933237)
  ·
    refine ⟨215502408766393963024991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2298692360174868938933237 215502408766393963024991)
    ·
      refine ⟨323253613149590944537487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215502408766393963024991 323253613149590944537487)
      ·
        refine ⟨484880419724386416806231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323253613149590944537487 484880419724386416806231)
        ·
          refine ⟨727320629586579625209347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484880419724386416806231 727320629586579625209347)
          ·
            refine ⟨1090980944379869437814021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727320629586579625209347 1090980944379869437814021)
            ·
              refine ⟨204558927071225519590129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090980944379869437814021 204558927071225519590129)
              ·
                refine ⟨153419195303419139692597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204558927071225519590129 153419195303419139692597)
                ·
                  refine ⟨14383049559695544346181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153419195303419139692597 14383049559695544346181)
                  ·
                    rfl

theorem cell23_252098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_252098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252098 prefixEnd_252098 := by exact prefixLift 252098
  have htrace : WordTrace (prefixWord ++ tailWord_252098) baseStart_252098 baseEnd_252098 := by
    simpa [prefixWord, tailWord_252098, baseEnd_252098] using wordTrace_append hprefix tailTrace_252098
  have hstable : (prefixWord ++ tailWord_252098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252098).length < 2 ^ (prefixWord ++ tailWord_252098).sum := by decide
  have hdescent : baseEnd_252098 < baseStart_252098 := by decide
  rcases family_descends (prefixWord ++ tailWord_252098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252114 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_252114 : Nat := 118140960795 + 252114 * 2 ^ 59
def prefixEnd_252114 : Nat := 4983230072969 + 3 ^ 40 * 252114 * 2
def baseEnd_252114 : Nat := 129455661727731836515555

theorem tailTrace_252114 : CollatzResearch.WordTrace tailWord_252114 prefixEnd_252114 129455661727731836515555 := by
  unfold tailWord_252114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298838252160377622078849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6130235339094340325543597 2298838252160377622078849)
  ·
    refine ⟨1724128689120283216559137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2298838252160377622078849 1724128689120283216559137)
    ·
      refine ⟨1293096516840212412419353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1724128689120283216559137 1293096516840212412419353)
      ·
        refine ⟨969822387630159309314515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293096516840212412419353 969822387630159309314515)
        ·
          refine ⟨1454733581445238963971773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969822387630159309314515 1454733581445238963971773)
          ·
            refine ⟨545525093041964611489415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1454733581445238963971773 545525093041964611489415)
            ·
              refine ⟨818287639562946917234123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545525093041964611489415 818287639562946917234123)
              ·
                refine ⟨1227431459344420375851185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818287639562946917234123 1227431459344420375851185)
                ·
                  refine ⟨920573594508315281888389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227431459344420375851185 920573594508315281888389)
                  ·
                    refine ⟨172607548970309115354073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920573594508315281888389 172607548970309115354073)
                    ·
                      refine ⟨129455661727731836515555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172607548970309115354073 129455661727731836515555)
                      ·
                        rfl

theorem cell23_252114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_252114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252114 prefixEnd_252114 := by exact prefixLift 252114
  have htrace : WordTrace (prefixWord ++ tailWord_252114) baseStart_252114 baseEnd_252114 := by
    simpa [prefixWord, tailWord_252114, baseEnd_252114] using wordTrace_append hprefix tailTrace_252114
  have hstable : (prefixWord ++ tailWord_252114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252114).length < 2 ^ (prefixWord ++ tailWord_252114).sum := by decide
  have hdescent : baseEnd_252114 < baseStart_252114 := by decide
  rcases family_descends (prefixWord ++ tailWord_252114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252131 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 4]
def baseStart_252131 : Nat := 118140960795 + 252131 * 2 ^ 59
def prefixEnd_252131 : Nat := 4983230072969 + 3 ^ 40 * 252131 * 2
def baseEnd_252131 : Nat := 129464390898858270002977

theorem tailTrace_252131 : CollatzResearch.WordTrace tailWord_252131 prefixEnd_252131 129464390898858270002977 := by
  unfold tailWord_252131
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195973049579922391684247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6130648699719948261122831 9195973049579922391684247)
  ·
    refine ⟨13793959574369883587526371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195973049579922391684247 13793959574369883587526371)
    ·
      refine ⟨20690939361554825381289557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793959574369883587526371 20690939361554825381289557)
      ·
        refine ⟨242471945643220609936987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 20690939361554825381289557 242471945643220609936987)
        ·
          refine ⟨363707918464830914905481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242471945643220609936987 363707918464830914905481)
          ·
            refine ⟨272780938848623186179111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363707918464830914905481 272780938848623186179111)
            ·
              refine ⟨409171408272934779268667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272780938848623186179111 409171408272934779268667)
              ·
                refine ⟨613757112409402168903001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409171408272934779268667 613757112409402168903001)
                ·
                  refine ⟨460317834307051626677251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613757112409402168903001 460317834307051626677251)
                  ·
                    refine ⟨690476751460577440015877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460317834307051626677251 690476751460577440015877)
                    ·
                      refine ⟨129464390898858270002977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 690476751460577440015877 129464390898858270002977)
                      ·
                        rfl

theorem cell23_252131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_252131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252131 prefixEnd_252131 := by exact prefixLift 252131
  have htrace : WordTrace (prefixWord ++ tailWord_252131) baseStart_252131 baseEnd_252131 := by
    simpa [prefixWord, tailWord_252131, baseEnd_252131] using wordTrace_append hprefix tailTrace_252131
  have hstable : (prefixWord ++ tailWord_252131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252131).length < 2 ^ (prefixWord ++ tailWord_252131).sum := by decide
  have hdescent : baseEnd_252131 < baseStart_252131 := by decide
  rcases family_descends (prefixWord ++ tailWord_252131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252147 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 3]
def baseStart_252147 : Nat := 118140960795 + 252147 * 2 ^ 59
def prefixEnd_252147 : Nat := 4983230072969 + 3 ^ 40 * 252147 * 2
def baseEnd_252147 : Nat := 129472606589330207402903

theorem tailTrace_252147 : CollatzResearch.WordTrace tailWord_252147 prefixEnd_252147 129472606589330207402903 := by
  unfold tailWord_252147
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196556617521957124266695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6131037745014638082844463 9196556617521957124266695)
  ·
    refine ⟨13794834926282935686400043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9196556617521957124266695 13794834926282935686400043)
    ·
      refine ⟨20692252389424403529600065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13794834926282935686400043 20692252389424403529600065)
      ·
        refine ⟨15519189292068302647200049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20692252389424403529600065 15519189292068302647200049)
        ·
          refine ⟨11639391969051226985400037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15519189292068302647200049 11639391969051226985400037)
          ·
            refine ⟨2182385994197105059762507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11639391969051226985400037 2182385994197105059762507)
            ·
              refine ⟨3273578991295657589643761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182385994197105059762507 3273578991295657589643761)
              ·
                refine ⟨2455184243471743192232821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273578991295657589643761 2455184243471743192232821)
                ·
                  refine ⟨230173522825475924271827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455184243471743192232821 230173522825475924271827)
                  ·
                    refine ⟨345260284238213886407741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230173522825475924271827 345260284238213886407741)
                    ·
                      refine ⟨129472606589330207402903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345260284238213886407741 129472606589330207402903)
                      ·
                        rfl

theorem cell23_252147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_252147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252147 prefixEnd_252147 := by exact prefixLift 252147
  have htrace : WordTrace (prefixWord ++ tailWord_252147) baseStart_252147 baseEnd_252147 := by
    simpa [prefixWord, tailWord_252147, baseEnd_252147] using wordTrace_append hprefix tailTrace_252147
  have hstable : (prefixWord ++ tailWord_252147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252147).length < 2 ^ (prefixWord ++ tailWord_252147).sum := by decide
  have hdescent : baseEnd_252147 < baseStart_252147 := by decide
  rcases family_descends (prefixWord ++ tailWord_252147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252187 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 4]
def baseStart_252187 : Nat := 118140960795 + 252187 * 2 ^ 59
def prefixEnd_252187 : Nat := 4983230072969 + 3 ^ 40 * 252187 * 2
def baseEnd_252187 : Nat := 129493145815510050902719

theorem tailTrace_252187 : CollatzResearch.WordTrace tailWord_252187 prefixEnd_252187 129493145815510050902719 := by
  unfold tailWord_252187
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198015537377043955722815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6132010358251362637148543 9198015537377043955722815)
  ·
    refine ⟨13797023306065565933584223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9198015537377043955722815 13797023306065565933584223)
    ·
      refine ⟨20695534959098348900376335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13797023306065565933584223 20695534959098348900376335)
      ·
        refine ⟨31043302438647523350564503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20695534959098348900376335 31043302438647523350564503)
        ·
          refine ⟨46564953657971285025846755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31043302438647523350564503 46564953657971285025846755)
          ·
            refine ⟨69847430486956927538770133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46564953657971285025846755 69847430486956927538770133)
            ·
              refine ⟨1637049152038052989189925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69847430486956927538770133 1637049152038052989189925)
              ·
                refine ⟨306946716007134935473111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1637049152038052989189925 306946716007134935473111)
                ·
                  refine ⟨460420074010702403209667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306946716007134935473111 460420074010702403209667)
                  ·
                    refine ⟨690630111016053604814501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460420074010702403209667 690630111016053604814501)
                    ·
                      refine ⟨129493145815510050902719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 690630111016053604814501 129493145815510050902719)
                      ·
                        rfl

theorem cell23_252187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 4].length) (baseStart_252187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252187 prefixEnd_252187 := by exact prefixLift 252187
  have htrace : WordTrace (prefixWord ++ tailWord_252187) baseStart_252187 baseEnd_252187 := by
    simpa [prefixWord, tailWord_252187, baseEnd_252187] using wordTrace_append hprefix tailTrace_252187
  have hstable : (prefixWord ++ tailWord_252187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252187).length < 2 ^ (prefixWord ++ tailWord_252187).sum := by decide
  have hdescent : baseEnd_252187 < baseStart_252187 := by decide
  rcases family_descends (prefixWord ++ tailWord_252187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252204 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_252204 : Nat := 118140960795 + 252204 * 2 ^ 59
def prefixEnd_252204 : Nat := 4983230072969 + 3 ^ 40 * 252204 * 2
def baseEnd_252204 : Nat := 129501874986636484390141

theorem tailTrace_252204 : CollatzResearch.WordTrace tailWord_252204 prefixEnd_252204 129501874986636484390141 := by
  unfold tailWord_252204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599317789157727929545833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6132423718876970572727777 4599317789157727929545833)
  ·
    refine ⟨3449488341868295947159375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4599317789157727929545833 3449488341868295947159375)
    ·
      refine ⟨5174232512802443920739063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449488341868295947159375 5174232512802443920739063)
      ·
        refine ⟨7761348769203665881108595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174232512802443920739063 7761348769203665881108595)
        ·
          refine ⟨11642023153805498821662893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761348769203665881108595 11642023153805498821662893)
          ·
            refine ⟨4365758682677062058123585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11642023153805498821662893 4365758682677062058123585)
            ·
              refine ⟨3274319012007796543592689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365758682677062058123585 3274319012007796543592689)
              ·
                refine ⟨2455739259005847407694517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274319012007796543592689 2455739259005847407694517)
                ·
                  refine ⟨230225555531798194471361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455739259005847407694517 230225555531798194471361)
                  ·
                    refine ⟨172669166648848645853521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230225555531798194471361 172669166648848645853521)
                    ·
                      refine ⟨129501874986636484390141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172669166648848645853521 129501874986636484390141)
                      ·
                        rfl

theorem cell23_252204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_252204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252204 prefixEnd_252204 := by exact prefixLift 252204
  have htrace : WordTrace (prefixWord ++ tailWord_252204) baseStart_252204 baseEnd_252204 := by
    simpa [prefixWord, tailWord_252204, baseEnd_252204] using wordTrace_append hprefix tailTrace_252204
  have hstable : (prefixWord ++ tailWord_252204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252204).length < 2 ^ (prefixWord ++ tailWord_252204).sum := by decide
  have hdescent : baseEnd_252204 < baseStart_252204 := by decide
  rcases family_descends (prefixWord ++ tailWord_252204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252217 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_252217 : Nat := 118140960795 + 252217 * 2 ^ 59
def prefixEnd_252217 : Nat := 4983230072969 + 3 ^ 40 * 252217 * 2
def baseEnd_252217 : Nat := 129508550235144933527581

theorem tailTrace_252217 : CollatzResearch.WordTrace tailWord_252217 prefixEnd_252217 129508550235144933527581 := by
  unfold tailWord_252217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199109727268359079314905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6132739818178906052876603 9199109727268359079314905)
  ·
    refine ⟨6899332295451269309486179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9199109727268359079314905 6899332295451269309486179)
    ·
      refine ⟨10348998443176903964229269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6899332295451269309486179 10348998443176903964229269)
      ·
        refine ⟨485109302023917373323247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10348998443176903964229269 485109302023917373323247)
        ·
          refine ⟨727663953035876059984871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485109302023917373323247 727663953035876059984871)
          ·
            refine ⟨1091495929553814089977307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727663953035876059984871 1091495929553814089977307)
            ·
              refine ⟨1637243894330721134965961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091495929553814089977307 1637243894330721134965961)
              ·
                refine ⟨1227932920748040851224471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637243894330721134965961 1227932920748040851224471)
                ·
                  refine ⟨1841899381122061276836707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227932920748040851224471 1841899381122061276836707)
                  ·
                    refine ⟨2762849071683091915255061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1841899381122061276836707 2762849071683091915255061)
                    ·
                      refine ⟨129508550235144933527581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2762849071683091915255061 129508550235144933527581)
                      ·
                        rfl

theorem cell23_252217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_252217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252217 prefixEnd_252217 := by exact prefixLift 252217
  have htrace : WordTrace (prefixWord ++ tailWord_252217) baseStart_252217 baseEnd_252217 := by
    simpa [prefixWord, tailWord_252217, baseEnd_252217] using wordTrace_append hprefix tailTrace_252217
  have hstable : (prefixWord ++ tailWord_252217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252217).length < 2 ^ (prefixWord ++ tailWord_252217).sum := by decide
  have hdescent : baseEnd_252217 < baseStart_252217 := by decide
  rcases family_descends (prefixWord ++ tailWord_252217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252241 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_252241 : Nat := 118140960795 + 252241 * 2 ^ 59
def prefixEnd_252241 : Nat := 4983230072969 + 3 ^ 40 * 252241 * 2
def baseEnd_252241 : Nat := 129520873770852839627471

theorem tailTrace_252241 : CollatzResearch.WordTrace tailWord_252241 prefixEnd_252241 129520873770852839627471 := by
  unfold tailWord_252241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199985079181411178188577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6133323386120940785459051 9199985079181411178188577)
  ·
    refine ⟨6899988809386058383641433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9199985079181411178188577 6899988809386058383641433)
    ·
      refine ⟨5174991607039543787731075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6899988809386058383641433 5174991607039543787731075)
      ·
        refine ⟨7762487410559315681596613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174991607039543787731075 7762487410559315681596613)
        ·
          refine ⟨1455466389479871690299365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7762487410559315681596613 1455466389479871690299365)
          ·
            refine ⟨272899948027475941931131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1455466389479871690299365 272899948027475941931131)
            ·
              refine ⟨409349922041213912896697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272899948027475941931131 409349922041213912896697)
              ·
                refine ⟨307012441530910434672523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409349922041213912896697 307012441530910434672523)
                ·
                  refine ⟨460518662296365652008785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307012441530910434672523 460518662296365652008785)
                  ·
                    refine ⟨345388996722274239006589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 460518662296365652008785 345388996722274239006589)
                    ·
                      refine ⟨129520873770852839627471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345388996722274239006589 129520873770852839627471)
                      ·
                        rfl

theorem cell23_252241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_252241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252241 prefixEnd_252241 := by exact prefixLift 252241
  have htrace : WordTrace (prefixWord ++ tailWord_252241) baseStart_252241 baseEnd_252241 := by
    simpa [prefixWord, tailWord_252241, baseEnd_252241] using wordTrace_append hprefix tailTrace_252241
  have hstable : (prefixWord ++ tailWord_252241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252241).length < 2 ^ (prefixWord ++ tailWord_252241).sum := by decide
  have hdescent : baseEnd_252241 < baseStart_252241 := by decide
  rcases family_descends (prefixWord ++ tailWord_252241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252258 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_252258 : Nat := 118140960795 + 252258 * 2 ^ 59
def prefixEnd_252258 : Nat := 4983230072969 + 3 ^ 40 * 252258 * 2
def baseEnd_252258 : Nat := 129529602941979273114893

theorem tailTrace_252258 : CollatzResearch.WordTrace tailWord_252258 prefixEnd_252258 129529602941979273114893 := by
  unfold tailWord_252258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300151280029955770389357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6133736746746548721038285 2300151280029955770389357)
  ·
    refine ⟨862556730011233413896009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2300151280029955770389357 862556730011233413896009)
    ·
      refine ⟨646917547508425060422007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862556730011233413896009 646917547508425060422007)
      ·
        refine ⟨970376321262637590633011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646917547508425060422007 970376321262637590633011)
        ·
          refine ⟨1455564481893956385949517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970376321262637590633011 1455564481893956385949517)
          ·
            refine ⟨545836680710233644731069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1455564481893956385949517 545836680710233644731069)
            ·
              refine ⟨204688755266337616774151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545836680710233644731069 204688755266337616774151)
              ·
                refine ⟨307033132899506425161227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204688755266337616774151 307033132899506425161227)
                ·
                  refine ⟨460549699349259637741841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307033132899506425161227 460549699349259637741841)
                  ·
                    refine ⟨345412274511944728306381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 460549699349259637741841 345412274511944728306381)
                    ·
                      refine ⟨129529602941979273114893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345412274511944728306381 129529602941979273114893)
                      ·
                        rfl

theorem cell23_252258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_252258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252258 prefixEnd_252258 := by exact prefixLift 252258
  have htrace : WordTrace (prefixWord ++ tailWord_252258) baseStart_252258 baseEnd_252258 := by
    simpa [prefixWord, tailWord_252258, baseEnd_252258] using wordTrace_append hprefix tailTrace_252258
  have hstable : (prefixWord ++ tailWord_252258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252258).length < 2 ^ (prefixWord ++ tailWord_252258).sum := by decide
  have hdescent : baseEnd_252258 < baseStart_252258 := by decide
  rcases family_descends (prefixWord ++ tailWord_252258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252278 : List Nat := [5, 1, 1, 4, 2, 1, 1, 8]
def baseStart_252278 : Nat := 118140960795 + 252278 * 2 ^ 59
def prefixEnd_252278 : Nat := 4983230072969 + 3 ^ 40 * 252278 * 2
def baseEnd_252278 : Nat := 4797773057595155365363

theorem tailTrace_252278 : CollatzResearch.WordTrace tailWord_252278 prefixEnd_252278 4797773057595155365363 := by
  unfold tailWord_252278
  simp only [CollatzResearch.WordTrace]
  refine ⟨575083411252960406080343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6134223053364910998190325 575083411252960406080343)
  ·
    refine ⟨862625116879440609120515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 575083411252960406080343 862625116879440609120515)
    ·
      refine ⟨1293937675319160913680773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862625116879440609120515 1293937675319160913680773)
      ·
        refine ⟨242613314122342671315145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1293937675319160913680773 242613314122342671315145)
        ·
          refine ⟨181959985591757003486359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242613314122342671315145 181959985591757003486359)
          ·
            refine ⟨272939978387635505229539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181959985591757003486359 272939978387635505229539)
            ·
              refine ⟨409409967581453257844309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272939978387635505229539 409409967581453257844309)
              ·
                refine ⟨4797773057595155365363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 409409967581453257844309 4797773057595155365363)
                ·
                  rfl

theorem cell23_252278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_252278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252278 prefixEnd_252278 := by exact prefixLift 252278
  have htrace : WordTrace (prefixWord ++ tailWord_252278) baseStart_252278 baseEnd_252278 := by
    simpa [prefixWord, tailWord_252278, baseEnd_252278] using wordTrace_append hprefix tailTrace_252278
  have hstable : (prefixWord ++ tailWord_252278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252278).length < 2 ^ (prefixWord ++ tailWord_252278).sum := by decide
  have hdescent : baseEnd_252278 < baseStart_252278 := by decide
  rcases family_descends (prefixWord ++ tailWord_252278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252345 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 2, 2, 2]
def baseStart_252345 : Nat := 118140960795 + 252345 * 2 ^ 59
def prefixEnd_252345 : Nat := 4983230072969 + 3 ^ 40 * 252345 * 2
def baseEnd_252345 : Nat := 129574275758920432726993

theorem tailTrace_252345 : CollatzResearch.WordTrace tailWord_252345 prefixEnd_252345 129574275758920432726993 := by
  unfold tailWord_252345
  simp only [CollatzResearch.WordTrace]
  refine ⟨9203778270804636939974489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6135852180536424626649659 9203778270804636939974489)
  ·
    refine ⟨6902833703103477704980867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9203778270804636939974489 6902833703103477704980867)
    ·
      refine ⟨10354250554655216557471301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6902833703103477704980867 10354250554655216557471301)
      ·
        refine ⟨1941421978997853104525869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10354250554655216557471301 1941421978997853104525869)
        ·
          refine ⟨728033242124194914197201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1941421978997853104525869 728033242124194914197201)
          ·
            refine ⟨546024931593146185647901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728033242124194914197201 546024931593146185647901)
            ·
              refine ⟨204759349347429819617963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546024931593146185647901 204759349347429819617963)
              ·
                refine ⟨307139024021144729426945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204759349347429819617963 307139024021144729426945)
                ·
                  refine ⟨230354268015858547070209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307139024021144729426945 230354268015858547070209)
                  ·
                    refine ⟨172765701011893910302657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230354268015858547070209 172765701011893910302657)
                    ·
                      refine ⟨129574275758920432726993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172765701011893910302657 129574275758920432726993)
                      ·
                        rfl

theorem cell23_252345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_252345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252345 prefixEnd_252345 := by exact prefixLift 252345
  have htrace : WordTrace (prefixWord ++ tailWord_252345) baseStart_252345 baseEnd_252345 := by
    simpa [prefixWord, tailWord_252345, baseEnd_252345] using wordTrace_append hprefix tailTrace_252345
  have hstable : (prefixWord ++ tailWord_252345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252345).length < 2 ^ (prefixWord ++ tailWord_252345).sum := by decide
  have hdescent : baseEnd_252345 < baseStart_252345 := by decide
  rcases family_descends (prefixWord ++ tailWord_252345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252384 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_252384 : Nat := 118140960795 + 252384 * 2 ^ 59
def prefixEnd_252384 : Nat := 4983230072969 + 3 ^ 40 * 252384 * 2
def baseEnd_252384 : Nat := 129594301504445780139313

theorem tailTrace_252384 : CollatzResearch.WordTrace tailWord_252384 prefixEnd_252384 129594301504445780139313 := by
  unfold tailWord_252384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602600358831673300322103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6136800478442231067096137 4602600358831673300322103)
  ·
    refine ⟨6903900538247509950483155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602600358831673300322103 6903900538247509950483155)
    ·
      refine ⟨10355850807371264925724733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903900538247509950483155 10355850807371264925724733)
      ·
        refine ⟨3883444052764224347146775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10355850807371264925724733 3883444052764224347146775)
        ·
          refine ⟨5825166079146336520720163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883444052764224347146775 5825166079146336520720163)
          ·
            refine ⟨8737749118719504781080245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825166079146336520720163 8737749118719504781080245)
            ·
              refine ⟨819163979879953573226273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8737749118719504781080245 819163979879953573226273)
              ·
                refine ⟨614372984909965179919705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819163979879953573226273 614372984909965179919705)
                ·
                  refine ⟨460779738682473884939779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614372984909965179919705 460779738682473884939779)
                  ·
                    refine ⟨691169608023710827409669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460779738682473884939779 691169608023710827409669)
                    ·
                      refine ⟨129594301504445780139313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 691169608023710827409669 129594301504445780139313)
                      ·
                        rfl

theorem cell23_252384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_252384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252384 prefixEnd_252384 := by exact prefixLift 252384
  have htrace : WordTrace (prefixWord ++ tailWord_252384) baseStart_252384 baseEnd_252384 := by
    simpa [prefixWord, tailWord_252384, baseEnd_252384] using wordTrace_append hprefix tailTrace_252384
  have hstable : (prefixWord ++ tailWord_252384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252384).length < 2 ^ (prefixWord ++ tailWord_252384).sum := by decide
  have hdescent : baseEnd_252384 < baseStart_252384 := by decide
  rcases family_descends (prefixWord ++ tailWord_252384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252445 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_252445 : Nat := 118140960795 + 252445 * 2 ^ 59
def prefixEnd_252445 : Nat := 4983230072969 + 3 ^ 40 * 252445 * 2
def baseEnd_252445 : Nat := 43208541274790013825511

theorem tailTrace_252445 : CollatzResearch.WordTrace tailWord_252445 prefixEnd_252445 43208541274790013825511 := by
  unfold tailWord_252445
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207425570442354018614789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6138283713628236012409859 9207425570442354018614789)
  ·
    refine ⟨1726392294457941378490273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9207425570442354018614789 1726392294457941378490273)
    ·
      refine ⟨1294794220843456033867705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1726392294457941378490273 1294794220843456033867705)
      ·
        refine ⟨971095665632592025400779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1294794220843456033867705 971095665632592025400779)
        ·
          refine ⟨1456643498448888038101169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971095665632592025400779 1456643498448888038101169)
          ·
            refine ⟨1092482623836666028575877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456643498448888038101169 1092482623836666028575877)
            ·
              refine ⟨204840491969374880357977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1092482623836666028575877 204840491969374880357977)
              ·
                refine ⟨153630368977031160268483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204840491969374880357977 153630368977031160268483)
                ·
                  refine ⟨230445553465546740402725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153630368977031160268483 230445553465546740402725)
                  ·
                    refine ⟨43208541274790013825511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230445553465546740402725 43208541274790013825511)
                    ·
                      rfl

theorem cell23_252445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_252445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252445 prefixEnd_252445 := by exact prefixLift 252445
  have htrace : WordTrace (prefixWord ++ tailWord_252445) baseStart_252445 baseEnd_252445 := by
    simpa [prefixWord, tailWord_252445, baseEnd_252445] using wordTrace_append hprefix tailTrace_252445
  have hstable : (prefixWord ++ tailWord_252445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252445).length < 2 ^ (prefixWord ++ tailWord_252445).sum := by decide
  have hdescent : baseEnd_252445 < baseStart_252445 := by decide
  rcases family_descends (prefixWord ++ tailWord_252445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252485 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 1, 1, 3]
def baseStart_252485 : Nat := 118140960795 + 252485 * 2 ^ 59
def prefixEnd_252485 : Nat := 4983230072969 + 3 ^ 40 * 252485 * 2
def baseEnd_252485 : Nat := 129646163050549884976349

theorem tailTrace_252485 : CollatzResearch.WordTrace tailWord_252485 prefixEnd_252485 129646163050549884976349 := by
  unfold tailWord_252485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208884490297440850070909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6139256326864960566713939 9208884490297440850070909)
  ·
    refine ⟨3453331683861540318776591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9208884490297440850070909 3453331683861540318776591)
    ·
      refine ⟨5179997525792310478164887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453331683861540318776591 5179997525792310478164887)
      ·
        refine ⟨7769996288688465717247331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179997525792310478164887 7769996288688465717247331)
        ·
          refine ⟨11654994433032698575870997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769996288688465717247331 11654994433032698575870997)
          ·
            refine ⟨546327864048407745743953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11654994433032698575870997 546327864048407745743953)
            ·
              refine ⟨409745898036305809307965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546327864048407745743953 409745898036305809307965)
              ·
                refine ⟨153654711763614678490487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409745898036305809307965 153654711763614678490487)
                ·
                  refine ⟨230482067645422017735731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153654711763614678490487 230482067645422017735731)
                  ·
                    refine ⟨345723101468133026603597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230482067645422017735731 345723101468133026603597)
                    ·
                      refine ⟨129646163050549884976349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345723101468133026603597 129646163050549884976349)
                      ·
                        rfl

theorem cell23_252485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_252485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252485 prefixEnd_252485 := by exact prefixLift 252485
  have htrace : WordTrace (prefixWord ++ tailWord_252485) baseStart_252485 baseEnd_252485 := by
    simpa [prefixWord, tailWord_252485, baseEnd_252485] using wordTrace_append hprefix tailTrace_252485
  have hstable : (prefixWord ++ tailWord_252485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252485).length < 2 ^ (prefixWord ++ tailWord_252485).sum := by decide
  have hdescent : baseEnd_252485 < baseStart_252485 := by decide
  rcases family_descends (prefixWord ++ tailWord_252485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252504 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_252504 : Nat := 118140960795 + 252504 * 2 ^ 59
def prefixEnd_252504 : Nat := 4983230072969 + 3 ^ 40 * 252504 * 2
def baseEnd_252504 : Nat := 129655919182985310638761

theorem tailTrace_252504 : CollatzResearch.WordTrace tailWord_252504 prefixEnd_252504 129655919182985310638761 := by
  unfold tailWord_252504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604788738614303547506283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6139718318152404730008377 4604788738614303547506283)
  ·
    refine ⟨6907183107921455321259425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4604788738614303547506283 6907183107921455321259425)
    ·
      refine ⟨5180387330941091490944569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6907183107921455321259425 5180387330941091490944569)
      ·
        refine ⟨3885290498205818618208427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5180387330941091490944569 3885290498205818618208427)
        ·
          refine ⟨5827935747308727927312641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885290498205818618208427 5827935747308727927312641)
          ·
            refine ⟨4370951810481545945484481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827935747308727927312641 4370951810481545945484481)
            ·
              refine ⟨3278213857861159459113361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370951810481545945484481 3278213857861159459113361)
              ·
                refine ⟨2458660393395869594335021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278213857861159459113361 2458660393395869594335021)
                ·
                  refine ⟨921997647523451097875633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2458660393395869594335021 921997647523451097875633)
                  ·
                    refine ⟨691498235642588323406725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921997647523451097875633 691498235642588323406725)
                    ·
                      refine ⟨129655919182985310638761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 691498235642588323406725 129655919182985310638761)
                      ·
                        rfl

theorem cell23_252504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_252504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252504 prefixEnd_252504 := by exact prefixLift 252504
  have htrace : WordTrace (prefixWord ++ tailWord_252504) baseStart_252504 baseEnd_252504 := by
    simpa [prefixWord, tailWord_252504, baseEnd_252504] using wordTrace_append hprefix tailTrace_252504
  have hstable : (prefixWord ++ tailWord_252504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252504).length < 2 ^ (prefixWord ++ tailWord_252504).sum := by decide
  have hdescent : baseEnd_252504 < baseStart_252504 := by decide
  rcases family_descends (prefixWord ++ tailWord_252504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252525 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_252525 : Nat := 118140960795 + 252525 * 2 ^ 59
def prefixEnd_252525 : Nat := 4983230072969 + 3 ^ 40 * 252525 * 2
def baseEnd_252525 : Nat := 129666702276729728476165

theorem tailTrace_252525 : CollatzResearch.WordTrace tailWord_252525 prefixEnd_252525 129666702276729728476165 := by
  unfold tailWord_252525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9210343410152527681527029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6140228940101685121018019 9210343410152527681527029)
  ·
    refine ⟨863469694701799470143159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9210343410152527681527029 863469694701799470143159)
    ·
      refine ⟨1295204542052699205214739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863469694701799470143159 1295204542052699205214739)
      ·
        refine ⟨1942806813079048807822109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295204542052699205214739 1942806813079048807822109)
        ·
          refine ⟨728552554904643302933291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942806813079048807822109 728552554904643302933291)
          ·
            refine ⟨1092828832356964954399937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728552554904643302933291 1092828832356964954399937)
            ·
              refine ⟨819621624267723715799953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092828832356964954399937 819621624267723715799953)
              ·
                refine ⟨614716218200792786849965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819621624267723715799953 614716218200792786849965)
                ·
                  refine ⟨230518581825297295068737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614716218200792786849965 230518581825297295068737)
                  ·
                    refine ⟨172888936368972971301553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230518581825297295068737 172888936368972971301553)
                    ·
                      refine ⟨129666702276729728476165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172888936368972971301553 129666702276729728476165)
                      ·
                        rfl

theorem cell23_252525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_252525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252525 prefixEnd_252525 := by exact prefixLift 252525
  have htrace : WordTrace (prefixWord ++ tailWord_252525) baseStart_252525 baseEnd_252525 := by
    simpa [prefixWord, tailWord_252525, baseEnd_252525] using wordTrace_append hprefix tailTrace_252525
  have hstable : (prefixWord ++ tailWord_252525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252525).length < 2 ^ (prefixWord ++ tailWord_252525).sum := by decide
  have hdescent : baseEnd_252525 < baseStart_252525 := by decide
  rcases family_descends (prefixWord ++ tailWord_252525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252558 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_252558 : Nat := 118140960795 + 252558 * 2 ^ 59
def prefixEnd_252558 : Nat := 4983230072969 + 3 ^ 40 * 252558 * 2
def baseEnd_252558 : Nat := 129683647138328099363513

theorem tailTrace_252558 : CollatzResearch.WordTrace tailWord_252558 prefixEnd_252558 129683647138328099363513 := by
  unfold tailWord_252558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151443377379121789684791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6141031346021982878318885 1151443377379121789684791)
  ·
    refine ⟨1727165066068682684527187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1151443377379121789684791 1727165066068682684527187)
    ·
      refine ⟨2590747599103024026790781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727165066068682684527187 2590747599103024026790781)
      ·
        refine ⟨971530349663634010046543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2590747599103024026790781 971530349663634010046543)
        ·
          refine ⟨1457295524495451015069815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971530349663634010046543 1457295524495451015069815)
          ·
            refine ⟨2185943286743176522604723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457295524495451015069815 2185943286743176522604723)
            ·
              refine ⟨3278914930114764783907085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185943286743176522604723 3278914930114764783907085)
              ·
                refine ⟨1229593098793036793965157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3278914930114764783907085 1229593098793036793965157)
                ·
                  refine ⟨230548706023694398868467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229593098793036793965157 230548706023694398868467)
                  ·
                    refine ⟨345823059035541598302701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230548706023694398868467 345823059035541598302701)
                    ·
                      refine ⟨129683647138328099363513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345823059035541598302701 129683647138328099363513)
                      ·
                        rfl

theorem cell23_252558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_252558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252558 prefixEnd_252558 := by exact prefixLift 252558
  have htrace : WordTrace (prefixWord ++ tailWord_252558) baseStart_252558 baseEnd_252558 := by
    simpa [prefixWord, tailWord_252558, baseEnd_252558] using wordTrace_append hprefix tailTrace_252558
  have hstable : (prefixWord ++ tailWord_252558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252558).length < 2 ^ (prefixWord ++ tailWord_252558).sum := by decide
  have hdescent : baseEnd_252558 < baseStart_252558 := by decide
  rcases family_descends (prefixWord ++ tailWord_252558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252568 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_252568 : Nat := 118140960795 + 252568 * 2 ^ 59
def prefixEnd_252568 : Nat := 4983230072969 + 3 ^ 40 * 252568 * 2
def baseEnd_252568 : Nat := 129688781944873060238467

theorem tailTrace_252568 : CollatzResearch.WordTrace tailWord_252568 prefixEnd_252568 129688781944873060238467 := by
  unfold tailWord_252568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605955874498373012671179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6141274499331164016894905 4605955874498373012671179)
  ·
    refine ⟨6908933811747559519006769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4605955874498373012671179 6908933811747559519006769)
    ·
      refine ⟨5181700358810669639255077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6908933811747559519006769 5181700358810669639255077)
      ·
        refine ⟨971568817277000557360327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5181700358810669639255077 971568817277000557360327)
        ·
          refine ⟨1457353225915500836040491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971568817277000557360327 1457353225915500836040491)
          ·
            refine ⟨2186029838873251254060737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457353225915500836040491 2186029838873251254060737)
            ·
              refine ⟨1639522379154938440545553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186029838873251254060737 1639522379154938440545553)
              ·
                refine ⟨1229641784366203830409165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639522379154938440545553 1229641784366203830409165)
                ·
                  refine ⟨461115669137326436403437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229641784366203830409165 461115669137326436403437)
                  ·
                    refine ⟨172918375926497413651289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461115669137326436403437 172918375926497413651289)
                    ·
                      refine ⟨129688781944873060238467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 172918375926497413651289 129688781944873060238467)
                      ·
                        rfl

theorem cell23_252568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_252568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252568 prefixEnd_252568 := by exact prefixLift 252568
  have htrace : WordTrace (prefixWord ++ tailWord_252568) baseStart_252568 baseEnd_252568 := by
    simpa [prefixWord, tailWord_252568, baseEnd_252568] using wordTrace_append hprefix tailTrace_252568
  have hstable : (prefixWord ++ tailWord_252568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252568).length < 2 ^ (prefixWord ++ tailWord_252568).sum := by decide
  have hdescent : baseEnd_252568 < baseStart_252568 := by decide
  rcases family_descends (prefixWord ++ tailWord_252568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252609 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_252609 : Nat := 118140960795 + 252609 * 2 ^ 59
def prefixEnd_252609 : Nat := 4983230072969 + 3 ^ 40 * 252609 * 2
def baseEnd_252609 : Nat := 129709834651707399825779

theorem tailTrace_252609 : CollatzResearch.WordTrace tailWord_252609 prefixEnd_252609 129709834651707399825779 := by
  unfold tailWord_252609
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213407141848210027584881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6142271427898806685056587 9213407141848210027584881)
  ·
    refine ⟨6910055356386157520688661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9213407141848210027584881 6910055356386157520688661)
    ·
      refine ⟨323908844830601133782281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6910055356386157520688661 323908844830601133782281)
      ·
        refine ⟨242931633622950850336711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323908844830601133782281 242931633622950850336711)
        ·
          refine ⟨364397450434426275505067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242931633622950850336711 364397450434426275505067)
          ·
            refine ⟨546596175651639413257601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364397450434426275505067 546596175651639413257601)
            ·
              refine ⟨409947131738729559943201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546596175651639413257601 409947131738729559943201)
              ·
                refine ⟨307460348804047169957401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409947131738729559943201 307460348804047169957401)
                ·
                  refine ⟨230595261603035377468051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307460348804047169957401 230595261603035377468051)
                  ·
                    refine ⟨345892892404553066202077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230595261603035377468051 345892892404553066202077)
                    ·
                      refine ⟨129709834651707399825779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345892892404553066202077 129709834651707399825779)
                      ·
                        rfl

theorem cell23_252609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_252609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252609 prefixEnd_252609 := by exact prefixLift 252609
  have htrace : WordTrace (prefixWord ++ tailWord_252609) baseStart_252609 baseEnd_252609 := by
    simpa [prefixWord, tailWord_252609, baseEnd_252609] using wordTrace_append hprefix tailTrace_252609
  have hstable : (prefixWord ++ tailWord_252609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252609).length < 2 ^ (prefixWord ++ tailWord_252609).sum := by decide
  have hdescent : baseEnd_252609 < baseStart_252609 := by decide
  rcases family_descends (prefixWord ++ tailWord_252609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252631 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_252631 : Nat := 118140960795 + 252631 * 2 ^ 59
def prefixEnd_252631 : Nat := 4983230072969 + 3 ^ 40 * 252631 * 2
def baseEnd_252631 : Nat := 129721131226106313750677

theorem tailTrace_252631 : CollatzResearch.WordTrace tailWord_252631 prefixEnd_252631 129721131226106313750677 := by
  unfold tailWord_252631
  simp only [CollatzResearch.WordTrace]
  refine ⟨9214209547768507784885747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6142806365179005189923831 9214209547768507784885747)
  ·
    refine ⟨13821314321652761677328621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9214209547768507784885747 13821314321652761677328621)
    ·
      refine ⟨5182992870619785628998233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13821314321652761677328621 5182992870619785628998233)
      ·
        refine ⟨3887244652964839221748675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5182992870619785628998233 3887244652964839221748675)
        ·
          refine ⟨5830866979447258832623013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887244652964839221748675 5830866979447258832623013)
          ·
            refine ⟨1093287558646361031116815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5830866979447258832623013 1093287558646361031116815)
            ·
              refine ⟨1639931337969541546675223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093287558646361031116815 1639931337969541546675223)
              ·
                refine ⟨2459897006954312320012835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639931337969541546675223 2459897006954312320012835)
                ·
                  refine ⟨3689845510431468480019253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459897006954312320012835 3689845510431468480019253)
                  ·
                    refine ⟨345923016602950170001805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3689845510431468480019253 345923016602950170001805)
                    ·
                      refine ⟨129721131226106313750677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 345923016602950170001805 129721131226106313750677)
                      ·
                        rfl

theorem cell23_252631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_252631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252631 prefixEnd_252631 := by exact prefixLift 252631
  have htrace : WordTrace (prefixWord ++ tailWord_252631) baseStart_252631 baseEnd_252631 := by
    simpa [prefixWord, tailWord_252631, baseEnd_252631] using wordTrace_append hprefix tailTrace_252631
  have hstable : (prefixWord ++ tailWord_252631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252631).length < 2 ^ (prefixWord ++ tailWord_252631).sum := by decide
  have hdescent : baseEnd_252631 < baseStart_252631 := by decide
  rcases family_descends (prefixWord ++ tailWord_252631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252671 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_252671 : Nat := 118140960795 + 252671 * 2 ^ 59
def prefixEnd_252671 : Nat := 4983230072969 + 3 ^ 40 * 252671 * 2
def baseEnd_252671 : Nat := 129741670452286157250493

theorem tailTrace_252671 : CollatzResearch.WordTrace tailWord_252671 prefixEnd_252671 129741670452286157250493 := by
  unfold tailWord_252671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215668467623594616341867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6143778978415729744227911 9215668467623594616341867)
  ·
    refine ⟨13823502701435391924512801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9215668467623594616341867 13823502701435391924512801)
    ·
      refine ⟨10367627026076543943384601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13823502701435391924512801 10367627026076543943384601)
      ·
        refine ⟨7775720269557407957538451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10367627026076543943384601 7775720269557407957538451)
        ·
          refine ⟨11663580404336111936307677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775720269557407957538451 11663580404336111936307677)
          ·
            refine ⟨4373842651626041976115379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11663580404336111936307677 4373842651626041976115379)
            ·
              refine ⟨6560763977439062964173069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373842651626041976115379 6560763977439062964173069)
              ·
                refine ⟨2460286491539648611564901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6560763977439062964173069 2460286491539648611564901)
                ·
                  refine ⟨461303717163684114668419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460286491539648611564901 461303717163684114668419)
                  ·
                    refine ⟨691955575745526172002629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 461303717163684114668419 691955575745526172002629)
                    ·
                      refine ⟨129741670452286157250493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 691955575745526172002629 129741670452286157250493)
                      ·
                        rfl

theorem cell23_252671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_252671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252671 prefixEnd_252671 := by exact prefixLift 252671
  have htrace : WordTrace (prefixWord ++ tailWord_252671) baseStart_252671 baseEnd_252671 := by
    simpa [prefixWord, tailWord_252671, baseEnd_252671] using wordTrace_append hprefix tailTrace_252671
  have hstable : (prefixWord ++ tailWord_252671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252671).length < 2 ^ (prefixWord ++ tailWord_252671).sum := by decide
  have hdescent : baseEnd_252671 < baseStart_252671 := by decide
  rcases family_descends (prefixWord ++ tailWord_252671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252691 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3]
def baseStart_252691 : Nat := 118140960795 + 252691 * 2 ^ 59
def prefixEnd_252691 : Nat := 4983230072969 + 3 ^ 40 * 252691 * 2
def baseEnd_252691 : Nat := 129751940065376079000401

theorem tailTrace_252691 : CollatzResearch.WordTrace tailWord_252691 prefixEnd_252691 129751940065376079000401 := by
  unfold tailWord_252691
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216397927551138032069927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6144265285034092021379951 9216397927551138032069927)
  ·
    refine ⟨13824596891326707048104891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9216397927551138032069927 13824596891326707048104891)
    ·
      refine ⟨20736895336990060572157337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13824596891326707048104891 20736895336990060572157337)
      ·
        refine ⟨15552671502742545429118003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20736895336990060572157337 15552671502742545429118003)
        ·
          refine ⟨23329007254113818143677005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552671502742545429118003 23329007254113818143677005)
          ·
            refine ⟨8748377720292681803878877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23329007254113818143677005 8748377720292681803878877)
            ·
              refine ⟨3280641645109755676454579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8748377720292681803878877 3280641645109755676454579)
              ·
                refine ⟨4920962467664633514681869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280641645109755676454579 4920962467664633514681869)
                ·
                  refine ⟨1845360925374237568005701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4920962467664633514681869 1845360925374237568005701)
                  ·
                    refine ⟨346005173507669544001069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845360925374237568005701 346005173507669544001069)
                    ·
                      refine ⟨129751940065376079000401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346005173507669544001069 129751940065376079000401)
                      ·
                        rfl

theorem cell23_252691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_252691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252691 prefixEnd_252691 := by exact prefixLift 252691
  have htrace : WordTrace (prefixWord ++ tailWord_252691) baseStart_252691 baseEnd_252691 := by
    simpa [prefixWord, tailWord_252691, baseEnd_252691] using wordTrace_append hprefix tailTrace_252691
  have hstable : (prefixWord ++ tailWord_252691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252691).length < 2 ^ (prefixWord ++ tailWord_252691).sum := by decide
  have hdescent : baseEnd_252691 < baseStart_252691 := by decide
  rcases family_descends (prefixWord ++ tailWord_252691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252698 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_252698 : Nat := 118140960795 + 252698 * 2 ^ 59
def prefixEnd_252698 : Nat := 4983230072969 + 3 ^ 40 * 252698 * 2
def baseEnd_252698 : Nat := 43251844809985850537623

theorem tailTrace_252698 : CollatzResearch.WordTrace tailWord_252698 prefixEnd_252698 43251844809985850537623 := by
  unfold tailWord_252698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304163309631444556893687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6144435492350518818383165 2304163309631444556893687)
  ·
    refine ⟨3456244964447166835340531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304163309631444556893687 3456244964447166835340531)
    ·
      refine ⟨5184367446670750253010797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3456244964447166835340531 5184367446670750253010797)
      ·
        refine ⟨1944137792501531344879049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5184367446670750253010797 1944137792501531344879049)
        ·
          refine ⟨1458103344376148508659287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944137792501531344879049 1458103344376148508659287)
          ·
            refine ⟨2187155016564222762988931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458103344376148508659287 2187155016564222762988931)
            ·
              refine ⟨3280732524846334144483397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187155016564222762988931 3280732524846334144483397)
              ·
                refine ⟨615137348408687652090637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3280732524846334144483397 615137348408687652090637)
                ·
                  refine ⟨230676505653257869533989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615137348408687652090637 230676505653257869533989)
                  ·
                    refine ⟨43251844809985850537623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230676505653257869533989 43251844809985850537623)
                    ·
                      rfl

theorem cell23_252698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_252698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252698 prefixEnd_252698 := by exact prefixLift 252698
  have htrace : WordTrace (prefixWord ++ tailWord_252698) baseStart_252698 baseEnd_252698 := by
    simpa [prefixWord, tailWord_252698, baseEnd_252698] using wordTrace_append hprefix tailTrace_252698
  have hstable : (prefixWord ++ tailWord_252698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252698).length < 2 ^ (prefixWord ++ tailWord_252698).sum := by decide
  have hdescent : baseEnd_252698 < baseStart_252698 := by decide
  rcases family_descends (prefixWord ++ tailWord_252698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252725 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_252725 : Nat := 118140960795 + 252725 * 2 ^ 59
def prefixEnd_252725 : Nat := 4983230072969 + 3 ^ 40 * 252725 * 2
def baseEnd_252725 : Nat := 129769398407628945975245

theorem tailTrace_252725 : CollatzResearch.WordTrace tailWord_252725 prefixEnd_252725 129769398407628945975245 := by
  unfold tailWord_252725
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217638009427961838807629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6145092006285307892538419 9217638009427961838807629)
  ·
    refine ⟨3456614253535485689552861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9217638009427961838807629 3456614253535485689552861)
    ·
      refine ⟨1296230345075807133582323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3456614253535485689552861 1296230345075807133582323)
      ·
        refine ⟨1944345517613710700373485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296230345075807133582323 1944345517613710700373485)
        ·
          refine ⟨729129569105141512640057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1944345517613710700373485 729129569105141512640057)
          ·
            refine ⟨546847176828856134480043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729129569105141512640057 546847176828856134480043)
            ·
              refine ⟨820270765243284201720065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546847176828856134480043 820270765243284201720065)
              ·
                refine ⟨615203073932463151290049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820270765243284201720065 615203073932463151290049)
                ·
                  refine ⟨461402305449347363467537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615203073932463151290049 461402305449347363467537)
                  ·
                    refine ⟨346051729087010522600653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461402305449347363467537 346051729087010522600653)
                    ·
                      refine ⟨129769398407628945975245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346051729087010522600653 129769398407628945975245)
                      ·
                        rfl

theorem cell23_252725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_252725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252725 prefixEnd_252725 := by exact prefixLift 252725
  have htrace : WordTrace (prefixWord ++ tailWord_252725) baseStart_252725 baseEnd_252725 := by
    simpa [prefixWord, tailWord_252725, baseEnd_252725] using wordTrace_append hprefix tailTrace_252725
  have hstable : (prefixWord ++ tailWord_252725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252725).length < 2 ^ (prefixWord ++ tailWord_252725).sum := by decide
  have hdescent : baseEnd_252725 < baseStart_252725 := by decide
  rcases family_descends (prefixWord ++ tailWord_252725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252745 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 6]
def baseStart_252745 : Nat := 118140960795 + 252745 * 2 ^ 59
def prefixEnd_252745 : Nat := 4983230072969 + 3 ^ 40 * 252745 * 2
def baseEnd_252745 : Nat := 14419963113413207525017

theorem tailTrace_252745 : CollatzResearch.WordTrace tailWord_252745 prefixEnd_252745 14419963113413207525017 := by
  unfold tailWord_252745
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218367469355505254535689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6145578312903670169690459 9218367469355505254535689)
  ·
    refine ⟨6913775602016628940901767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9218367469355505254535689 6913775602016628940901767)
    ·
      refine ⟨10370663403024943411352651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6913775602016628940901767 10370663403024943411352651)
      ·
        refine ⟨15555995104537415117028977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10370663403024943411352651 15555995104537415117028977)
        ·
          refine ⟨11666996328403061337771733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555995104537415117028977 11666996328403061337771733)
          ·
            refine ⟨273445226446946750104025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11666996328403061337771733 273445226446946750104025)
            ·
              refine ⟨205083919835210062578019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273445226446946750104025 205083919835210062578019)
              ·
                refine ⟨307625879752815093867029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205083919835210062578019 307625879752815093867029)
                ·
                  refine ⟨14419963113413207525017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307625879752815093867029 14419963113413207525017)
                  ·
                    rfl

theorem cell23_252745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 6].length) (baseStart_252745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252745 prefixEnd_252745 := by exact prefixLift 252745
  have htrace : WordTrace (prefixWord ++ tailWord_252745) baseStart_252745 baseEnd_252745 := by
    simpa [prefixWord, tailWord_252745, baseEnd_252745] using wordTrace_append hprefix tailTrace_252745
  have hstable : (prefixWord ++ tailWord_252745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252745).length < 2 ^ (prefixWord ++ tailWord_252745).sum := by decide
  have hdescent : baseEnd_252745 < baseStart_252745 := by decide
  rcases family_descends (prefixWord ++ tailWord_252745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252789 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_252789 : Nat := 118140960795 + 252789 * 2 ^ 59
def prefixEnd_252789 : Nat := 4983230072969 + 3 ^ 40 * 252789 * 2
def baseEnd_252789 : Nat := 129802261169516695574951

theorem tailTrace_252789 : CollatzResearch.WordTrace tailWord_252789 prefixEnd_252789 129802261169516695574951 := by
  unfold tailWord_252789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9219972281196100769137421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6146648187464067179424947 9219972281196100769137421)
  ·
    refine ⟨3457489605448537788426533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9219972281196100769137421 3457489605448537788426533)
    ·
      refine ⟨648279301021600835329975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3457489605448537788426533 648279301021600835329975)
      ·
        refine ⟨972418951532401252994963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648279301021600835329975 972418951532401252994963)
        ·
          refine ⟨1458628427298601879492445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972418951532401252994963 1458628427298601879492445)
          ·
            refine ⟨546985660236975704809667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1458628427298601879492445 546985660236975704809667)
            ·
              refine ⟨820478490355463557214501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546985660236975704809667 820478490355463557214501)
              ·
                refine ⟨153839716941649416977719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820478490355463557214501 153839716941649416977719)
                ·
                  refine ⟨230759575412474125466579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153839716941649416977719 230759575412474125466579)
                  ·
                    refine ⟨346139363118711188199869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230759575412474125466579 346139363118711188199869)
                    ·
                      refine ⟨129802261169516695574951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346139363118711188199869 129802261169516695574951)
                      ·
                        rfl

theorem cell23_252789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_252789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252789 prefixEnd_252789 := by exact prefixLift 252789
  have htrace : WordTrace (prefixWord ++ tailWord_252789) baseStart_252789 baseEnd_252789 := by
    simpa [prefixWord, tailWord_252789, baseEnd_252789] using wordTrace_append hprefix tailTrace_252789
  have hstable : (prefixWord ++ tailWord_252789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252789).length < 2 ^ (prefixWord ++ tailWord_252789).sum := by decide
  have hdescent : baseEnd_252789 < baseStart_252789 := by decide
  rcases family_descends (prefixWord ++ tailWord_252789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252791 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_252791 : Nat := 118140960795 + 252791 * 2 ^ 59
def prefixEnd_252791 : Nat := 4983230072969 + 3 ^ 40 * 252791 * 2
def baseEnd_252791 : Nat := 129803288130825687749941

theorem tailTrace_252791 : CollatzResearch.WordTrace tailWord_252791 prefixEnd_252791 129803288130825687749941 := by
  unfold tailWord_252791
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220045227188855110710227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6146696818125903407140151 9220045227188855110710227)
  ·
    refine ⟨13830067840783282666065341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9220045227188855110710227 13830067840783282666065341)
    ·
      refine ⟨5186275440293730999774503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13830067840783282666065341 5186275440293730999774503)
      ·
        refine ⟨7779413160440596499661755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5186275440293730999774503 7779413160440596499661755)
        ·
          refine ⟨11669119740660894749492633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7779413160440596499661755 11669119740660894749492633)
          ·
            refine ⟨8751839805495671062119475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11669119740660894749492633 8751839805495671062119475)
            ·
              refine ⟨13127759708243506593179213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751839805495671062119475 13127759708243506593179213)
              ·
                refine ⟨4922909890591314972442205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13127759708243506593179213 4922909890591314972442205)
                ·
                  refine ⟨1846091208971743114665827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4922909890591314972442205 1846091208971743114665827)
                  ·
                    refine ⟨2769136813457614671998741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1846091208971743114665827 2769136813457614671998741)
                    ·
                      refine ⟨129803288130825687749941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2769136813457614671998741 129803288130825687749941)
                      ·
                        rfl

theorem cell23_252791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_252791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252791 prefixEnd_252791 := by exact prefixLift 252791
  have htrace : WordTrace (prefixWord ++ tailWord_252791) baseStart_252791 baseEnd_252791 := by
    simpa [prefixWord, tailWord_252791, baseEnd_252791] using wordTrace_append hprefix tailTrace_252791
  have hstable : (prefixWord ++ tailWord_252791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252791).length < 2 ^ (prefixWord ++ tailWord_252791).sum := by decide
  have hdescent : baseEnd_252791 < baseStart_252791 := by decide
  rcases family_descends (prefixWord ++ tailWord_252791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252805 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_252805 : Nat := 118140960795 + 252805 * 2 ^ 59
def prefixEnd_252805 : Nat := 4983230072969 + 3 ^ 40 * 252805 * 2
def baseEnd_252805 : Nat := 43270158953329544324959

theorem tailTrace_252805 : CollatzResearch.WordTrace tailWord_252805 prefixEnd_252805 43270158953329544324959 := by
  unfold tailWord_252805
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220555849138135501719869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6147037232758757001146579 9220555849138135501719869)
  ·
    refine ⟨3457708443426800813144951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9220555849138135501719869 3457708443426800813144951)
    ·
      refine ⟨5186562665140201219717427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457708443426800813144951 5186562665140201219717427)
      ·
        refine ⟨7779843997710301829576141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5186562665140201219717427 7779843997710301829576141)
        ·
          refine ⟨2917441499141363186091053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7779843997710301829576141 2917441499141363186091053)
          ·
            refine ⟨1094040562178011194784145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2917441499141363186091053 1094040562178011194784145)
            ·
              refine ⟨820530421633508396088109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094040562178011194784145 820530421633508396088109)
              ·
                refine ⟨307698908112565648533041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 820530421633508396088109 307698908112565648533041)
                ·
                  refine ⟨230774181084424236399781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307698908112565648533041 230774181084424236399781)
                  ·
                    refine ⟨43270158953329544324959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230774181084424236399781 43270158953329544324959)
                    ·
                      rfl

theorem cell23_252805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_252805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252805 prefixEnd_252805 := by exact prefixLift 252805
  have htrace : WordTrace (prefixWord ++ tailWord_252805) baseStart_252805 baseEnd_252805 := by
    simpa [prefixWord, tailWord_252805, baseEnd_252805] using wordTrace_append hprefix tailTrace_252805
  have hstable : (prefixWord ++ tailWord_252805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252805).length < 2 ^ (prefixWord ++ tailWord_252805).sum := by decide
  have hdescent : baseEnd_252805 < baseStart_252805 := by decide
  rcases family_descends (prefixWord ++ tailWord_252805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252832 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3]
def baseStart_252832 : Nat := 118140960795 + 252832 * 2 ^ 59
def prefixEnd_252832 : Nat := 4983230072969 + 3 ^ 40 * 252832 * 2
def baseEnd_252832 : Nat := 129824340837660027337253

theorem tailTrace_252832 : CollatzResearch.WordTrace tailWord_252832 prefixEnd_252832 129824340837660027337253 := by
  unfold tailWord_252832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4610770310020159556476375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6147693746693546075301833 4610770310020159556476375)
  ·
    refine ⟨6916155465030239334714563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4610770310020159556476375 6916155465030239334714563)
    ·
      refine ⟨10374233197545359002071845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916155465030239334714563 10374233197545359002071845)
      ·
        refine ⟨1945168724539754812888471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10374233197545359002071845 1945168724539754812888471)
        ·
          refine ⟨2917753086809632219332707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945168724539754812888471 2917753086809632219332707)
          ·
            refine ⟨4376629630214448328999061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917753086809632219332707 4376629630214448328999061)
            ·
              refine ⟨205154513916302265421831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4376629630214448328999061 205154513916302265421831)
              ·
                refine ⟨307731770874453398132747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205154513916302265421831 307731770874453398132747)
                ·
                  refine ⟨461597656311680097199121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307731770874453398132747 461597656311680097199121)
                  ·
                    refine ⟨346198242233760072899341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461597656311680097199121 346198242233760072899341)
                    ·
                      refine ⟨129824340837660027337253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346198242233760072899341 129824340837660027337253)
                      ·
                        rfl

theorem cell23_252832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_252832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252832 prefixEnd_252832 := by exact prefixLift 252832
  have htrace : WordTrace (prefixWord ++ tailWord_252832) baseStart_252832 baseEnd_252832 := by
    simpa [prefixWord, tailWord_252832, baseEnd_252832] using wordTrace_append hprefix tailTrace_252832
  have hstable : (prefixWord ++ tailWord_252832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252832).length < 2 ^ (prefixWord ++ tailWord_252832).sum := by decide
  have hdescent : baseEnd_252832 < baseStart_252832 := by decide
  rcases family_descends (prefixWord ++ tailWord_252832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252839 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 2, 4]
def baseStart_252839 : Nat := 118140960795 + 252839 * 2 ^ 59
def prefixEnd_252839 : Nat := 4983230072969 + 3 ^ 40 * 252839 * 2
def baseEnd_252839 : Nat := 43275978400747166649907

theorem tailTrace_252839 : CollatzResearch.WordTrace tailWord_252839 prefixEnd_252839 43275978400747166649907 := by
  unfold tailWord_252839
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221795931014959308457571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6147863954009972872305047 9221795931014959308457571)
  ·
    refine ⟨13832693896522438962686357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9221795931014959308457571 13832693896522438962686357)
    ·
      refine ⟨648407526399489326375923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13832693896522438962686357 648407526399489326375923)
      ·
        refine ⟨972611289599233989563885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648407526399489326375923 972611289599233989563885)
        ·
          refine ⟨364729233599712746086457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972611289599233989563885 364729233599712746086457)
          ·
            refine ⟨273546925199784559564843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364729233599712746086457 273546925199784559564843)
            ·
              refine ⟨410320387799676839347265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273546925199784559564843 410320387799676839347265)
              ·
                refine ⟨307740290849757629510449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410320387799676839347265 307740290849757629510449)
                ·
                  refine ⟨230805218137318222132837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307740290849757629510449 230805218137318222132837)
                  ·
                    refine ⟨43275978400747166649907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230805218137318222132837 43275978400747166649907)
                    ·
                      rfl

theorem cell23_252839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_252839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252839 prefixEnd_252839 := by exact prefixLift 252839
  have htrace : WordTrace (prefixWord ++ tailWord_252839) baseStart_252839 baseEnd_252839 := by
    simpa [prefixWord, tailWord_252839, baseEnd_252839] using wordTrace_append hprefix tailTrace_252839
  have hstable : (prefixWord ++ tailWord_252839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252839).length < 2 ^ (prefixWord ++ tailWord_252839).sum := by decide
  have hdescent : baseEnd_252839 < baseStart_252839 := by decide
  rcases family_descends (prefixWord ++ tailWord_252839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252855 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_252855 : Nat := 118140960795 + 252855 * 2 ^ 59
def prefixEnd_252855 : Nat := 4983230072969 + 3 ^ 40 * 252855 * 2
def baseEnd_252855 : Nat := 129836150892713437349647

theorem tailTrace_252855 : CollatzResearch.WordTrace tailWord_252855 prefixEnd_252855 129836150892713437349647 := by
  unfold tailWord_252855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9222379498956994041040019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6148252999304662694026679 9222379498956994041040019)
  ·
    refine ⟨13833569248435491061560029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9222379498956994041040019 13833569248435491061560029)
    ·
      refine ⟨5187588468163309148085011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13833569248435491061560029 5187588468163309148085011)
      ·
        refine ⟨7781382702244963722127517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187588468163309148085011 7781382702244963722127517)
        ·
          refine ⟨2918018513341861395797819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7781382702244963722127517 2918018513341861395797819)
          ·
            refine ⟨4377027770012792093696729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918018513341861395797819 4377027770012792093696729)
            ·
              refine ⟨3282770827509594070272547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377027770012792093696729 3282770827509594070272547)
              ·
                refine ⟨4924156241264391105408821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282770827509594070272547 4924156241264391105408821)
                ·
                  refine ⟨461639647618536666132077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4924156241264391105408821 461639647618536666132077)
                  ·
                    refine ⟨173114867856951249799529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461639647618536666132077 173114867856951249799529)
                    ·
                      refine ⟨129836150892713437349647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173114867856951249799529 129836150892713437349647)
                      ·
                        rfl

theorem cell23_252855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_252855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252855 prefixEnd_252855 := by exact prefixLift 252855
  have htrace : WordTrace (prefixWord ++ tailWord_252855) baseStart_252855 baseEnd_252855 := by
    simpa [prefixWord, tailWord_252855, baseEnd_252855] using wordTrace_append hprefix tailTrace_252855
  have hstable : (prefixWord ++ tailWord_252855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252855).length < 2 ^ (prefixWord ++ tailWord_252855).sum := by decide
  have hdescent : baseEnd_252855 < baseStart_252855 := by decide
  rcases family_descends (prefixWord ++ tailWord_252855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252888 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_252888 : Nat := 118140960795 + 252888 * 2 ^ 59
def prefixEnd_252888 : Nat := 4983230072969 + 3 ^ 40 * 252888 * 2
def baseEnd_252888 : Nat := 129853095754311808236995

theorem tailTrace_252888 : CollatzResearch.WordTrace tailWord_252888 prefixEnd_252888 129853095754311808236995 := by
  unfold tailWord_252888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611791553918720338495659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6149055405224960451327545 4611791553918720338495659)
  ·
    refine ⟨6917687330878080507743489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4611791553918720338495659 6917687330878080507743489)
    ·
      refine ⟨5188265498158560380807617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6917687330878080507743489 5188265498158560380807617)
      ·
        refine ⟨3891199123618920285605713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5188265498158560380807617 3891199123618920285605713)
        ·
          refine ⟨2918399342714190214204285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891199123618920285605713 2918399342714190214204285)
          ·
            refine ⟨1094399753517821330326607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2918399342714190214204285 1094399753517821330326607)
            ·
              refine ⟨1641599630276731995489911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094399753517821330326607 1641599630276731995489911)
              ·
                refine ⟨2462399445415097993234867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641599630276731995489911 2462399445415097993234867)
                ·
                  refine ⟨3693599168122646989852301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462399445415097993234867 3693599168122646989852301)
                  ·
                    refine ⟨1385099688045992621194613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693599168122646989852301 1385099688045992621194613)
                    ·
                      refine ⟨129853095754311808236995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1385099688045992621194613 129853095754311808236995)
                      ·
                        rfl

theorem cell23_252888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_252888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252888 prefixEnd_252888 := by exact prefixLift 252888
  have htrace : WordTrace (prefixWord ++ tailWord_252888) baseStart_252888 baseEnd_252888 := by
    simpa [prefixWord, tailWord_252888, baseEnd_252888] using wordTrace_append hprefix tailTrace_252888
  have hstable : (prefixWord ++ tailWord_252888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252888).length < 2 ^ (prefixWord ++ tailWord_252888).sum := by decide
  have hdescent : baseEnd_252888 < baseStart_252888 := by decide
  rcases family_descends (prefixWord ++ tailWord_252888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252945 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_252945 : Nat := 118140960795 + 252945 * 2 ^ 59
def prefixEnd_252945 : Nat := 4983230072969 + 3 ^ 40 * 252945 * 2
def baseEnd_252945 : Nat := 129882364151618085224233

theorem tailTrace_252945 : CollatzResearch.WordTrace tailWord_252945 prefixEnd_252945 129882364151618085224233 := by
  unfold tailWord_252945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9225662068630939411816289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6150441379087292941210859 9225662068630939411816289)
  ·
    refine ⟨6919246551473204558862217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9225662068630939411816289 6919246551473204558862217)
    ·
      refine ⟨5189434913604903419146663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6919246551473204558862217 5189434913604903419146663)
      ·
        refine ⟨7784152370407355128719995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189434913604903419146663 7784152370407355128719995)
        ·
          refine ⟨11676228555611032693079993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784152370407355128719995 11676228555611032693079993)
          ·
            refine ⟨8757171416708274519809995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11676228555611032693079993 8757171416708274519809995)
            ·
              refine ⟨13135757125062411779714993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757171416708274519809995 13135757125062411779714993)
              ·
                refine ⟨9851817843796808834786245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135757125062411779714993 9851817843796808834786245)
                ·
                  refine ⟨1847215845711901656522421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9851817843796808834786245 1847215845711901656522421)
                  ·
                    refine ⟨173176485535490780298977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1847215845711901656522421 173176485535490780298977)
                    ·
                      refine ⟨129882364151618085224233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173176485535490780298977 129882364151618085224233)
                      ·
                        rfl

theorem cell23_252945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_252945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252945 prefixEnd_252945 := by exact prefixLift 252945
  have htrace : WordTrace (prefixWord ++ tailWord_252945) baseStart_252945 baseEnd_252945 := by
    simpa [prefixWord, tailWord_252945, baseEnd_252945] using wordTrace_append hprefix tailTrace_252945
  have hstable : (prefixWord ++ tailWord_252945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252945).length < 2 ^ (prefixWord ++ tailWord_252945).sum := by decide
  have hdescent : baseEnd_252945 < baseStart_252945 := by decide
  rcases family_descends (prefixWord ++ tailWord_252945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252959 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 5]
def baseStart_252959 : Nat := 118140960795 + 252959 * 2 ^ 59
def prefixEnd_252959 : Nat := 4983230072969 + 3 ^ 40 * 252959 * 2
def baseEnd_252959 : Nat := 14432172542309003383241

theorem tailTrace_252959 : CollatzResearch.WordTrace tailWord_252959 prefixEnd_252959 14432172542309003383241 := by
  unfold tailWord_252959
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226172690580219802825931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6150781793720146535217287 9226172690580219802825931)
  ·
    refine ⟨13839259035870329704238897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226172690580219802825931 13839259035870329704238897)
    ·
      refine ⟨10379444276902747278179173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13839259035870329704238897 10379444276902747278179173)
      ·
        refine ⟨1946145801919265114658595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10379444276902747278179173 1946145801919265114658595)
        ·
          refine ⟨2919218702878897671987893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946145801919265114658595 2919218702878897671987893)
          ·
            refine ⟨273676753394896656748865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2919218702878897671987893 273676753394896656748865)
            ·
              refine ⟨205257565046172492561649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273676753394896656748865 205257565046172492561649)
              ·
                refine ⟨153943173784629369421237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205257565046172492561649 153943173784629369421237)
                ·
                  refine ⟨14432172542309003383241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153943173784629369421237 14432172542309003383241)
                  ·
                    rfl

theorem cell23_252959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 5].length) (baseStart_252959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252959 prefixEnd_252959 := by exact prefixLift 252959
  have htrace : WordTrace (prefixWord ++ tailWord_252959) baseStart_252959 baseEnd_252959 := by
    simpa [prefixWord, tailWord_252959, baseEnd_252959] using wordTrace_append hprefix tailTrace_252959
  have hstable : (prefixWord ++ tailWord_252959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252959).length < 2 ^ (prefixWord ++ tailWord_252959).sum := by decide
  have hdescent : baseEnd_252959 < baseStart_252959 := by decide
  rcases family_descends (prefixWord ++ tailWord_252959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252962 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_252962 : Nat := 118140960795 + 252962 * 2 ^ 59
def prefixEnd_252962 : Nat := 4983230072969 + 3 ^ 40 * 252962 * 2
def baseEnd_252962 : Nat := 129891093322744518711655

theorem tailTrace_252962 : CollatzResearch.WordTrace tailWord_252962 prefixEnd_252962 129891093322744518711655 := by
  unfold tailWord_252962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306570527392337828796285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6150854739712900876790093 2306570527392337828796285)
  ·
    refine ⟨864963947772126685798607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2306570527392337828796285 864963947772126685798607)
    ·
      refine ⟨1297445921658190028697911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864963947772126685798607 1297445921658190028697911)
      ·
        refine ⟨1946168882487285043046867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297445921658190028697911 1946168882487285043046867)
        ·
          refine ⟨2919253323730927564570301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946168882487285043046867 2919253323730927564570301)
          ·
            refine ⟨1094719996399097836713863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2919253323730927564570301 1094719996399097836713863)
            ·
              refine ⟨1642079994598646755070795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094719996399097836713863 1642079994598646755070795)
              ·
                refine ⟨2463119991897970132606193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642079994598646755070795 2463119991897970132606193)
                ·
                  refine ⟨1847339993923477599454645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463119991897970132606193 1847339993923477599454645)
                  ·
                    refine ⟨173188124430326024948873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1847339993923477599454645 173188124430326024948873)
                    ·
                      refine ⟨129891093322744518711655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173188124430326024948873 129891093322744518711655)
                      ·
                        rfl

theorem cell23_252962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_252962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252962 prefixEnd_252962 := by exact prefixLift 252962
  have htrace : WordTrace (prefixWord ++ tailWord_252962) baseStart_252962 baseEnd_252962 := by
    simpa [prefixWord, tailWord_252962, baseEnd_252962] using wordTrace_append hprefix tailTrace_252962
  have hstable : (prefixWord ++ tailWord_252962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252962).length < 2 ^ (prefixWord ++ tailWord_252962).sum := by decide
  have hdescent : baseEnd_252962 < baseStart_252962 := by decide
  rcases family_descends (prefixWord ++ tailWord_252962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252995 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3]
def baseStart_252995 : Nat := 118140960795 + 252995 * 2 ^ 59
def prefixEnd_252995 : Nat := 4983230072969 + 3 ^ 40 * 252995 * 2
def baseEnd_252995 : Nat := 129908038184342889599003

theorem tailTrace_252995 : CollatzResearch.WordTrace tailWord_252995 prefixEnd_252995 129908038184342889599003 := by
  unfold tailWord_252995
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227485718449797951136439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6151657145633198634090959 9227485718449797951136439)
  ·
    refine ⟨13841228577674696926704659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9227485718449797951136439 13841228577674696926704659)
    ·
      refine ⟨20761842866512045390056989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13841228577674696926704659 20761842866512045390056989)
      ·
        refine ⟨7785691074942017021271371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20761842866512045390056989 7785691074942017021271371)
        ·
          refine ⟨11678536612413025531907057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7785691074942017021271371 11678536612413025531907057)
          ·
            refine ⟨8758902459309769148930293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11678536612413025531907057 8758902459309769148930293)
            ·
              refine ⟨821147105560290857712215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8758902459309769148930293 821147105560290857712215)
              ·
                refine ⟨1231720658340436286568323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821147105560290857712215 1231720658340436286568323)
                ·
                  refine ⟨1847580987510654429852485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231720658340436286568323 1847580987510654429852485)
                  ·
                    refine ⟨346421435158247705597341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847580987510654429852485 346421435158247705597341)
                    ·
                      refine ⟨129908038184342889599003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346421435158247705597341 129908038184342889599003)
                      ·
                        rfl

theorem cell23_252995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_252995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_252995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_252995 prefixEnd_252995 := by exact prefixLift 252995
  have htrace : WordTrace (prefixWord ++ tailWord_252995) baseStart_252995 baseEnd_252995 := by
    simpa [prefixWord, tailWord_252995, baseEnd_252995] using wordTrace_append hprefix tailTrace_252995
  have hstable : (prefixWord ++ tailWord_252995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252995).length < 2 ^ (prefixWord ++ tailWord_252995).sum := by decide
  have hdescent : baseEnd_252995 < baseStart_252995 := by decide
  rcases family_descends (prefixWord ++ tailWord_252995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253012 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_253012 : Nat := 118140960795 + 253012 * 2 ^ 59
def prefixEnd_253012 : Nat := 4983230072969 + 3 ^ 40 * 253012 * 2
def baseEnd_253012 : Nat := 129916767355469323086425

theorem tailTrace_253012 : CollatzResearch.WordTrace tailWord_253012 prefixEnd_253012 129916767355469323086425 := by
  unfold tailWord_253012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614052879694104927252645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6152070506258806569670193 4614052879694104927252645)
  ·
    refine ⟨865134914942644673859871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4614052879694104927252645 865134914942644673859871)
    ·
      refine ⟨1297702372413967010789807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865134914942644673859871 1297702372413967010789807)
      ·
        refine ⟨1946553558620950516184711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297702372413967010789807 1946553558620950516184711)
        ·
          refine ⟨2919830337931425774277067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946553558620950516184711 2919830337931425774277067)
          ·
            refine ⟨4379745506897138661415601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919830337931425774277067 4379745506897138661415601)
            ·
              refine ⟨3284809130172853996061701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379745506897138661415601 3284809130172853996061701)
              ·
                refine ⟨615901711907410124261569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3284809130172853996061701 615901711907410124261569)
                ·
                  refine ⟨461926283930557593196177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615901711907410124261569 461926283930557593196177)
                  ·
                    refine ⟨346444712947918194897133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461926283930557593196177 346444712947918194897133)
                    ·
                      refine ⟨129916767355469323086425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346444712947918194897133 129916767355469323086425)
                      ·
                        rfl

theorem cell23_253012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_253012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253012 prefixEnd_253012 := by exact prefixLift 253012
  have htrace : WordTrace (prefixWord ++ tailWord_253012) baseStart_253012 baseEnd_253012 := by
    simpa [prefixWord, tailWord_253012, baseEnd_253012] using wordTrace_append hprefix tailTrace_253012
  have hstable : (prefixWord ++ tailWord_253012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253012).length < 2 ^ (prefixWord ++ tailWord_253012).sum := by decide
  have hdescent : baseEnd_253012 < baseStart_253012 := by decide
  rcases family_descends (prefixWord ++ tailWord_253012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253052 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_253052 : Nat := 118140960795 + 253052 * 2 ^ 59
def prefixEnd_253052 : Nat := 4983230072969 + 3 ^ 40 * 253052 * 2
def baseEnd_253052 : Nat := 129937306581649166586241

theorem tailTrace_253052 : CollatzResearch.WordTrace tailWord_253052 prefixEnd_253052 129937306581649166586241 := by
  unfold tailWord_253052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614782339621648342980705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6153043119495531123974273 4614782339621648342980705)
  ·
    refine ⟨3461086754716236257235529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4614782339621648342980705 3461086754716236257235529)
    ·
      refine ⟨2595815066037177192926647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3461086754716236257235529 2595815066037177192926647)
      ·
        refine ⟨3893722599055765789389971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595815066037177192926647 3893722599055765789389971)
        ·
          refine ⟨5840583898583648684084957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893722599055765789389971 5840583898583648684084957)
          ·
            refine ⟨2190218961968868256531859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5840583898583648684084957 2190218961968868256531859)
            ·
              refine ⟨3285328442953302384797789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190218961968868256531859 3285328442953302384797789)
              ·
                refine ⟨1231998166107488394299171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3285328442953302384797789 1231998166107488394299171)
                ·
                  refine ⟨1847997249161232591448757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231998166107488394299171 1847997249161232591448757)
                  ·
                    refine ⟨173249742108865555448321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1847997249161232591448757 173249742108865555448321)
                    ·
                      refine ⟨129937306581649166586241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173249742108865555448321 129937306581649166586241)
                      ·
                        rfl

theorem cell23_253052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_253052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253052 prefixEnd_253052 := by exact prefixLift 253052
  have htrace : WordTrace (prefixWord ++ tailWord_253052) baseStart_253052 baseEnd_253052 := by
    simpa [prefixWord, tailWord_253052, baseEnd_253052] using wordTrace_append hprefix tailTrace_253052
  have hstable : (prefixWord ++ tailWord_253052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253052).length < 2 ^ (prefixWord ++ tailWord_253052).sum := by decide
  have hdescent : baseEnd_253052 < baseStart_253052 := by decide
  rcases family_descends (prefixWord ++ tailWord_253052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253116 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_253116 : Nat := 118140960795 + 253116 * 2 ^ 59
def prefixEnd_253116 : Nat := 4983230072969 + 3 ^ 40 * 253116 * 2
def baseEnd_253116 : Nat := 129970169343536916185947

theorem tailTrace_253116 : CollatzResearch.WordTrace tailWord_253116 prefixEnd_253116 129970169343536916185947 := by
  unfold tailWord_253116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615949475505717808145601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6154599300674290410860801 4615949475505717808145601)
  ·
    refine ⟨3461962106629288356109201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4615949475505717808145601 3461962106629288356109201)
    ·
      refine ⟨2596471579971966267081901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3461962106629288356109201 2596471579971966267081901)
      ·
        refine ⟨973676842489487350155713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2596471579971966267081901 973676842489487350155713)
        ·
          refine ⟨730257631867115512616785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973676842489487350155713 730257631867115512616785)
          ·
            refine ⟨547693223900336634462589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730257631867115512616785 547693223900336634462589)
            ·
              refine ⟨205384958962626237923471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547693223900336634462589 205384958962626237923471)
              ·
                refine ⟨308077438443939356885207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205384958962626237923471 308077438443939356885207)
                ·
                  refine ⟨462116157665909035327811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308077438443939356885207 462116157665909035327811)
                  ·
                    refine ⟨693174236498863552991717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462116157665909035327811 693174236498863552991717)
                    ·
                      refine ⟨129970169343536916185947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 693174236498863552991717 129970169343536916185947)
                      ·
                        rfl

theorem cell23_253116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_253116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253116 prefixEnd_253116 := by exact prefixLift 253116
  have htrace : WordTrace (prefixWord ++ tailWord_253116) baseStart_253116 baseEnd_253116 := by
    simpa [prefixWord, tailWord_253116, baseEnd_253116] using wordTrace_append hprefix tailTrace_253116
  have hstable : (prefixWord ++ tailWord_253116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253116).length < 2 ^ (prefixWord ++ tailWord_253116).sum := by decide
  have hdescent : baseEnd_253116 < baseStart_253116 := by decide
  rcases family_descends (prefixWord ++ tailWord_253116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253145 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_253145 : Nat := 118140960795 + 253145 * 2 ^ 59
def prefixEnd_253145 : Nat := 4983230072969 + 3 ^ 40 * 253145 * 2
def baseEnd_253145 : Nat := 129985060282517302723313

theorem tailTrace_253145 : CollatzResearch.WordTrace tailWord_253145 prefixEnd_253145 129985060282517302723313 := by
  unfold tailWord_253145
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232956667906373569096889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6155304445270915712731259 9232956667906373569096889)
  ·
    refine ⟨6924717500929780176822667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9232956667906373569096889 6924717500929780176822667)
    ·
      refine ⟨10387076251394670265234001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924717500929780176822667 10387076251394670265234001)
      ·
        refine ⟨7790307188546002698925501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10387076251394670265234001 7790307188546002698925501)
        ·
          refine ⟨2921365195704751012097063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7790307188546002698925501 2921365195704751012097063)
          ·
            refine ⟨4382047793557126518145595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921365195704751012097063 4382047793557126518145595)
            ·
              refine ⟨6573071690335689777218393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382047793557126518145595 6573071690335689777218393)
              ·
                refine ⟨4929803767751767332913795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573071690335689777218393 4929803767751767332913795)
                ·
                  refine ⟨7394705651627650999370693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929803767751767332913795 7394705651627650999370693)
                  ·
                    refine ⟨1386507309680184562382005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7394705651627650999370693 1386507309680184562382005)
                    ·
                      refine ⟨129985060282517302723313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1386507309680184562382005 129985060282517302723313)
                      ·
                        rfl

theorem cell23_253145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_253145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253145 prefixEnd_253145 := by exact prefixLift 253145
  have htrace : WordTrace (prefixWord ++ tailWord_253145) baseStart_253145 baseEnd_253145 := by
    simpa [prefixWord, tailWord_253145, baseEnd_253145] using wordTrace_append hprefix tailTrace_253145
  have hstable : (prefixWord ++ tailWord_253145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253145).length < 2 ^ (prefixWord ++ tailWord_253145).sum := by decide
  have hdescent : baseEnd_253145 < baseStart_253145 := by decide
  rcases family_descends (prefixWord ++ tailWord_253145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253170 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_253170 : Nat := 118140960795 + 253170 * 2 ^ 59
def prefixEnd_253170 : Nat := 4983230072969 + 3 ^ 40 * 253170 * 2
def baseEnd_253170 : Nat := 129997897298879704910699

theorem tailTrace_253170 : CollatzResearch.WordTrace tailWord_253170 prefixEnd_253170 129997897298879704910699 := by
  unfold tailWord_253170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308467123203950709689241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6155912328543868559171309 2308467123203950709689241)
  ·
    refine ⟨1731350342402963032266931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2308467123203950709689241 1731350342402963032266931)
    ·
      refine ⟨2597025513604444548400397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731350342402963032266931 2597025513604444548400397)
      ·
        refine ⟨973884567601666705650149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2597025513604444548400397 973884567601666705650149)
        ·
          refine ⟨182603356425312507309403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 973884567601666705650149 182603356425312507309403)
          ·
            refine ⟨273905034637968760964105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182603356425312507309403 273905034637968760964105)
            ·
              refine ⟨205428775978476570723079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273905034637968760964105 205428775978476570723079)
              ·
                refine ⟨308143163967714856084619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205428775978476570723079 308143163967714856084619)
                ·
                  refine ⟨462214745951572284126929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308143163967714856084619 462214745951572284126929)
                  ·
                    refine ⟨346661059463679213095197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462214745951572284126929 346661059463679213095197)
                    ·
                      refine ⟨129997897298879704910699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 346661059463679213095197 129997897298879704910699)
                      ·
                        rfl

theorem cell23_253170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_253170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253170 prefixEnd_253170 := by exact prefixLift 253170
  have htrace : WordTrace (prefixWord ++ tailWord_253170) baseStart_253170 baseEnd_253170 := by
    simpa [prefixWord, tailWord_253170, baseEnd_253170] using wordTrace_append hprefix tailTrace_253170
  have hstable : (prefixWord ++ tailWord_253170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253170).length < 2 ^ (prefixWord ++ tailWord_253170).sum := by decide
  have hdescent : baseEnd_253170 < baseStart_253170 := by decide
  rcases family_descends (prefixWord ++ tailWord_253170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253212 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 7]
def baseStart_253212 : Nat := 118140960795 + 253212 * 2 ^ 59
def prefixEnd_253212 : Nat := 4983230072969 + 3 ^ 40 * 253212 * 2
def baseEnd_253212 : Nat := 14446607054040948953945

theorem tailTrace_253212 : CollatzResearch.WordTrace tailWord_253212 prefixEnd_253212 14446607054040948953945 := by
  unfold tailWord_253212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617700179331822005892945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6156933572442429341190593 4617700179331822005892945)
  ·
    refine ⟨3463275134498866504419709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4617700179331822005892945 3463275134498866504419709)
    ·
      refine ⟨1298728175437074939157391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3463275134498866504419709 1298728175437074939157391)
      ·
        refine ⟨1948092263155612408736087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298728175437074939157391 1948092263155612408736087)
        ·
          refine ⟨2922138394733418613104131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948092263155612408736087 2922138394733418613104131)
          ·
            refine ⟨4383207592100127919656197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922138394733418613104131 4383207592100127919656197)
            ·
              refine ⟨821851423518773984935537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4383207592100127919656197 821851423518773984935537)
              ·
                refine ⟨616388567639080488701653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821851423518773984935537 616388567639080488701653)
                ·
                  refine ⟨14446607054040948953945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 616388567639080488701653 14446607054040948953945)
                  ·
                    rfl

theorem cell23_253212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_253212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253212 prefixEnd_253212 := by exact prefixLift 253212
  have htrace : WordTrace (prefixWord ++ tailWord_253212) baseStart_253212 baseEnd_253212 := by
    simpa [prefixWord, tailWord_253212, baseEnd_253212] using wordTrace_append hprefix tailTrace_253212
  have hstable : (prefixWord ++ tailWord_253212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253212).length < 2 ^ (prefixWord ++ tailWord_253212).sum := by decide
  have hdescent : baseEnd_253212 < baseStart_253212 := by decide
  rcases family_descends (prefixWord ++ tailWord_253212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253279 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 4, 4, 2]
def baseStart_253279 : Nat := 118140960795 + 253279 * 2 ^ 59
def prefixEnd_253279 : Nat := 4983230072969 + 3 ^ 40 * 253279 * 2
def baseEnd_253279 : Nat := 130053866690219778447697

theorem tailTrace_253279 : CollatzResearch.WordTrace tailWord_253279 prefixEnd_253279 130053866690219778447697 := by
  unfold tailWord_253279
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237844049420914454474891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6158562699613942969649927 9237844049420914454474891)
  ·
    refine ⟨13856766074131371681712337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9237844049420914454474891 13856766074131371681712337)
    ·
      refine ⟨10392574555598528761284253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13856766074131371681712337 10392574555598528761284253)
      ·
        refine ⟨3897215458349448285481595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10392574555598528761284253 3897215458349448285481595)
        ·
          refine ⟨5845823187524172428222393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897215458349448285481595 5845823187524172428222393)
          ·
            refine ⟨4384367390643129321166795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845823187524172428222393 4384367390643129321166795)
            ·
              refine ⟨6576551085964693981750193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384367390643129321166795 6576551085964693981750193)
              ·
                refine ⟨4932413314473520486312645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576551085964693981750193 4932413314473520486312645)
                ·
                  refine ⟨924827496463785091183621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4932413314473520486312645 924827496463785091183621)
                  ·
                    refine ⟨173405155586959704596929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924827496463785091183621 173405155586959704596929)
                    ·
                      refine ⟨130053866690219778447697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173405155586959704596929 130053866690219778447697)
                      ·
                        rfl

theorem cell23_253279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_253279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253279 prefixEnd_253279 := by exact prefixLift 253279
  have htrace : WordTrace (prefixWord ++ tailWord_253279) baseStart_253279 baseEnd_253279 := by
    simpa [prefixWord, tailWord_253279, baseEnd_253279] using wordTrace_append hprefix tailTrace_253279
  have hstable : (prefixWord ++ tailWord_253279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253279).length < 2 ^ (prefixWord ++ tailWord_253279).sum := by decide
  have hdescent : baseEnd_253279 < baseStart_253279 := by decide
  rcases family_descends (prefixWord ++ tailWord_253279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253306 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_253306 : Nat := 118140960795 + 253306 * 2 ^ 59
def prefixEnd_253306 : Nat := 4983230072969 + 3 ^ 40 * 253306 * 2
def baseEnd_253306 : Nat := 43355910222630390936691

theorem tailTrace_253306 : CollatzResearch.WordTrace tailWord_253306 prefixEnd_253306 43355910222630390936691 := by
  unfold tailWord_253306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309707205080774516426943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6159219213548732043805181 2309707205080774516426943)
  ·
    refine ⟨3464560807621161774640415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2309707205080774516426943 3464560807621161774640415)
    ·
      refine ⟨5196841211431742661960623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464560807621161774640415 5196841211431742661960623)
      ·
        refine ⟨7795261817147613992940935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196841211431742661960623 7795261817147613992940935)
        ·
          refine ⟨11692892725721420989411403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7795261817147613992940935 11692892725721420989411403)
          ·
            refine ⟨17539339088582131484117105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11692892725721420989411403 17539339088582131484117105)
            ·
              refine ⟨13154504316436598613087829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17539339088582131484117105 13154504316436598613087829)
              ·
                refine ⟨154154347458241389997123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13154504316436598613087829 154154347458241389997123)
                ·
                  refine ⟨231231521187362084995685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154154347458241389997123 231231521187362084995685)
                  ·
                    refine ⟨43355910222630390936691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231231521187362084995685 43355910222630390936691)
                    ·
                      rfl

theorem cell23_253306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_253306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253306 prefixEnd_253306 := by exact prefixLift 253306
  have htrace : WordTrace (prefixWord ++ tailWord_253306) baseStart_253306 baseEnd_253306 := by
    simpa [prefixWord, tailWord_253306, baseEnd_253306] using wordTrace_append hprefix tailTrace_253306
  have hstable : (prefixWord ++ tailWord_253306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253306).length < 2 ^ (prefixWord ++ tailWord_253306).sum := by decide
  have hdescent : baseEnd_253306 < baseStart_253306 := by decide
  rcases family_descends (prefixWord ++ tailWord_253306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253313 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_253313 : Nat := 118140960795 + 253313 * 2 ^ 59
def prefixEnd_253313 : Nat := 4983230072969 + 3 ^ 40 * 253313 * 2
def baseEnd_253313 : Nat := 130071325032472645422541

theorem tailTrace_253313 : CollatzResearch.WordTrace tailWord_253313 prefixEnd_253313 130071325032472645422541 := by
  unfold tailWord_253313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239084131297738261212593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6159389420865158840808395 9239084131297738261212593)
  ·
    refine ⟨6929313098473303695909445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9239084131297738261212593 6929313098473303695909445)
    ·
      refine ⟨1299246205963744442983021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6929313098473303695909445 1299246205963744442983021)
      ·
        refine ⟨487217327236404166118633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1299246205963744442983021 487217327236404166118633)
        ·
          refine ⟨365412995427303124588975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487217327236404166118633 365412995427303124588975)
          ·
            refine ⟨548119493140954686883463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365412995427303124588975 548119493140954686883463)
            ·
              refine ⟨822179239711432030325195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548119493140954686883463 822179239711432030325195)
              ·
                refine ⟨1233268859567148045487793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822179239711432030325195 1233268859567148045487793)
                ·
                  refine ⟨924951644675361034115845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233268859567148045487793 924951644675361034115845)
                  ·
                    refine ⟨173428433376630193896721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924951644675361034115845 173428433376630193896721)
                    ·
                      refine ⟨130071325032472645422541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173428433376630193896721 130071325032472645422541)
                      ·
                        rfl

theorem cell23_253313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_253313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253313 prefixEnd_253313 := by exact prefixLift 253313
  have htrace : WordTrace (prefixWord ++ tailWord_253313) baseStart_253313 baseEnd_253313 := by
    simpa [prefixWord, tailWord_253313, baseEnd_253313] using wordTrace_append hprefix tailTrace_253313
  have hstable : (prefixWord ++ tailWord_253313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253313).length < 2 ^ (prefixWord ++ tailWord_253313).sum := by decide
  have hdescent : baseEnd_253313 < baseStart_253313 := by decide
  rcases family_descends (prefixWord ++ tailWord_253313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253319 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 6]
def baseStart_253319 : Nat := 118140960795 + 253319 * 2 ^ 59
def prefixEnd_253319 : Nat := 4983230072969 + 3 ^ 40 * 253319 * 2
def baseEnd_253319 : Nat := 14452711768488846883057

theorem tailTrace_253319 : CollatzResearch.WordTrace tailWord_253319 prefixEnd_253319 14452711768488846883057 := by
  unfold tailWord_253319
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239302969276001285931011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6159535312850667523954007 9239302969276001285931011)
  ·
    refine ⟨13858954453914001928896517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9239302969276001285931011 13858954453914001928896517)
    ·
      refine ⟨2598553960108875361668097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13858954453914001928896517 2598553960108875361668097)
      ·
        refine ⟨1948915470081656521251073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2598553960108875361668097 1948915470081656521251073)
        ·
          refine ⟨1461686602561242390938305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948915470081656521251073 1461686602561242390938305)
          ·
            refine ⟨1096264951920931793203729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461686602561242390938305 1096264951920931793203729)
            ·
              refine ⟨822198713940698844902797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096264951920931793203729 822198713940698844902797)
              ·
                refine ⟨308324517727762066838549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822198713940698844902797 308324517727762066838549)
                ·
                  refine ⟨14452711768488846883057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 308324517727762066838549 14452711768488846883057)
                  ·
                    rfl

theorem cell23_253319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 6].length) (baseStart_253319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253319 prefixEnd_253319 := by exact prefixLift 253319
  have htrace : WordTrace (prefixWord ++ tailWord_253319) baseStart_253319 baseEnd_253319 := by
    simpa [prefixWord, tailWord_253319, baseEnd_253319] using wordTrace_append hprefix tailTrace_253319
  have hstable : (prefixWord ++ tailWord_253319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253319).length < 2 ^ (prefixWord ++ tailWord_253319).sum := by decide
  have hdescent : baseEnd_253319 < baseStart_253319 := by decide
  rcases family_descends (prefixWord ++ tailWord_253319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253330 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_253330 : Nat := 118140960795 + 253330 * 2 ^ 59
def prefixEnd_253330 : Nat := 4983230072969 + 3 ^ 40 * 253330 * 2
def baseEnd_253330 : Nat := 130080054203599078909963

theorem tailTrace_253330 : CollatzResearch.WordTrace tailWord_253330 prefixEnd_253330 130080054203599078909963 := by
  unfold tailWord_253330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309926043059037541145361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6159802781490766776387629 2309926043059037541145361)
  ·
    refine ⟨1732444532294278155859021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2309926043059037541145361 1732444532294278155859021)
    ·
      refine ⟨649666699610354308447133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1732444532294278155859021 649666699610354308447133)
      ·
        refine ⟨243625012353882865667675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649666699610354308447133 243625012353882865667675)
        ·
          refine ⟨365437518530824298501513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243625012353882865667675 365437518530824298501513)
          ·
            refine ⟨274078138898118223876135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365437518530824298501513 274078138898118223876135)
            ·
              refine ⟨411117208347177335814203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274078138898118223876135 411117208347177335814203)
              ·
                refine ⟨616675812520766003721305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411117208347177335814203 616675812520766003721305)
                ·
                  refine ⟨462506859390574502790979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616675812520766003721305 462506859390574502790979)
                  ·
                    refine ⟨693760289085861754186469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462506859390574502790979 693760289085861754186469)
                    ·
                      refine ⟨130080054203599078909963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 693760289085861754186469 130080054203599078909963)
                      ·
                        rfl

theorem cell23_253330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_253330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253330 prefixEnd_253330 := by exact prefixLift 253330
  have htrace : WordTrace (prefixWord ++ tailWord_253330) baseStart_253330 baseEnd_253330 := by
    simpa [prefixWord, tailWord_253330, baseEnd_253330] using wordTrace_append hprefix tailTrace_253330
  have hstable : (prefixWord ++ tailWord_253330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253330).length < 2 ^ (prefixWord ++ tailWord_253330).sum := by decide
  have hdescent : baseEnd_253330 < baseStart_253330 := by decide
  rcases family_descends (prefixWord ++ tailWord_253330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253339 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 5, 2]
def baseStart_253339 : Nat := 118140960795 + 253339 * 2 ^ 59
def prefixEnd_253339 : Nat := 4983230072969 + 3 ^ 40 * 253339 * 2
def baseEnd_253339 : Nat := 130084675529489543697421

theorem tailTrace_253339 : CollatzResearch.WordTrace tailWord_253339 prefixEnd_253339 130084675529489543697421 := by
  unfold tailWord_253339
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240032429203544701659071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6160021619469029801106047 9240032429203544701659071)
  ·
    refine ⟨13860048643805317052488607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9240032429203544701659071 13860048643805317052488607)
    ·
      refine ⟨20790072965707975578732911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860048643805317052488607 20790072965707975578732911)
      ·
        refine ⟨31185109448561963368099367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20790072965707975578732911 31185109448561963368099367)
        ·
          refine ⟨46777664172842945052149051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31185109448561963368099367 46777664172842945052149051)
          ·
            refine ⟨70166496259264417578223577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46777664172842945052149051 70166496259264417578223577)
            ·
              refine ⟨52624872194448313183667683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70166496259264417578223577 52624872194448313183667683)
              ·
                refine ⟨78937308291672469775501525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52624872194448313183667683 78937308291672469775501525)
                ·
                  refine ⟨1850093163086073510363317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78937308291672469775501525 1850093163086073510363317)
                  ·
                    refine ⟨173446234039319391596561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1850093163086073510363317 173446234039319391596561)
                    ·
                      refine ⟨130084675529489543697421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173446234039319391596561 130084675529489543697421)
                      ·
                        rfl

theorem cell23_253339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5, 2].length) (baseStart_253339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253339 prefixEnd_253339 := by exact prefixLift 253339
  have htrace : WordTrace (prefixWord ++ tailWord_253339) baseStart_253339 baseEnd_253339 := by
    simpa [prefixWord, tailWord_253339, baseEnd_253339] using wordTrace_append hprefix tailTrace_253339
  have hstable : (prefixWord ++ tailWord_253339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253339).length < 2 ^ (prefixWord ++ tailWord_253339).sum := by decide
  have hdescent : baseEnd_253339 < baseStart_253339 := by decide
  rcases family_descends (prefixWord ++ tailWord_253339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253356 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_253356 : Nat := 118140960795 + 253356 * 2 ^ 59
def prefixEnd_253356 : Nat := 4983230072969 + 3 ^ 40 * 253356 * 2
def baseEnd_253356 : Nat := 130093404700615977184843

theorem tailTrace_253356 : CollatzResearch.WordTrace tailWord_253356 prefixEnd_253356 130093404700615977184843 := by
  unfold tailWord_253356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620326235070978302513961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6160434980094637736685281 4620326235070978302513961)
  ·
    refine ⟨3465244676303233726885471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4620326235070978302513961 3465244676303233726885471)
    ·
      refine ⟨5197867014454850590328207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465244676303233726885471 5197867014454850590328207)
      ·
        refine ⟨7796800521682275885492311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197867014454850590328207 7796800521682275885492311)
        ·
          refine ⟨11695200782523413828238467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796800521682275885492311 11695200782523413828238467)
          ·
            refine ⟨17542801173785120742357701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695200782523413828238467 17542801173785120742357701)
            ·
              refine ⟨3289275220084710139192069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17542801173785120742357701 3289275220084710139192069)
              ·
                refine ⟨616739103765883151098513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3289275220084710139192069 616739103765883151098513)
                ·
                  refine ⟨462554327824412363323885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616739103765883151098513 462554327824412363323885)
                  ·
                    refine ⟨173457872934154636246457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462554327824412363323885 173457872934154636246457)
                    ·
                      refine ⟨130093404700615977184843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173457872934154636246457 130093404700615977184843)
                      ·
                        rfl

theorem cell23_253356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_253356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253356 prefixEnd_253356 := by exact prefixLift 253356
  have htrace : WordTrace (prefixWord ++ tailWord_253356) baseStart_253356 baseEnd_253356 := by
    simpa [prefixWord, tailWord_253356, baseEnd_253356] using wordTrace_append hprefix tailTrace_253356
  have hstable : (prefixWord ++ tailWord_253356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253356).length < 2 ^ (prefixWord ++ tailWord_253356).sum := by decide
  have hdescent : baseEnd_253356 < baseStart_253356 := by decide
  rcases family_descends (prefixWord ++ tailWord_253356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253379 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 1, 6]
def baseStart_253379 : Nat := 118140960795 + 253379 * 2 ^ 59
def prefixEnd_253379 : Nat := 4983230072969 + 3 ^ 40 * 253379 * 2
def baseEnd_253379 : Nat := 43368404918556462399079

theorem tailTrace_253379 : CollatzResearch.WordTrace tailWord_253379 prefixEnd_253379 43368404918556462399079 := by
  unfold tailWord_253379
  simp only [CollatzResearch.WordTrace]
  refine ⟨9241491349058631533115191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6160994232705754355410127 9241491349058631533115191)
  ·
    refine ⟨13862237023587947299672787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9241491349058631533115191 13862237023587947299672787)
    ·
      refine ⟨20793355535381920949509181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862237023587947299672787 20793355535381920949509181)
      ·
        refine ⟨7797508325768220356065943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20793355535381920949509181 7797508325768220356065943)
        ·
          refine ⟨11696262488652330534098915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797508325768220356065943 11696262488652330534098915)
          ·
            refine ⟨17544393732978495801148373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696262488652330534098915 17544393732978495801148373)
            ·
              refine ⟨411196728116683495339415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17544393732978495801148373 411196728116683495339415)
              ·
                refine ⟨616795092175025243009123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411196728116683495339415 616795092175025243009123)
                ·
                  refine ⟨925192638262537864513685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616795092175025243009123 925192638262537864513685)
                  ·
                    refine ⟨43368404918556462399079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 925192638262537864513685 43368404918556462399079)
                    ·
                      rfl

theorem cell23_253379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 6].length) (baseStart_253379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253379 prefixEnd_253379 := by exact prefixLift 253379
  have htrace : WordTrace (prefixWord ++ tailWord_253379) baseStart_253379 baseEnd_253379 := by
    simpa [prefixWord, tailWord_253379, baseEnd_253379] using wordTrace_append hprefix tailTrace_253379
  have hstable : (prefixWord ++ tailWord_253379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253379).length < 2 ^ (prefixWord ++ tailWord_253379).sum := by decide
  have hdescent : baseEnd_253379 < baseStart_253379 := by decide
  rcases family_descends (prefixWord ++ tailWord_253379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253386 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_253386 : Nat := 118140960795 + 253386 * 2 ^ 59
def prefixEnd_253386 : Nat := 4983230072969 + 3 ^ 40 * 253386 * 2
def baseEnd_253386 : Nat := 130108809120250859809705

theorem tailTrace_253386 : CollatzResearch.WordTrace tailWord_253386 prefixEnd_253386 130108809120250859809705 := by
  unfold tailWord_253386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310436665008317932155003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6161164440022181152413341 2310436665008317932155003)
  ·
    refine ⟨3465654997512476898232505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2310436665008317932155003 3465654997512476898232505)
    ·
      refine ⟨2599241248134357673674379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3465654997512476898232505 2599241248134357673674379)
      ·
        refine ⟨3898861872201536510511569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599241248134357673674379 3898861872201536510511569)
        ·
          refine ⟨2924146404151152382883677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898861872201536510511569 2924146404151152382883677)
          ·
            refine ⟨1096554901556682143581379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2924146404151152382883677 1096554901556682143581379)
            ·
              refine ⟨1644832352335023215372069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096554901556682143581379 1644832352335023215372069)
              ·
                refine ⟨308406066062816852882263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1644832352335023215372069 308406066062816852882263)
                ·
                  refine ⟨462609099094225279323395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308406066062816852882263 462609099094225279323395)
                  ·
                    refine ⟨693913648641337918985093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462609099094225279323395 693913648641337918985093)
                    ·
                      refine ⟨130108809120250859809705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 693913648641337918985093 130108809120250859809705)
                      ·
                        rfl

theorem cell23_253386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_253386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253386 prefixEnd_253386 := by exact prefixLift 253386
  have htrace : WordTrace (prefixWord ++ tailWord_253386) baseStart_253386 baseEnd_253386 := by
    simpa [prefixWord, tailWord_253386, baseEnd_253386] using wordTrace_append hprefix tailTrace_253386
  have hstable : (prefixWord ++ tailWord_253386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253386).length < 2 ^ (prefixWord ++ tailWord_253386).sum := by decide
  have hdescent : baseEnd_253386 < baseStart_253386 := by decide
  rcases family_descends (prefixWord ++ tailWord_253386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253392 : List Nat := [2, 1, 1, 1, 1, 2, 2, 13]
def baseStart_253392 : Nat := 118140960795 + 253392 * 2 ^ 59
def prefixEnd_253392 : Nat := 4983230072969 + 3 ^ 40 * 253392 * 2
def baseEnd_253392 : Nat := 4818958889043623567951

theorem tailTrace_253392 : CollatzResearch.WordTrace tailWord_253392 prefixEnd_253392 4818958889043623567951 := by
  unfold tailWord_253392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620982749005767376669215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6161310332007689835558953 4620982749005767376669215)
  ·
    refine ⟨6931474123508651065003823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620982749005767376669215 6931474123508651065003823)
    ·
      refine ⟨10397211185262976597505735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6931474123508651065003823 10397211185262976597505735)
      ·
        refine ⟨15595816777894464896258603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10397211185262976597505735 15595816777894464896258603)
        ·
          refine ⟨23393725166841697344387905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15595816777894464896258603 23393725166841697344387905)
          ·
            refine ⟨17545293875131273008290929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23393725166841697344387905 17545293875131273008290929)
            ·
              refine ⟨13158970406348454756218197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17545293875131273008290929 13158970406348454756218197)
              ·
                refine ⟨4818958889043623567951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 13158970406348454756218197 4818958889043623567951)
                ·
                  rfl

theorem cell23_253392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 13].length) (baseStart_253392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253392 prefixEnd_253392 := by exact prefixLift 253392
  have htrace : WordTrace (prefixWord ++ tailWord_253392) baseStart_253392 baseEnd_253392 := by
    simpa [prefixWord, tailWord_253392, baseEnd_253392] using wordTrace_append hprefix tailTrace_253392
  have hstable : (prefixWord ++ tailWord_253392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253392).length < 2 ^ (prefixWord ++ tailWord_253392).sum := by decide
  have hdescent : baseEnd_253392 < baseStart_253392 := by decide
  rcases family_descends (prefixWord ++ tailWord_253392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253399 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_253399 : Nat := 118140960795 + 253399 * 2 ^ 59
def prefixEnd_253399 : Nat := 4983230072969 + 3 ^ 40 * 253399 * 2
def baseEnd_253399 : Nat := 130115484368759308947145

theorem tailTrace_253399 : CollatzResearch.WordTrace tailWord_253399 prefixEnd_253399 130115484368759308947145 := by
  unfold tailWord_253399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242220808986174948843251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6161480539324116632562167 9242220808986174948843251)
  ·
    refine ⟨13863331213479262423264877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9242220808986174948843251 13863331213479262423264877)
    ·
      refine ⟨5198749205054723408724329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13863331213479262423264877 5198749205054723408724329)
      ·
        refine ⟨3899061903791042556543247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5198749205054723408724329 3899061903791042556543247)
        ·
          refine ⟨5848592855686563834814871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899061903791042556543247 5848592855686563834814871)
          ·
            refine ⟨8772889283529845752222307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848592855686563834814871 8772889283529845752222307)
            ·
              refine ⟨13159333925294768628333461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772889283529845752222307 13159333925294768628333461)
              ·
                refine ⟨616843777748192279453131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13159333925294768628333461 616843777748192279453131)
                ·
                  refine ⟨925265666622288419179697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616843777748192279453131 925265666622288419179697)
                  ·
                    refine ⟨693949249966716314384773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 925265666622288419179697 693949249966716314384773)
                    ·
                      refine ⟨130115484368759308947145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 693949249966716314384773 130115484368759308947145)
                      ·
                        rfl

theorem cell23_253399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_253399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253399 prefixEnd_253399 := by exact prefixLift 253399
  have htrace : WordTrace (prefixWord ++ tailWord_253399) baseStart_253399 baseEnd_253399 := by
    simpa [prefixWord, tailWord_253399, baseEnd_253399] using wordTrace_append hprefix tailTrace_253399
  have hstable : (prefixWord ++ tailWord_253399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253399).length < 2 ^ (prefixWord ++ tailWord_253399).sum := by decide
  have hdescent : baseEnd_253399 < baseStart_253399 := by decide
  rcases family_descends (prefixWord ++ tailWord_253399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253409 : List Nat := [1, 2, 3, 1, 2, 5, 9]
def baseStart_253409 : Nat := 118140960795 + 253409 * 2 ^ 59
def prefixEnd_253409 : Nat := 4983230072969 + 3 ^ 40 * 253409 * 2
def baseEnd_253409 : Nat := 1606427397225978639779

theorem tailTrace_253409 : CollatzResearch.WordTrace tailWord_253409 prefixEnd_253409 1606427397225978639779 := by
  unfold tailWord_253409
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242585538949946656707281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6161723692633297771138187 9242585538949946656707281)
  ·
    refine ⟨6931939154212459992530461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9242585538949946656707281 6931939154212459992530461)
    ·
      refine ⟨2599477182829672497198923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6931939154212459992530461 2599477182829672497198923)
      ·
        refine ⟨3899215774244508745798385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599477182829672497198923 3899215774244508745798385)
        ·
          refine ⟨2924411830683381559348789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899215774244508745798385 2924411830683381559348789)
          ·
            refine ⟨274163609126567021188949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2924411830683381559348789 274163609126567021188949)
            ·
              refine ⟨1606427397225978639779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 274163609126567021188949 1606427397225978639779)
              ·
                rfl

theorem cell23_253409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 9].length) (baseStart_253409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253409 prefixEnd_253409 := by exact prefixLift 253409
  have htrace : WordTrace (prefixWord ++ tailWord_253409) baseStart_253409 baseEnd_253409 := by
    simpa [prefixWord, tailWord_253409, baseEnd_253409] using wordTrace_append hprefix tailTrace_253409
  have hstable : (prefixWord ++ tailWord_253409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253409).length < 2 ^ (prefixWord ++ tailWord_253409).sum := by decide
  have hdescent : baseEnd_253409 < baseStart_253409 := by decide
  rcases family_descends (prefixWord ++ tailWord_253409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253419 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3]
def baseStart_253419 : Nat := 118140960795 + 253419 * 2 ^ 59
def prefixEnd_253419 : Nat := 4983230072969 + 3 ^ 40 * 253419 * 2
def baseEnd_253419 : Nat := 130125753981849230697053

theorem tailTrace_253419 : CollatzResearch.WordTrace tailWord_253419 prefixEnd_253419 130125753981849230697053 := by
  unfold tailWord_253419
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242950268913718364571311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6161966845942478909714207 9242950268913718364571311)
  ·
    refine ⟨13864425403370577546856967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9242950268913718364571311 13864425403370577546856967)
    ·
      refine ⟨20796638105055866320285451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13864425403370577546856967 20796638105055866320285451)
      ·
        refine ⟨31194957157583799480428177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796638105055866320285451 31194957157583799480428177)
        ·
          refine ⟨23396217868187849610321133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31194957157583799480428177 23396217868187849610321133)
          ·
            refine ⟨8773581700570443603870425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23396217868187849610321133 8773581700570443603870425)
            ·
              refine ⟨6580186275427832702902819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8773581700570443603870425 6580186275427832702902819)
              ·
                refine ⟨9870279413141749054354229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580186275427832702902819 9870279413141749054354229)
                ·
                  refine ⟨925338694982038973845709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9870279413141749054354229 925338694982038973845709)
                  ·
                    refine ⟨347002010618264615192141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925338694982038973845709 347002010618264615192141)
                    ·
                      refine ⟨130125753981849230697053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347002010618264615192141 130125753981849230697053)
                      ·
                        rfl

theorem cell23_253419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3].length) (baseStart_253419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253419 prefixEnd_253419 := by exact prefixLift 253419
  have htrace : WordTrace (prefixWord ++ tailWord_253419) baseStart_253419 baseEnd_253419 := by
    simpa [prefixWord, tailWord_253419, baseEnd_253419] using wordTrace_append hprefix tailTrace_253419
  have hstable : (prefixWord ++ tailWord_253419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253419).length < 2 ^ (prefixWord ++ tailWord_253419).sum := by decide
  have hdescent : baseEnd_253419 < baseStart_253419 := by decide
  rcases family_descends (prefixWord ++ tailWord_253419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253426 : List Nat := [3, 2, 1, 4, 1, 2, 2, 8]
def baseStart_253426 : Nat := 118140960795 + 253426 * 2 ^ 59
def prefixEnd_253426 : Nat := 4983230072969 + 3 ^ 40 * 253426 * 2
def baseEnd_253426 : Nat := 4819605494312248270723

theorem tailTrace_253426 : CollatzResearch.WordTrace tailWord_253426 prefixEnd_253426 4819605494312248270723 := by
  unfold tailWord_253426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310801394972089640019033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6162137053258905706717421 2310801394972089640019033)
  ·
    refine ⟨1733101046229067230014275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2310801394972089640019033 1733101046229067230014275)
    ·
      refine ⟨2599651569343600845021413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733101046229067230014275 2599651569343600845021413)
      ·
        refine ⟨487434669251925158441515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2599651569343600845021413 487434669251925158441515)
        ·
          refine ⟨731152003877887737662273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487434669251925158441515 731152003877887737662273)
          ·
            refine ⟨548364002908415803246705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731152003877887737662273 548364002908415803246705)
            ·
              refine ⟨411273002181311852435029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548364002908415803246705 411273002181311852435029)
              ·
                refine ⟨4819605494312248270723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 411273002181311852435029 4819605494312248270723)
                ·
                  rfl

theorem cell23_253426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_253426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253426 prefixEnd_253426 := by exact prefixLift 253426
  have htrace : WordTrace (prefixWord ++ tailWord_253426) baseStart_253426 baseEnd_253426 := by
    simpa [prefixWord, tailWord_253426, baseEnd_253426] using wordTrace_append hprefix tailTrace_253426
  have hstable : (prefixWord ++ tailWord_253426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253426).length < 2 ^ (prefixWord ++ tailWord_253426).sum := by decide
  have hdescent : baseEnd_253426 < baseStart_253426 := by decide
  rcases family_descends (prefixWord ++ tailWord_253426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253430 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_253430 : Nat := 118140960795 + 253430 * 2 ^ 59
def prefixEnd_253430 : Nat := 4983230072969 + 3 ^ 40 * 253430 * 2
def baseEnd_253430 : Nat := 43377134089682895886501

theorem tailTrace_253430 : CollatzResearch.WordTrace tailWord_253430 prefixEnd_253430 43377134089682895886501 := by
  unfold tailWord_253430
  simp only [CollatzResearch.WordTrace]
  refine ⟨577709466992116702701359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6162234314582578162147829 577709466992116702701359)
  ·
    refine ⟨866564200488175054052039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577709466992116702701359 866564200488175054052039)
    ·
      refine ⟨1299846300732262581078059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866564200488175054052039 1299846300732262581078059)
      ·
        refine ⟨1949769451098393871617089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299846300732262581078059 1949769451098393871617089)
        ·
          refine ⟨1462327088323795403712817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949769451098393871617089 1462327088323795403712817)
          ·
            refine ⟨1096745316242846552784613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462327088323795403712817 1096745316242846552784613)
            ·
              refine ⟨205639746795533728647115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096745316242846552784613 205639746795533728647115)
              ·
                refine ⟨308459620193300592970673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205639746795533728647115 308459620193300592970673)
                ·
                  refine ⟨231344715144975444728005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308459620193300592970673 231344715144975444728005)
                  ·
                    refine ⟨43377134089682895886501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231344715144975444728005 43377134089682895886501)
                    ·
                      rfl

theorem cell23_253430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_253430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253430 prefixEnd_253430 := by exact prefixLift 253430
  have htrace : WordTrace (prefixWord ++ tailWord_253430) baseStart_253430 baseEnd_253430 := by
    simpa [prefixWord, tailWord_253430, baseEnd_253430] using wordTrace_append hprefix tailTrace_253430
  have hstable : (prefixWord ++ tailWord_253430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253430).length < 2 ^ (prefixWord ++ tailWord_253430).sum := by decide
  have hdescent : baseEnd_253430 < baseStart_253430 := by decide
  rcases family_descends (prefixWord ++ tailWord_253430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253486 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_253486 : Nat := 118140960795 + 253486 * 2 ^ 59
def prefixEnd_253486 : Nat := 4983230072969 + 3 ^ 40 * 253486 * 2
def baseEnd_253486 : Nat := 43386719061900156186415

theorem tailTrace_253486 : CollatzResearch.WordTrace tailWord_253486 prefixEnd_253486 43386719061900156186415 := by
  unfold tailWord_253486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155674244958873600907539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6163595973113992538173541 1155674244958873600907539)
  ·
    refine ⟨1733511367438310401361309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155674244958873600907539 1733511367438310401361309)
    ·
      refine ⟨650066762789366400510491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1733511367438310401361309 650066762789366400510491)
      ·
        refine ⟨975100144184049600765737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650066762789366400510491 975100144184049600765737)
        ·
          refine ⟨731325108138037200574303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975100144184049600765737 731325108138037200574303)
          ·
            refine ⟨1096987662207055800861455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731325108138037200574303 1096987662207055800861455)
            ·
              refine ⟨1645481493310583701292183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096987662207055800861455 1645481493310583701292183)
              ·
                refine ⟨2468222239965875551938275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645481493310583701292183 2468222239965875551938275)
                ·
                  refine ⟨3702333359948813327907413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468222239965875551938275 3702333359948813327907413)
                  ·
                    refine ⟨43386719061900156186415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3702333359948813327907413 43386719061900156186415)
                    ·
                      rfl

theorem cell23_253486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_253486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253486 prefixEnd_253486 := by exact prefixLift 253486
  have htrace : WordTrace (prefixWord ++ tailWord_253486) baseStart_253486 baseEnd_253486 := by
    simpa [prefixWord, tailWord_253486, baseEnd_253486] using wordTrace_append hprefix tailTrace_253486
  have hstable : (prefixWord ++ tailWord_253486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253486).length < 2 ^ (prefixWord ++ tailWord_253486).sum := by decide
  have hdescent : baseEnd_253486 < baseStart_253486 := by decide
  rcases family_descends (prefixWord ++ tailWord_253486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253493 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_253493 : Nat := 118140960795 + 253493 * 2 ^ 59
def prefixEnd_253493 : Nat := 4983230072969 + 3 ^ 40 * 253493 * 2
def baseEnd_253493 : Nat := 130163751550281941171713

theorem tailTrace_253493 : CollatzResearch.WordTrace tailWord_253493 prefixEnd_253493 130163751550281941171713 := by
  unfold tailWord_253493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245649270645629002765133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6163766180430419335176755 9245649270645629002765133)
  ·
    refine ⟨3467118476492110876036925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9245649270645629002765133 3467118476492110876036925)
    ·
      refine ⟨1300169428684541578513847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3467118476492110876036925 1300169428684541578513847)
      ·
        refine ⟨1950254143026812367770771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300169428684541578513847 1950254143026812367770771)
        ·
          refine ⟨2925381214540218551656157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950254143026812367770771 2925381214540218551656157)
          ·
            refine ⟨1097017955452581956871059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2925381214540218551656157 1097017955452581956871059)
            ·
              refine ⟨1645526933178872935306589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097017955452581956871059 1645526933178872935306589)
              ·
                refine ⟨617072599942077350739971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645526933178872935306589 617072599942077350739971)
                ·
                  refine ⟨925608899913116026109957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617072599942077350739971 925608899913116026109957)
                  ·
                    refine ⟨173551668733709254895617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925608899913116026109957 173551668733709254895617)
                    ·
                      refine ⟨130163751550281941171713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173551668733709254895617 130163751550281941171713)
                      ·
                        rfl

theorem cell23_253493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_253493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253493 prefixEnd_253493 := by exact prefixLift 253493
  have htrace : WordTrace (prefixWord ++ tailWord_253493) baseStart_253493 baseEnd_253493 := by
    simpa [prefixWord, tailWord_253493, baseEnd_253493] using wordTrace_append hprefix tailTrace_253493
  have hstable : (prefixWord ++ tailWord_253493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253493).length < 2 ^ (prefixWord ++ tailWord_253493).sum := by decide
  have hdescent : baseEnd_253493 < baseStart_253493 := by decide
  rcases family_descends (prefixWord ++ tailWord_253493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253527 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_253527 : Nat := 118140960795 + 253527 * 2 ^ 59
def prefixEnd_253527 : Nat := 4983230072969 + 3 ^ 40 * 253527 * 2
def baseEnd_253527 : Nat := 130181209892534808146557

theorem tailTrace_253527 : CollatzResearch.WordTrace tailWord_253527 prefixEnd_253527 130181209892534808146557 := by
  unfold tailWord_253527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9246889352522452809502835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6164592901681635206335223 9246889352522452809502835)
  ·
    refine ⟨13870334028783679214254253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9246889352522452809502835 13870334028783679214254253)
    ·
      refine ⟨5201375260793879705345345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13870334028783679214254253 5201375260793879705345345)
      ·
        refine ⟨3901031445595409779009009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201375260793879705345345 3901031445595409779009009)
        ·
          refine ⟨2925773584196557334256757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3901031445595409779009009 2925773584196557334256757)
          ·
            refine ⟨274291273518427250086571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2925773584196557334256757 274291273518427250086571)
            ·
              refine ⟨411436910277640875129857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274291273518427250086571 411436910277640875129857)
              ·
                refine ⟨308577682708230656347393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411436910277640875129857 308577682708230656347393)
                ·
                  refine ⟨231433262031172992260545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308577682708230656347393 231433262031172992260545)
                  ·
                    refine ⟨173574946523379744195409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231433262031172992260545 173574946523379744195409)
                    ·
                      refine ⟨130181209892534808146557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173574946523379744195409 130181209892534808146557)
                      ·
                        rfl

theorem cell23_253527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_253527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253527 prefixEnd_253527 := by exact prefixLift 253527
  have htrace : WordTrace (prefixWord ++ tailWord_253527) baseStart_253527 baseEnd_253527 := by
    simpa [prefixWord, tailWord_253527, baseEnd_253527] using wordTrace_append hprefix tailTrace_253527
  have hstable : (prefixWord ++ tailWord_253527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253527).length < 2 ^ (prefixWord ++ tailWord_253527).sum := by decide
  have hdescent : baseEnd_253527 < baseStart_253527 := by decide
  rcases family_descends (prefixWord ++ tailWord_253527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253544 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_253544 : Nat := 118140960795 + 253544 * 2 ^ 59
def prefixEnd_253544 : Nat := 4983230072969 + 3 ^ 40 * 253544 * 2
def baseEnd_253544 : Nat := 130189939063661241633979

theorem tailTrace_253544 : CollatzResearch.WordTrace tailWord_253544 prefixEnd_253544 130189939063661241633979 := by
  unfold tailWord_253544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623754696730432356435843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6165006262307243141914457 4623754696730432356435843)
  ·
    refine ⟨6935632045095648534653765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4623754696730432356435843 6935632045095648534653765)
    ·
      refine ⟨1300431008455434100247581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6935632045095648534653765 1300431008455434100247581)
      ·
        refine ⟨487661628170787787592843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1300431008455434100247581 487661628170787787592843)
        ·
          refine ⟨731492442256181681389265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487661628170787787592843 731492442256181681389265)
          ·
            refine ⟨548619331692136261041949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731492442256181681389265 548619331692136261041949)
            ·
              refine ⟨205732249384551097890731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548619331692136261041949 205732249384551097890731)
              ·
                refine ⟨308598374076826646836097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205732249384551097890731 308598374076826646836097)
                ·
                  refine ⟨231448780557619985127073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308598374076826646836097 231448780557619985127073)
                  ·
                    refine ⟨173586585418214988845305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231448780557619985127073 173586585418214988845305)
                    ·
                      refine ⟨130189939063661241633979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173586585418214988845305 130189939063661241633979)
                      ·
                        rfl

theorem cell23_253544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_253544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253544 prefixEnd_253544 := by exact prefixLift 253544
  have htrace : WordTrace (prefixWord ++ tailWord_253544) baseStart_253544 baseEnd_253544 := by
    simpa [prefixWord, tailWord_253544, baseEnd_253544] using wordTrace_append hprefix tailTrace_253544
  have hstable : (prefixWord ++ tailWord_253544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253544).length < 2 ^ (prefixWord ++ tailWord_253544).sum := by decide
  have hdescent : baseEnd_253544 < baseStart_253544 := by decide
  rcases family_descends (prefixWord ++ tailWord_253544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253546 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_253546 : Nat := 118140960795 + 253546 * 2 ^ 59
def prefixEnd_253546 : Nat := 4983230072969 + 3 ^ 40 * 253546 * 2
def baseEnd_253546 : Nat := 43396988674990077936323

theorem tailTrace_253546 : CollatzResearch.WordTrace tailWord_253546 prefixEnd_253546 43396988674990077936323 := by
  unfold tailWord_253546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311895584863404763611123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6165054892969079369629661 2311895584863404763611123)
  ·
    refine ⟨3467843377295107145416685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311895584863404763611123 3467843377295107145416685)
    ·
      refine ⟨1300441266485665179531257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3467843377295107145416685 1300441266485665179531257)
      ·
        refine ⟨975330949864248884648443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300441266485665179531257 975330949864248884648443)
        ·
          refine ⟨1462996424796373326972665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975330949864248884648443 1462996424796373326972665)
          ·
            refine ⟨1097247318597279995229499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462996424796373326972665 1097247318597279995229499)
            ·
              refine ⟨1645870977895919992844249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097247318597279995229499 1645870977895919992844249)
              ·
                refine ⟨1234403233421939994633187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645870977895919992844249 1234403233421939994633187)
                ·
                  refine ⟨1851604850132909991949781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234403233421939994633187 1851604850132909991949781)
                  ·
                    refine ⟨43396988674990077936323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1851604850132909991949781 43396988674990077936323)
                    ·
                      rfl

theorem cell23_253546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_253546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253546 prefixEnd_253546 := by exact prefixLift 253546
  have htrace : WordTrace (prefixWord ++ tailWord_253546) baseStart_253546 baseEnd_253546 := by
    simpa [prefixWord, tailWord_253546, baseEnd_253546] using wordTrace_append hprefix tailTrace_253546
  have hstable : (prefixWord ++ tailWord_253546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253546).length < 2 ^ (prefixWord ++ tailWord_253546).sum := by decide
  have hdescent : baseEnd_253546 < baseStart_253546 := by decide
  rcases family_descends (prefixWord ++ tailWord_253546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253559 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 10]
def baseStart_253559 : Nat := 118140960795 + 253559 * 2 ^ 59
def prefixEnd_253559 : Nat := 4983230072969 + 3 ^ 40 * 253559 * 2
def baseEnd_253559 : Nat := 43399213757826227648803

theorem tailTrace_253559 : CollatzResearch.WordTrace tailWord_253559 prefixEnd_253559 43399213757826227648803 := by
  unfold tailWord_253559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248056488406522274667731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6165370992271014849778487 9248056488406522274667731)
  ·
    refine ⟨13872084732609783412001597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9248056488406522274667731 13872084732609783412001597)
    ·
      refine ⟨5202031774728668779500599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13872084732609783412001597 5202031774728668779500599)
      ·
        refine ⟨7803047662093003169250899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202031774728668779500599 7803047662093003169250899)
        ·
          refine ⟨11704571493139504753876349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803047662093003169250899 11704571493139504753876349)
          ·
            refine ⟨4389214309927314282703631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11704571493139504753876349 4389214309927314282703631)
            ·
              refine ⟨6583821464890971424055447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389214309927314282703631 6583821464890971424055447)
              ·
                refine ⟨9875732197336457136083171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583821464890971424055447 9875732197336457136083171)
                ·
                  refine ⟨14813598296004685704124757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875732197336457136083171 14813598296004685704124757)
                  ·
                    refine ⟨43399213757826227648803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 14813598296004685704124757 43399213757826227648803)
                    ·
                      rfl

theorem cell23_253559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_253559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253559 prefixEnd_253559 := by exact prefixLift 253559
  have htrace : WordTrace (prefixWord ++ tailWord_253559) baseStart_253559 baseEnd_253559 := by
    simpa [prefixWord, tailWord_253559, baseEnd_253559] using wordTrace_append hprefix tailTrace_253559
  have hstable : (prefixWord ++ tailWord_253559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253559).length < 2 ^ (prefixWord ++ tailWord_253559).sum := by decide
  have hdescent : baseEnd_253559 < baseStart_253559 := by decide
  rcases family_descends (prefixWord ++ tailWord_253559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253616 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_253616 : Nat := 118140960795 + 253616 * 2 ^ 59
def prefixEnd_253616 : Nat := 4983230072969 + 3 ^ 40 * 253616 * 2
def baseEnd_253616 : Nat := 130226909670784959933647

theorem tailTrace_253616 : CollatzResearch.WordTrace tailWord_253616 prefixEnd_253616 130226909670784959933647 := by
  unfold tailWord_253616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625067724600010504746351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6166756966133347339661801 4625067724600010504746351)
  ·
    refine ⟨6937601586900015757119527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625067724600010504746351 6937601586900015757119527)
    ·
      refine ⟨10406402380350023635679291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6937601586900015757119527 10406402380350023635679291)
      ·
        refine ⟨15609603570525035453518937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10406402380350023635679291 15609603570525035453518937)
        ·
          refine ⟨11707202677893776590139203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15609603570525035453518937 11707202677893776590139203)
          ·
            refine ⟨17560804016840664885208805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707202677893776590139203 17560804016840664885208805)
            ·
              refine ⟨3292650753157624665976651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17560804016840664885208805 3292650753157624665976651)
              ·
                refine ⟨4938976129736436998964977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292650753157624665976651 4938976129736436998964977)
                ·
                  refine ⟨3704232097302327749223733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938976129736436998964977 3704232097302327749223733)
                  ·
                    refine ⟨347271759122093226489725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3704232097302327749223733 347271759122093226489725)
                    ·
                      refine ⟨130226909670784959933647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347271759122093226489725 130226909670784959933647)
                      ·
                        rfl

theorem cell23_253616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_253616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253616 prefixEnd_253616 := by exact prefixLift 253616
  have htrace : WordTrace (prefixWord ++ tailWord_253616) baseStart_253616 baseEnd_253616 := by
    simpa [prefixWord, tailWord_253616, baseEnd_253616] using wordTrace_append hprefix tailTrace_253616
  have hstable : (prefixWord ++ tailWord_253616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253616).length < 2 ^ (prefixWord ++ tailWord_253616).sum := by decide
  have hdescent : baseEnd_253616 < baseStart_253616 := by decide
  rcases family_descends (prefixWord ++ tailWord_253616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253667 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 3]
def baseStart_253667 : Nat := 118140960795 + 253667 * 2 ^ 59
def prefixEnd_253667 : Nat := 4983230072969 + 3 ^ 40 * 253667 * 2
def baseEnd_253667 : Nat := 130253097184164260395913

theorem tailTrace_253667 : CollatzResearch.WordTrace tailWord_253667 prefixEnd_253667 130253097184164260395913 := by
  unfold tailWord_253667
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251995572015256719599255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6167997048010171146399503 9251995572015256719599255)
  ·
    refine ⟨13877993358022885079398883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9251995572015256719599255 13877993358022885079398883)
    ·
      refine ⟨20816990037034327619098325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877993358022885079398883 20816990037034327619098325)
      ·
        refine ⟨487898203992992053572617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20816990037034327619098325 487898203992992053572617)
        ·
          refine ⟨365923652994744040179463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487898203992992053572617 365923652994744040179463)
          ·
            refine ⟨548885479492116060269195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365923652994744040179463 548885479492116060269195)
            ·
              refine ⟨823328219238174090403793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548885479492116060269195 823328219238174090403793)
              ·
                refine ⟨617496164428630567802845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823328219238174090403793 617496164428630567802845)
                ·
                  refine ⟨231561061660736462926067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617496164428630567802845 231561061660736462926067)
                  ·
                    refine ⟨347341592491104694389101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231561061660736462926067 347341592491104694389101)
                    ·
                      refine ⟨130253097184164260395913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347341592491104694389101 130253097184164260395913)
                      ·
                        rfl

theorem cell23_253667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_253667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253667 prefixEnd_253667 := by exact prefixLift 253667
  have htrace : WordTrace (prefixWord ++ tailWord_253667) baseStart_253667 baseEnd_253667 := by
    simpa [prefixWord, tailWord_253667, baseEnd_253667] using wordTrace_append hprefix tailTrace_253667
  have hstable : (prefixWord ++ tailWord_253667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253667).length < 2 ^ (prefixWord ++ tailWord_253667).sum := by decide
  have hdescent : baseEnd_253667 < baseStart_253667 := by decide
  rcases family_descends (prefixWord ++ tailWord_253667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253673 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_253673 : Nat := 118140960795 + 253673 * 2 ^ 59
def prefixEnd_253673 : Nat := 4983230072969 + 3 ^ 40 * 253673 * 2
def baseEnd_253673 : Nat := 130256178068091236920885

theorem tailTrace_253673 : CollatzResearch.WordTrace tailWord_253673 prefixEnd_253673 130256178068091236920885 := by
  unfold tailWord_253673
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252214409993519744317673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168142939995679829545115 9252214409993519744317673)
  ·
    refine ⟨6939160807495139808238255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9252214409993519744317673 6939160807495139808238255)
    ·
      refine ⟨10408741211242709712357383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6939160807495139808238255 10408741211242709712357383)
      ·
        refine ⟨15613111816864064568536075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408741211242709712357383 15613111816864064568536075)
        ·
          refine ⟨23419667725296096852804113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15613111816864064568536075 23419667725296096852804113)
          ·
            refine ⟨17564750793972072639603085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23419667725296096852804113 17564750793972072639603085)
            ·
              refine ⟨6586781547739527239851157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17564750793972072639603085 6586781547739527239851157)
              ·
                refine ⟨308755385050290339368023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6586781547739527239851157 308755385050290339368023)
                ·
                  refine ⟨463133077575435509052035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308755385050290339368023 463133077575435509052035)
                  ·
                    refine ⟨694699616363153263578053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 463133077575435509052035 694699616363153263578053)
                    ·
                      refine ⟨130256178068091236920885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 694699616363153263578053 130256178068091236920885)
                      ·
                        rfl

theorem cell23_253673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_253673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253673 prefixEnd_253673 := by exact prefixLift 253673
  have htrace : WordTrace (prefixWord ++ tailWord_253673) baseStart_253673 baseEnd_253673 := by
    simpa [prefixWord, tailWord_253673, baseEnd_253673] using wordTrace_append hprefix tailTrace_253673
  have hstable : (prefixWord ++ tailWord_253673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253673).length < 2 ^ (prefixWord ++ tailWord_253673).sum := by decide
  have hdescent : baseEnd_253673 < baseStart_253673 := by decide
  rcases family_descends (prefixWord ++ tailWord_253673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253677 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_253677 : Nat := 118140960795 + 253677 * 2 ^ 59
def prefixEnd_253677 : Nat := 4983230072969 + 3 ^ 40 * 253677 * 2
def baseEnd_253677 : Nat := 130258231990709221270867

theorem tailTrace_253677 : CollatzResearch.WordTrace tailWord_253677 prefixEnd_253677 130258231990709221270867 := by
  unfold tailWord_253677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252360301979028427463285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168240201319352284975523 9252360301979028427463285)
  ·
    refine ⟨867408778310533915074683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9252360301979028427463285 867408778310533915074683)
    ·
      refine ⟨1301113167465800872612025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867408778310533915074683 1301113167465800872612025)
      ·
        refine ⟨975834875599350654459019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1301113167465800872612025 975834875599350654459019)
        ·
          refine ⟨1463752313399025981688529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975834875599350654459019 1463752313399025981688529)
          ·
            refine ⟨1097814235049269486266397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463752313399025981688529 1097814235049269486266397)
            ·
              refine ⟨411680338143476057349899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097814235049269486266397 411680338143476057349899)
              ·
                refine ⟨617520507215214086024849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411680338143476057349899 617520507215214086024849)
                ·
                  refine ⟨463140380411410564518637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617520507215214086024849 463140380411410564518637)
                  ·
                    refine ⟨173677642654278961694489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463140380411410564518637 173677642654278961694489)
                    ·
                      refine ⟨130258231990709221270867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173677642654278961694489 130258231990709221270867)
                      ·
                        rfl

theorem cell23_253677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_253677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253677 prefixEnd_253677 := by exact prefixLift 253677
  have htrace : WordTrace (prefixWord ++ tailWord_253677) baseStart_253677 baseEnd_253677 := by
    simpa [prefixWord, tailWord_253677, baseEnd_253677] using wordTrace_append hprefix tailTrace_253677
  have hstable : (prefixWord ++ tailWord_253677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253677).length < 2 ^ (prefixWord ++ tailWord_253677).sum := by decide
  have hdescent : baseEnd_253677 < baseStart_253677 := by decide
  rcases family_descends (prefixWord ++ tailWord_253677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253690 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_253690 : Nat := 118140960795 + 253690 * 2 ^ 59
def prefixEnd_253690 : Nat := 4983230072969 + 3 ^ 40 * 253690 * 2
def baseEnd_253690 : Nat := 130264907239217670408307

theorem tailTrace_253690 : CollatzResearch.WordTrace tailWord_253690 prefixEnd_253690 130264907239217670408307 := by
  unfold tailWord_253690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313208612732982911921631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6168556300621287765124349 2313208612732982911921631)
  ·
    refine ⟨3469812919099474367882447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2313208612732982911921631 3469812919099474367882447)
    ·
      refine ⟨5204719378649211551823671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469812919099474367882447 5204719378649211551823671)
      ·
        refine ⟨7807079067973817327735507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204719378649211551823671 7807079067973817327735507)
        ·
          refine ⟨11710618601960725991603261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807079067973817327735507 11710618601960725991603261)
          ·
            refine ⟨4391481975735272246851223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11710618601960725991603261 4391481975735272246851223)
            ·
              refine ⟨6587222963602908370276835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391481975735272246851223 6587222963602908370276835)
              ·
                refine ⟨9880834445404362555415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587222963602908370276835 9880834445404362555415253)
                ·
                  refine ⟨231582057314164747392545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9880834445404362555415253 231582057314164747392545)
                  ·
                    refine ⟨173686542985623560544409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231582057314164747392545 173686542985623560544409)
                    ·
                      refine ⟨130264907239217670408307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173686542985623560544409 130264907239217670408307)
                      ·
                        rfl

theorem cell23_253690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_253690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253690 prefixEnd_253690 := by exact prefixLift 253690
  have htrace : WordTrace (prefixWord ++ tailWord_253690) baseStart_253690 baseEnd_253690 := by
    simpa [prefixWord, tailWord_253690, baseEnd_253690] using wordTrace_append hprefix tailTrace_253690
  have hstable : (prefixWord ++ tailWord_253690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253690).length < 2 ^ (prefixWord ++ tailWord_253690).sum := by decide
  have hdescent : baseEnd_253690 < baseStart_253690 := by decide
  rcases family_descends (prefixWord ++ tailWord_253690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253693 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_253693 : Nat := 118140960795 + 253693 * 2 ^ 59
def prefixEnd_253693 : Nat := 4983230072969 + 3 ^ 40 * 253693 * 2
def baseEnd_253693 : Nat := 130266447681181158670793

theorem tailTrace_253693 : CollatzResearch.WordTrace tailWord_253693 prefixEnd_253693 130266447681181158670793 := by
  unfold tailWord_253693
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252943869921063160045733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168629246614042106697155 9252943869921063160045733)
  ·
    refine ⟨1734926975610199342508575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9252943869921063160045733 1734926975610199342508575)
    ·
      refine ⟨2602390463415299013762863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734926975610199342508575 2602390463415299013762863)
      ·
        refine ⟨3903585695122948520644295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602390463415299013762863 3903585695122948520644295)
        ·
          refine ⟨5855378542684422780966443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903585695122948520644295 5855378542684422780966443)
          ·
            refine ⟨8783067814026634171449665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855378542684422780966443 8783067814026634171449665)
            ·
              refine ⟨6587300860519975628587249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783067814026634171449665 6587300860519975628587249)
              ·
                refine ⟨4940475645389981721440437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587300860519975628587249 4940475645389981721440437)
                ·
                  refine ⟨463169591755310786385041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4940475645389981721440437 463169591755310786385041)
                  ·
                    refine ⟨347377193816483089788781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 463169591755310786385041 347377193816483089788781)
                    ·
                      refine ⟨130266447681181158670793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347377193816483089788781 130266447681181158670793)
                      ·
                        rfl

theorem cell23_253693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_253693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253693 prefixEnd_253693 := by exact prefixLift 253693
  have htrace : WordTrace (prefixWord ++ tailWord_253693) baseStart_253693 baseEnd_253693 := by
    simpa [prefixWord, tailWord_253693, baseEnd_253693] using wordTrace_append hprefix tailTrace_253693
  have hstable : (prefixWord ++ tailWord_253693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253693).length < 2 ^ (prefixWord ++ tailWord_253693).sum := by decide
  have hdescent : baseEnd_253693 < baseStart_253693 := by decide
  rcases family_descends (prefixWord ++ tailWord_253693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253700 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_253700 : Nat := 118140960795 + 253700 * 2 ^ 59
def prefixEnd_253700 : Nat := 4983230072969 + 3 ^ 40 * 253700 * 2
def baseEnd_253700 : Nat := 43423347348587543761087

theorem tailTrace_253700 : CollatzResearch.WordTrace tailWord_253700 prefixEnd_253700 43423347348587543761087 := by
  unfold tailWord_253700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626599590447851677775277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6168799453930468903700369 4626599590447851677775277)
  ·
    refine ⟨1734974846417944379165729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4626599590447851677775277 1734974846417944379165729)
    ·
      refine ⟨1301231134813458284374297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1734974846417944379165729 1301231134813458284374297)
      ·
        refine ⟨975923351110093713280723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1301231134813458284374297 975923351110093713280723)
        ·
          refine ⟨1463885026665140569921085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975923351110093713280723 1463885026665140569921085)
          ·
            refine ⟨548956884999427713720407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1463885026665140569921085 548956884999427713720407)
            ·
              refine ⟨823435327499141570580611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548956884999427713720407 823435327499141570580611)
              ·
                refine ⟨1235152991248712355870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823435327499141570580611 1235152991248712355870917)
                ·
                  refine ⟨231591185859133566725797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235152991248712355870917 231591185859133566725797)
                  ·
                    refine ⟨43423347348587543761087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231591185859133566725797 43423347348587543761087)
                    ·
                      rfl

theorem cell23_253700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_253700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253700 prefixEnd_253700 := by exact prefixLift 253700
  have htrace : WordTrace (prefixWord ++ tailWord_253700) baseStart_253700 baseEnd_253700 := by
    simpa [prefixWord, tailWord_253700, baseEnd_253700] using wordTrace_append hprefix tailTrace_253700
  have hstable : (prefixWord ++ tailWord_253700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253700).length < 2 ^ (prefixWord ++ tailWord_253700).sum := by decide
  have hdescent : baseEnd_253700 < baseStart_253700 := by decide
  rcases family_descends (prefixWord ++ tailWord_253700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253717 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_253717 : Nat := 118140960795 + 253717 * 2 ^ 59
def prefixEnd_253717 : Nat := 4983230072969 + 3 ^ 40 * 253717 * 2
def baseEnd_253717 : Nat := 43426257072296354923561

theorem tailTrace_253717 : CollatzResearch.WordTrace tailWord_253717 prefixEnd_253717 43426257072296354923561 := by
  unfold tailWord_253717
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253819221834115258919405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6169212814556076839279603 9253819221834115258919405)
  ·
    refine ⟨3470182208187793222094777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9253819221834115258919405 3470182208187793222094777)
    ·
      refine ⟨2602636656140844916571083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470182208187793222094777 2602636656140844916571083)
      ·
        refine ⟨3903954984211267374856625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602636656140844916571083 3903954984211267374856625)
        ·
          refine ⟨2927966238158450531142469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3903954984211267374856625 2927966238158450531142469)
          ·
            refine ⟨548993669654709474589213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2927966238158450531142469 548993669654709474589213)
            ·
              refine ⟨205872626120516052970955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548993669654709474589213 205872626120516052970955)
              ·
                refine ⟨308808939180774079456433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205872626120516052970955 308808939180774079456433)
                ·
                  refine ⟨231606704385580559592325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308808939180774079456433 231606704385580559592325)
                  ·
                    refine ⟨43426257072296354923561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231606704385580559592325 43426257072296354923561)
                    ·
                      rfl

theorem cell23_253717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_253717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253717 prefixEnd_253717 := by exact prefixLift 253717
  have htrace : WordTrace (prefixWord ++ tailWord_253717) baseStart_253717 baseEnd_253717 := by
    simpa [prefixWord, tailWord_253717, baseEnd_253717] using wordTrace_append hprefix tailTrace_253717
  have hstable : (prefixWord ++ tailWord_253717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253717).length < 2 ^ (prefixWord ++ tailWord_253717).sum := by decide
  have hdescent : baseEnd_253717 < baseStart_253717 := by decide
  rcases family_descends (prefixWord ++ tailWord_253717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253740 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_253740 : Nat := 118140960795 + 253740 * 2 ^ 59
def prefixEnd_253740 : Nat := 4983230072969 + 3 ^ 40 * 253740 * 2
def baseEnd_253740 : Nat := 130290581271942474783077

theorem tailTrace_253740 : CollatzResearch.WordTrace tailWord_253740 prefixEnd_253740 130290581271942474783077 := by
  unfold tailWord_253740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627329050375395093503337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6169772067167193458004449 4627329050375395093503337)
  ·
    refine ⟨3470496787781546320127503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4627329050375395093503337 3470496787781546320127503)
    ·
      refine ⟨5205745181672319480191255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470496787781546320127503 5205745181672319480191255)
      ·
        refine ⟨7808617772508479220286883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205745181672319480191255 7808617772508479220286883)
        ·
          refine ⟨11712926658762718830430325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808617772508479220286883 11712926658762718830430325)
          ·
            refine ⟨1098086874259004890352843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11712926658762718830430325 1098086874259004890352843)
            ·
              refine ⟨1647130311388507335529265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098086874259004890352843 1647130311388507335529265)
              ·
                refine ⟨1235347733541380501646949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647130311388507335529265 1235347733541380501646949)
                ·
                  refine ⟨231627700039008844058803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235347733541380501646949 231627700039008844058803)
                  ·
                    refine ⟨347441550058513266088205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231627700039008844058803 347441550058513266088205)
                    ·
                      refine ⟨130290581271942474783077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347441550058513266088205 130290581271942474783077)
                      ·
                        rfl

theorem cell23_253740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_253740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253740 prefixEnd_253740 := by exact prefixLift 253740
  have htrace : WordTrace (prefixWord ++ tailWord_253740) baseStart_253740 baseEnd_253740 := by
    simpa [prefixWord, tailWord_253740, baseEnd_253740] using wordTrace_append hprefix tailTrace_253740
  have hstable : (prefixWord ++ tailWord_253740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253740).length < 2 ^ (prefixWord ++ tailWord_253740).sum := by decide
  have hdescent : baseEnd_253740 < baseStart_253740 := by decide
  rcases family_descends (prefixWord ++ tailWord_253740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253757 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_253757 : Nat := 118140960795 + 253757 * 2 ^ 59
def prefixEnd_253757 : Nat := 4983230072969 + 3 ^ 40 * 253757 * 2
def baseEnd_253757 : Nat := 130299310443068908270499

theorem tailTrace_253757 : CollatzResearch.WordTrace tailWord_253757 prefixEnd_253757 130299310443068908270499 := by
  unfold tailWord_253757
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255278141689202090375525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6170185427792801393583683 9255278141689202090375525)
  ·
    refine ⟨1735364651566725391945411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9255278141689202090375525 1735364651566725391945411)
    ·
      refine ⟨2603046977350088087918117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735364651566725391945411 2603046977350088087918117)
      ·
        refine ⟨488071308253141516484647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2603046977350088087918117 488071308253141516484647)
        ·
          refine ⟨732106962379712274726971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488071308253141516484647 732106962379712274726971)
          ·
            refine ⟨1098160443569568412090457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732106962379712274726971 1098160443569568412090457)
            ·
              refine ⟨823620332677176309067843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098160443569568412090457 823620332677176309067843)
              ·
                refine ⟨1235430499015764463601765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823620332677176309067843 1235430499015764463601765)
                ·
                  refine ⟨231643218565455836925331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235430499015764463601765 231643218565455836925331)
                  ·
                    refine ⟨347464827848183755387997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231643218565455836925331 347464827848183755387997)
                    ·
                      refine ⟨130299310443068908270499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347464827848183755387997 130299310443068908270499)
                      ·
                        rfl

theorem cell23_253757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_253757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253757 prefixEnd_253757 := by exact prefixLift 253757
  have htrace : WordTrace (prefixWord ++ tailWord_253757) baseStart_253757 baseEnd_253757 := by
    simpa [prefixWord, tailWord_253757, baseEnd_253757] using wordTrace_append hprefix tailTrace_253757
  have hstable : (prefixWord ++ tailWord_253757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253757).length < 2 ^ (prefixWord ++ tailWord_253757).sum := by decide
  have hdescent : baseEnd_253757 < baseStart_253757 := by decide
  rcases family_descends (prefixWord ++ tailWord_253757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253758 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_253758 : Nat := 118140960795 + 253758 * 2 ^ 59
def prefixEnd_253758 : Nat := 4983230072969 + 3 ^ 40 * 253758 * 2
def baseEnd_253758 : Nat := 130299823923723404357995

theorem tailTrace_253758 : CollatzResearch.WordTrace tailWord_253758 prefixEnd_253758 130299823923723404357995 := by
  unfold tailWord_253758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156914326835697407645241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6170209743123719507441285 1156914326835697407645241)
  ·
    refine ⟨867685745126773055733931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156914326835697407645241 867685745126773055733931)
    ·
      refine ⟨1301528617690159583600897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867685745126773055733931 1301528617690159583600897)
      ·
        refine ⟨976146463267619687700673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1301528617690159583600897 976146463267619687700673)
        ·
          refine ⟨732109847450714765775505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976146463267619687700673 732109847450714765775505)
          ·
            refine ⟨549082385588036074331629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732109847450714765775505 549082385588036074331629)
            ·
              refine ⟨205905894595513527874361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549082385588036074331629 205905894595513527874361)
              ·
                refine ⟨154429420946635145905771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205905894595513527874361 154429420946635145905771)
                ·
                  refine ⟨231644131419952718858657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154429420946635145905771 231644131419952718858657)
                  ·
                    refine ⟨173733098564964539143993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231644131419952718858657 173733098564964539143993)
                    ·
                      refine ⟨130299823923723404357995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173733098564964539143993 130299823923723404357995)
                      ·
                        rfl

theorem cell23_253758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_253758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253758 prefixEnd_253758 := by exact prefixLift 253758
  have htrace : WordTrace (prefixWord ++ tailWord_253758) baseStart_253758 baseEnd_253758 := by
    simpa [prefixWord, tailWord_253758, baseEnd_253758] using wordTrace_append hprefix tailTrace_253758
  have hstable : (prefixWord ++ tailWord_253758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253758).length < 2 ^ (prefixWord ++ tailWord_253758).sum := by decide
  have hdescent : baseEnd_253758 < baseStart_253758 := by decide
  rcases family_descends (prefixWord ++ tailWord_253758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253833 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_253833 : Nat := 118140960795 + 253833 * 2 ^ 59
def prefixEnd_253833 : Nat := 4983230072969 + 3 ^ 40 * 253833 * 2
def baseEnd_253833 : Nat := 43446111657603536973383

theorem tailTrace_253833 : CollatzResearch.WordTrace tailWord_253833 prefixEnd_253833 43446111657603536973383 := by
  unfold tailWord_253833
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258050089413867070142153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6172033392942578046761435 9258050089413867070142153)
  ·
    refine ⟨6943537567060400302606615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9258050089413867070142153 6943537567060400302606615)
    ·
      refine ⟨10415306350590600453909923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943537567060400302606615 10415306350590600453909923)
      ·
        refine ⟨15622959525885900680864885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415306350590600453909923 15622959525885900680864885)
        ·
          refine ⟨1464652455551803188831083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15622959525885900680864885 1464652455551803188831083)
          ·
            refine ⟨2196978683327704783246625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464652455551803188831083 2196978683327704783246625)
            ·
              refine ⟨1647734012495778587434969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196978683327704783246625 1647734012495778587434969)
              ·
                refine ⟨1235800509371833940576227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647734012495778587434969 1235800509371833940576227)
                ·
                  refine ⟨1853700764057750910864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235800509371833940576227 1853700764057750910864341)
                  ·
                    refine ⟨43446111657603536973383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1853700764057750910864341 43446111657603536973383)
                    ·
                      rfl

theorem cell23_253833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_253833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253833 prefixEnd_253833 := by exact prefixLift 253833
  have htrace : WordTrace (prefixWord ++ tailWord_253833) baseStart_253833 baseEnd_253833 := by
    simpa [prefixWord, tailWord_253833, baseEnd_253833] using wordTrace_append hprefix tailTrace_253833
  have hstable : (prefixWord ++ tailWord_253833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253833).length < 2 ^ (prefixWord ++ tailWord_253833).sum := by decide
  have hdescent : baseEnd_253833 < baseStart_253833 := by decide
  rcases family_descends (prefixWord ++ tailWord_253833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253850 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_253850 : Nat := 118140960795 + 253850 * 2 ^ 59
def prefixEnd_253850 : Nat := 4983230072969 + 3 ^ 40 * 253850 * 2
def baseEnd_253850 : Nat := 43449021381312348135857

theorem tailTrace_253850 : CollatzResearch.WordTrace tailWord_253850 prefixEnd_253850 43449021381312348135857 := by
  unfold tailWord_253850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314667532588069743377751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6172446753568185982340669 2314667532588069743377751)
  ·
    refine ⟨3472001298882104615066627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314667532588069743377751 3472001298882104615066627)
    ·
      refine ⟨5208001948323156922599941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472001298882104615066627 5208001948323156922599941)
      ·
        refine ⟨976500365310591922987489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5208001948323156922599941 976500365310591922987489)
        ·
          refine ⟨732375273982943942240617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976500365310591922987489 732375273982943942240617)
          ·
            refine ⟨549281455487207956680463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732375273982943942240617 549281455487207956680463)
            ·
              refine ⟨823922183230811935020695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549281455487207956680463 823922183230811935020695)
              ·
                refine ⟨1235883274846217902531043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823922183230811935020695 1235883274846217902531043)
                ·
                  refine ⟨1853824912269326853796565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235883274846217902531043 1853824912269326853796565)
                  ·
                    refine ⟨43449021381312348135857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1853824912269326853796565 43449021381312348135857)
                    ·
                      rfl

theorem cell23_253850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_253850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253850 prefixEnd_253850 := by exact prefixLift 253850
  have htrace : WordTrace (prefixWord ++ tailWord_253850) baseStart_253850 baseEnd_253850 := by
    simpa [prefixWord, tailWord_253850, baseEnd_253850] using wordTrace_append hprefix tailTrace_253850
  have hstable : (prefixWord ++ tailWord_253850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253850).length < 2 ^ (prefixWord ++ tailWord_253850).sum := by decide
  have hdescent : baseEnd_253850 < baseStart_253850 := by decide
  rcases family_descends (prefixWord ++ tailWord_253850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253883 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_253883 : Nat := 118140960795 + 253883 * 2 ^ 59
def prefixEnd_253883 : Nat := 4983230072969 + 3 ^ 40 * 253883 * 2
def baseEnd_253883 : Nat := 130364009005535415294919

theorem tailTrace_253883 : CollatzResearch.WordTrace tailWord_253883 prefixEnd_253883 130364009005535415294919 := by
  unfold tailWord_253883
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259873739232725609462303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6173249159488483739641535 9259873739232725609462303)
  ·
    refine ⟨13889810608849088414193455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9259873739232725609462303 13889810608849088414193455)
    ·
      refine ⟨20834715913273632621290183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889810608849088414193455 20834715913273632621290183)
      ·
        refine ⟨31252073869910448931935275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20834715913273632621290183 31252073869910448931935275)
        ·
          refine ⟨46878110804865673397902913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31252073869910448931935275 46878110804865673397902913)
          ·
            refine ⟨35158583103649255048427185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46878110804865673397902913 35158583103649255048427185)
            ·
              refine ⟨26368937327736941286320389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35158583103649255048427185 26368937327736941286320389)
              ·
                refine ⟨4944175748950676491185073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26368937327736941286320389 4944175748950676491185073)
                ·
                  refine ⟨3708131811713007368388805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944175748950676491185073 3708131811713007368388805)
                  ·
                    refine ⟨695274714696188881572901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708131811713007368388805 695274714696188881572901)
                    ·
                      refine ⟨130364009005535415294919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 695274714696188881572901 130364009005535415294919)
                      ·
                        rfl

theorem cell23_253883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_253883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253883 prefixEnd_253883 := by exact prefixLift 253883
  have htrace : WordTrace (prefixWord ++ tailWord_253883) baseStart_253883 baseEnd_253883 := by
    simpa [prefixWord, tailWord_253883, baseEnd_253883] using wordTrace_append hprefix tailTrace_253883
  have hstable : (prefixWord ++ tailWord_253883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253883).length < 2 ^ (prefixWord ++ tailWord_253883).sum := by decide
  have hdescent : baseEnd_253883 < baseStart_253883 := by decide
  rcases family_descends (prefixWord ++ tailWord_253883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253943 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_253943 : Nat := 118140960795 + 253943 * 2 ^ 59
def prefixEnd_253943 : Nat := 4983230072969 + 3 ^ 40 * 253943 * 2
def baseEnd_253943 : Nat := 130394817844805180544643

theorem tailTrace_253943 : CollatzResearch.WordTrace tailWord_253943 prefixEnd_253943 130394817844805180544643 := by
  unfold tailWord_253943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262062119015355856646483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6174708079343570571097655 9262062119015355856646483)
  ·
    refine ⟨13893093178523033784969725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9262062119015355856646483 13893093178523033784969725)
    ·
      refine ⟨5209909941946137669363647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13893093178523033784969725 5209909941946137669363647)
      ·
        refine ⟨7814864912919206504045471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5209909941946137669363647 7814864912919206504045471)
        ·
          refine ⟨11722297369378809756068207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814864912919206504045471 11722297369378809756068207)
          ·
            refine ⟨17583446054068214634102311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722297369378809756068207 17583446054068214634102311)
            ·
              refine ⟨26375169081102321951153467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583446054068214634102311 26375169081102321951153467)
              ·
                refine ⟨39562753621653482926730201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26375169081102321951153467 39562753621653482926730201)
                ·
                  refine ⟨29672065216240112195047651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39562753621653482926730201 29672065216240112195047651)
                  ·
                    refine ⟨44508097824360168292571477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29672065216240112195047651 44508097824360168292571477)
                    ·
                      refine ⟨130394817844805180544643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 44508097824360168292571477 130394817844805180544643)
                      ·
                        rfl

theorem cell23_253943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_253943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253943 prefixEnd_253943 := by exact prefixLift 253943
  have htrace : WordTrace (prefixWord ++ tailWord_253943) baseStart_253943 baseEnd_253943 := by
    simpa [prefixWord, tailWord_253943, baseEnd_253943] using wordTrace_append hprefix tailTrace_253943
  have hstable : (prefixWord ++ tailWord_253943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253943).length < 2 ^ (prefixWord ++ tailWord_253943).sum := by decide
  have hdescent : baseEnd_253943 < baseStart_253943 := by decide
  rcases family_descends (prefixWord ++ tailWord_253943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253957 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_253957 : Nat := 118140960795 + 253957 * 2 ^ 59
def prefixEnd_253957 : Nat := 4983230072969 + 3 ^ 40 * 253957 * 2
def baseEnd_253957 : Nat := 43467335524656041923193

theorem tailTrace_253957 : CollatzResearch.WordTrace tailWord_253957 prefixEnd_253957 43467335524656041923193 := by
  unfold tailWord_253957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262572740964636247656125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6175048493976424165104083 9262572740964636247656125)
  ·
    refine ⟨3473464777861738592871047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9262572740964636247656125 3473464777861738592871047)
    ·
      refine ⟨5210197166792607889306571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473464777861738592871047 5210197166792607889306571)
      ·
        refine ⟨7815295750188911833959857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210197166792607889306571 7815295750188911833959857)
        ·
          refine ⟨5861471812641683875469893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7815295750188911833959857 5861471812641683875469893)
          ·
            refine ⟨1099025964870315726650605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5861471812641683875469893 1099025964870315726650605)
            ·
              refine ⟨412134736826368397493977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099025964870315726650605 412134736826368397493977)
              ·
                refine ⟨309101052619776298120483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412134736826368397493977 309101052619776298120483)
                ·
                  refine ⟨463651578929664447180725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309101052619776298120483 463651578929664447180725)
                  ·
                    refine ⟨43467335524656041923193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 463651578929664447180725 43467335524656041923193)
                    ·
                      rfl

theorem cell23_253957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_253957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253957 prefixEnd_253957 := by exact prefixLift 253957
  have htrace : WordTrace (prefixWord ++ tailWord_253957) baseStart_253957 baseEnd_253957 := by
    simpa [prefixWord, tailWord_253957, baseEnd_253957] using wordTrace_append hprefix tailTrace_253957
  have hstable : (prefixWord ++ tailWord_253957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253957).length < 2 ^ (prefixWord ++ tailWord_253957).sum := by decide
  have hdescent : baseEnd_253957 < baseStart_253957 := by decide
  rcases family_descends (prefixWord ++ tailWord_253957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253964 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_253964 : Nat := 118140960795 + 253964 * 2 ^ 59
def prefixEnd_253964 : Nat := 4983230072969 + 3 ^ 40 * 253964 * 2
def baseEnd_253964 : Nat := 130405600938549598382047

theorem tailTrace_253964 : CollatzResearch.WordTrace tailWord_253964 prefixEnd_253964 130405600938549598382047 := by
  unfold tailWord_253964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631414025969638221580473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6175218701292850962107297 4631414025969638221580473)
  ·
    refine ⟨3473560519477228666185355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4631414025969638221580473 3473560519477228666185355)
    ·
      refine ⟨5210340779215842999278033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473560519477228666185355 5210340779215842999278033)
      ·
        refine ⟨3907755584411882249458525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210340779215842999278033 3907755584411882249458525)
        ·
          refine ⟨1465408344154455843546947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3907755584411882249458525 1465408344154455843546947)
          ·
            refine ⟨2198112516231683765320421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465408344154455843546947 2198112516231683765320421)
            ·
              refine ⟨412146096793440705997579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2198112516231683765320421 412146096793440705997579)
              ·
                refine ⟨618219145190161058996369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412146096793440705997579 618219145190161058996369)
                ·
                  refine ⟨463664358892620794247277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618219145190161058996369 463664358892620794247277)
                  ·
                    refine ⟨173874134584732797842729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463664358892620794247277 173874134584732797842729)
                    ·
                      refine ⟨130405600938549598382047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173874134584732797842729 130405600938549598382047)
                      ·
                        rfl

theorem cell23_253964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_253964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253964 prefixEnd_253964 := by exact prefixLift 253964
  have htrace : WordTrace (prefixWord ++ tailWord_253964) baseStart_253964 baseEnd_253964 := by
    simpa [prefixWord, tailWord_253964, baseEnd_253964] using wordTrace_append hprefix tailTrace_253964
  have hstable : (prefixWord ++ tailWord_253964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253964).length < 2 ^ (prefixWord ++ tailWord_253964).sum := by decide
  have hdescent : baseEnd_253964 < baseStart_253964 := by decide
  rcases family_descends (prefixWord ++ tailWord_253964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253988 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_253988 : Nat := 118140960795 + 253988 * 2 ^ 59
def prefixEnd_253988 : Nat := 4983230072969 + 3 ^ 40 * 253988 * 2
def baseEnd_253988 : Nat := 130417924474257504481937

theorem tailTrace_253988 : CollatzResearch.WordTrace tailWord_253988 prefixEnd_253988 130417924474257504481937 := by
  unfold tailWord_253988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631851701926164271017309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6175802269234885694689745 4631851701926164271017309)
  ·
    refine ⟨1736944388222311601631491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4631851701926164271017309 1736944388222311601631491)
    ·
      refine ⟨2605416582333467402447237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1736944388222311601631491 2605416582333467402447237)
      ·
        refine ⟨488515609187525137958857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2605416582333467402447237 488515609187525137958857)
        ·
          refine ⟨366386706890643853469143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488515609187525137958857 366386706890643853469143)
          ·
            refine ⟨549580060335965780203715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366386706890643853469143 549580060335965780203715)
            ·
              refine ⟨824370090503948670305573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549580060335965780203715 824370090503948670305573)
              ·
                refine ⟨154569391969490375682295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824370090503948670305573 154569391969490375682295)
                ·
                  refine ⟨231854087954235563523443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154569391969490375682295 231854087954235563523443)
                  ·
                    refine ⟨347781131931353345285165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231854087954235563523443 347781131931353345285165)
                    ·
                      refine ⟨130417924474257504481937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347781131931353345285165 130417924474257504481937)
                      ·
                        rfl

theorem cell23_253988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_253988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_253988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_253988 prefixEnd_253988 := by exact prefixLift 253988
  have htrace : WordTrace (prefixWord ++ tailWord_253988) baseStart_253988 baseEnd_253988 := by
    simpa [prefixWord, tailWord_253988, baseEnd_253988] using wordTrace_append hprefix tailTrace_253988
  have hstable : (prefixWord ++ tailWord_253988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253988).length < 2 ^ (prefixWord ++ tailWord_253988).sum := by decide
  have hdescent : baseEnd_253988 < baseStart_253988 := by decide
  rcases family_descends (prefixWord ++ tailWord_253988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254000 : List Nat := [2, 1, 1, 1, 2, 5, 3, 8]
def baseStart_254000 : Nat := 118140960795 + 254000 * 2 ^ 59
def prefixEnd_254000 : Nat := 4983230072969 + 3 ^ 40 * 254000 * 2
def baseEnd_254000 : Nat := 4830521712670794723403

theorem tailTrace_254000 : CollatzResearch.WordTrace tailWord_254000 prefixEnd_254000 4830521712670794723403 := by
  unfold tailWord_254000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632070539904427295735727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6176094053205903060980969 4632070539904427295735727)
  ·
    refine ⟨6948105809856640943603591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4632070539904427295735727 6948105809856640943603591)
    ·
      refine ⟨10422158714784961415405387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6948105809856640943603591 10422158714784961415405387)
      ·
        refine ⟨15633238072177442123108081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422158714784961415405387 15633238072177442123108081)
        ·
          refine ⟨11724928554133081592331061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15633238072177442123108081 11724928554133081592331061)
          ·
            refine ⟨1099212051949976399281037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11724928554133081592331061 1099212051949976399281037)
            ·
              refine ⟨412204519481241149730389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099212051949976399281037 412204519481241149730389)
              ·
                refine ⟨4830521712670794723403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 412204519481241149730389 4830521712670794723403)
                ·
                  rfl

theorem cell23_254000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 8].length) (baseStart_254000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254000 prefixEnd_254000 := by exact prefixLift 254000
  have htrace : WordTrace (prefixWord ++ tailWord_254000) baseStart_254000 baseEnd_254000 := by
    simpa [prefixWord, tailWord_254000, baseEnd_254000] using wordTrace_append hprefix tailTrace_254000
  have hstable : (prefixWord ++ tailWord_254000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254000).length < 2 ^ (prefixWord ++ tailWord_254000).sum := by decide
  have hdescent : baseEnd_254000 < baseStart_254000 := by decide
  rcases family_descends (prefixWord ++ tailWord_254000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254027 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 3]
def baseStart_254027 : Nat := 118140960795 + 254027 * 2 ^ 59
def prefixEnd_254027 : Nat := 4983230072969 + 3 ^ 40 * 254027 * 2
def baseEnd_254027 : Nat := 130437950219782851894257

theorem tailTrace_254027 : CollatzResearch.WordTrace tailWord_254027 prefixEnd_254027 130437950219782851894257 := by
  unfold tailWord_254027
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265125850711038202704335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6176750567140692135136223 9265125850711038202704335)
  ·
    refine ⟨13897688776066557304056503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9265125850711038202704335 13897688776066557304056503)
    ·
      refine ⟨20846533164099835956084755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13897688776066557304056503 20846533164099835956084755)
      ·
        refine ⟨31269799746149753934127133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20846533164099835956084755 31269799746149753934127133)
        ·
          refine ⟨11726174904806157725297675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31269799746149753934127133 11726174904806157725297675)
          ·
            refine ⟨17589262357209236587946513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726174904806157725297675 17589262357209236587946513)
            ·
              refine ⟨13191946767906927440959885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17589262357209236587946513 13191946767906927440959885)
              ·
                refine ⟨4946980037965097790359957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13191946767906927440959885 4946980037965097790359957)
                ·
                  refine ⟨231889689279613958923123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4946980037965097790359957 231889689279613958923123)
                  ·
                    refine ⟨347834533919420938384685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231889689279613958923123 347834533919420938384685)
                    ·
                      refine ⟨130437950219782851894257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347834533919420938384685 130437950219782851894257)
                      ·
                        rfl

theorem cell23_254027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 3].length) (baseStart_254027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254027 prefixEnd_254027 := by exact prefixLift 254027
  have htrace : WordTrace (prefixWord ++ tailWord_254027) baseStart_254027 baseEnd_254027 := by
    simpa [prefixWord, tailWord_254027, baseEnd_254027] using wordTrace_append hprefix tailTrace_254027
  have hstable : (prefixWord ++ tailWord_254027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254027).length < 2 ^ (prefixWord ++ tailWord_254027).sum := by decide
  have hdescent : baseEnd_254027 < baseStart_254027 := by decide
  rcases family_descends (prefixWord ++ tailWord_254027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254038 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_254038 : Nat := 118140960795 + 254038 * 2 ^ 59
def prefixEnd_254038 : Nat := 4983230072969 + 3 ^ 40 * 254038 * 2
def baseEnd_254038 : Nat := 43481199502327436285569

theorem tailTrace_254038 : CollatzResearch.WordTrace tailWord_254038 prefixEnd_254038 43481199502327436285569 := by
  unfold tailWord_254038
  simp only [CollatzResearch.WordTrace]
  refine ⟨579095440854449192584673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6177018035780791387569845 579095440854449192584673)
  ·
    refine ⟨434321580640836894438505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 579095440854449192584673 434321580640836894438505)
    ·
      refine ⟨325741185480627670828879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434321580640836894438505 325741185480627670828879)
      ·
        refine ⟨488611778220941506243319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325741185480627670828879 488611778220941506243319)
        ·
          refine ⟨732917667331412259364979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488611778220941506243319 732917667331412259364979)
          ·
            refine ⟨1099376500997118389047469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732917667331412259364979 1099376500997118389047469)
            ·
              refine ⟨412266187873919395892801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099376500997118389047469 412266187873919395892801)
              ·
                refine ⟨309199640905439546919601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412266187873919395892801 309199640905439546919601)
                ·
                  refine ⟨231899730679079660189701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309199640905439546919601 231899730679079660189701)
                  ·
                    refine ⟨43481199502327436285569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231899730679079660189701 43481199502327436285569)
                    ·
                      rfl

theorem cell23_254038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_254038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254038 prefixEnd_254038 := by exact prefixLift 254038
  have htrace : WordTrace (prefixWord ++ tailWord_254038) baseStart_254038 baseEnd_254038 := by
    simpa [prefixWord, tailWord_254038, baseEnd_254038] using wordTrace_append hprefix tailTrace_254038
  have hstable : (prefixWord ++ tailWord_254038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254038).length < 2 ^ (prefixWord ++ tailWord_254038).sum := by decide
  have hdescent : baseEnd_254038 < baseStart_254038 := by decide
  rcases family_descends (prefixWord ++ tailWord_254038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254045 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_254045 : Nat := 118140960795 + 254045 * 2 ^ 59
def prefixEnd_254045 : Nat := 4983230072969 + 3 ^ 40 * 254045 * 2
def baseEnd_254045 : Nat := 130447192871563781469175

theorem tailTrace_254045 : CollatzResearch.WordTrace tailWord_254045 prefixEnd_254045 130447192871563781469175 := by
  unfold tailWord_254045
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265782364645827276859589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6177188243097218184573059 9265782364645827276859589)
  ·
    refine ⟨1737334193371092614411173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9265782364645827276859589 1737334193371092614411173)
    ·
      refine ⟨325750161257079865202095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1737334193371092614411173 325750161257079865202095)
      ·
        refine ⟨488625241885619797803143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325750161257079865202095 488625241885619797803143)
        ·
          refine ⟨732937862828429696704715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488625241885619797803143 732937862828429696704715)
          ·
            refine ⟨1099406794242644545057073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732937862828429696704715 1099406794242644545057073)
            ·
              refine ⟨824555095681983408792805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099406794242644545057073 824555095681983408792805)
              ·
                refine ⟨154604080440371889148651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824555095681983408792805 154604080440371889148651)
                ·
                  refine ⟨231906120660557833722977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154604080440371889148651 231906120660557833722977)
                  ·
                    refine ⟨173929590495418375292233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231906120660557833722977 173929590495418375292233)
                    ·
                      refine ⟨130447192871563781469175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173929590495418375292233 130447192871563781469175)
                      ·
                        rfl

theorem cell23_254045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_254045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254045 prefixEnd_254045 := by exact prefixLift 254045
  have htrace : WordTrace (prefixWord ++ tailWord_254045) baseStart_254045 baseEnd_254045 := by
    simpa [prefixWord, tailWord_254045, baseEnd_254045] using wordTrace_append hprefix tailTrace_254045
  have hstable : (prefixWord ++ tailWord_254045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254045).length < 2 ^ (prefixWord ++ tailWord_254045).sum := by decide
  have hdescent : baseEnd_254045 < baseStart_254045 := by decide
  rcases family_descends (prefixWord ++ tailWord_254045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254071 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_254071 : Nat := 118140960795 + 254071 * 2 ^ 59
def prefixEnd_254071 : Nat := 4983230072969 + 3 ^ 40 * 254071 * 2
def baseEnd_254071 : Nat := 130460543368580679744055

theorem tailTrace_254071 : CollatzResearch.WordTrace tailWord_254071 prefixEnd_254071 130460543368580679744055 := by
  unfold tailWord_254071
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266730662551633717306067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6177820441701089144870711 9266730662551633717306067)
  ·
    refine ⟨13900095993827450575959101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9266730662551633717306067 13900095993827450575959101)
    ·
      refine ⟨5212535997685293965984663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13900095993827450575959101 5212535997685293965984663)
      ·
        refine ⟨7818803996527940948976995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212535997685293965984663 7818803996527940948976995)
        ·
          refine ⟨11728205994791911423465493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818803996527940948976995 11728205994791911423465493)
          ·
            refine ⟨549759656005870847974945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11728205994791911423465493 549759656005870847974945)
            ·
              refine ⟨412319742004403135981209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549759656005870847974945 412319742004403135981209)
              ·
                refine ⟨309239806503302351985907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412319742004403135981209 309239806503302351985907)
                ·
                  refine ⟨463859709754953527978861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309239806503302351985907 463859709754953527978861)
                  ·
                    refine ⟨173947391158107572992073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463859709754953527978861 173947391158107572992073)
                    ·
                      refine ⟨130460543368580679744055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173947391158107572992073 130460543368580679744055)
                      ·
                        rfl

theorem cell23_254071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_254071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254071 prefixEnd_254071 := by exact prefixLift 254071
  have htrace : WordTrace (prefixWord ++ tailWord_254071) baseStart_254071 baseEnd_254071 := by
    simpa [prefixWord, tailWord_254071, baseEnd_254071] using wordTrace_append hprefix tailTrace_254071
  have hstable : (prefixWord ++ tailWord_254071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254071).length < 2 ^ (prefixWord ++ tailWord_254071).sum := by decide
  have hdescent : baseEnd_254071 < baseStart_254071 := by decide
  rcases family_descends (prefixWord ++ tailWord_254071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254084 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_254084 : Nat := 118140960795 + 254084 * 2 ^ 59
def prefixEnd_254084 : Nat := 4983230072969 + 3 ^ 40 * 254084 * 2
def baseEnd_254084 : Nat := 130467218617089128881495

theorem tailTrace_254084 : CollatzResearch.WordTrace tailWord_254084 prefixEnd_254084 130467218617089128881495 := by
  unfold tailWord_254084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633602405752268468764653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6178136541003024625019537 4633602405752268468764653)
  ·
    refine ⟨1737600902157100675786745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4633602405752268468764653 1737600902157100675786745)
    ·
      refine ⟨1303200676617825506840059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1737600902157100675786745 1303200676617825506840059)
      ·
        refine ⟨1954801014926738260260089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303200676617825506840059 1954801014926738260260089)
        ·
          refine ⟨1466100761195053695195067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954801014926738260260089 1466100761195053695195067)
          ·
            refine ⟨2199151141792580542792601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466100761195053695195067 2199151141792580542792601)
            ·
              refine ⟨1649363356344435407094451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199151141792580542792601 1649363356344435407094451)
              ·
                refine ⟨2474045034516653110641677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649363356344435407094451 2474045034516653110641677)
                ·
                  refine ⟨927766887943744916490629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2474045034516653110641677 927766887943744916490629)
                  ·
                    refine ⟨173956291489452171841993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927766887943744916490629 173956291489452171841993)
                    ·
                      refine ⟨130467218617089128881495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173956291489452171841993 130467218617089128881495)
                      ·
                        rfl

theorem cell23_254084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_254084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254084 prefixEnd_254084 := by exact prefixLift 254084
  have htrace : WordTrace (prefixWord ++ tailWord_254084) baseStart_254084 baseEnd_254084 := by
    simpa [prefixWord, tailWord_254084, baseEnd_254084] using wordTrace_append hprefix tailTrace_254084
  have hstable : (prefixWord ++ tailWord_254084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254084).length < 2 ^ (prefixWord ++ tailWord_254084).sum := by decide
  have hdescent : baseEnd_254084 < baseStart_254084 := by decide
  rcases family_descends (prefixWord ++ tailWord_254084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254101 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_254101 : Nat := 118140960795 + 254101 * 2 ^ 59
def prefixEnd_254101 : Nat := 4983230072969 + 3 ^ 40 * 254101 * 2
def baseEnd_254101 : Nat := 130475947788215562368917

theorem tailTrace_254101 : CollatzResearch.WordTrace tailWord_254101 prefixEnd_254101 130475947788215562368917 := by
  unfold tailWord_254101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267824852442948840898157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6178549901628632560598771 9267824852442948840898157)
  ·
    refine ⟨3475434319666105815336809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9267824852442948840898157 3475434319666105815336809)
    ·
      refine ⟨2606575739749579361502607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3475434319666105815336809 2606575739749579361502607)
      ·
        refine ⟨3909863609624369042253911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606575739749579361502607 3909863609624369042253911)
        ·
          refine ⟨5864795414436553563380867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909863609624369042253911 5864795414436553563380867)
          ·
            refine ⟨8797193121654830345071301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864795414436553563380867 8797193121654830345071301)
            ·
              refine ⟨1649473710310280689700869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8797193121654830345071301 1649473710310280689700869)
              ·
                refine ⟨309276320683177629318913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1649473710310280689700869 309276320683177629318913)
                ·
                  refine ⟨231957240512383221989185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309276320683177629318913 231957240512383221989185)
                  ·
                    refine ⟨173967930384287416491889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231957240512383221989185 173967930384287416491889)
                    ·
                      refine ⟨130475947788215562368917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173967930384287416491889 130475947788215562368917)
                      ·
                        rfl

theorem cell23_254101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_254101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254101 prefixEnd_254101 := by exact prefixLift 254101
  have htrace : WordTrace (prefixWord ++ tailWord_254101) baseStart_254101 baseEnd_254101 := by
    simpa [prefixWord, tailWord_254101, baseEnd_254101] using wordTrace_append hprefix tailTrace_254101
  have hstable : (prefixWord ++ tailWord_254101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254101).length < 2 ^ (prefixWord ++ tailWord_254101).sum := by decide
  have hdescent : baseEnd_254101 < baseStart_254101 := by decide
  rcases family_descends (prefixWord ++ tailWord_254101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254117 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_254117 : Nat := 118140960795 + 254117 * 2 ^ 59
def prefixEnd_254117 : Nat := 4983230072969 + 3 ^ 40 * 254117 * 2
def baseEnd_254117 : Nat := 130484163478687499768843

theorem tailTrace_254117 : CollatzResearch.WordTrace tailWord_254117 prefixEnd_254117 130484163478687499768843 := by
  unfold tailWord_254117
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268408420384983573480605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6178938946923322382320403 9268408420384983573480605)
  ·
    refine ⟨3475653157644368840055227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9268408420384983573480605 3475653157644368840055227)
    ·
      refine ⟨5213479736466553260082841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475653157644368840055227 5213479736466553260082841)
      ·
        refine ⟨3910109802349914945062131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5213479736466553260082841 3910109802349914945062131)
        ·
          refine ⟨5865164703524872417593197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910109802349914945062131 5865164703524872417593197)
          ·
            refine ⟨2199436763821827156597449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5865164703524872417593197 2199436763821827156597449)
            ·
              refine ⟨1649577572866370367448087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199436763821827156597449 1649577572866370367448087)
              ·
                refine ⟨2474366359299555551172131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649577572866370367448087 2474366359299555551172131)
                ·
                  refine ⟨3711549538949333326758197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474366359299555551172131 3711549538949333326758197)
                  ·
                    refine ⟨347957769276499999383581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3711549538949333326758197 347957769276499999383581)
                    ·
                      refine ⟨130484163478687499768843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 347957769276499999383581 130484163478687499768843)
                      ·
                        rfl

theorem cell23_254117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_254117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254117 prefixEnd_254117 := by exact prefixLift 254117
  have htrace : WordTrace (prefixWord ++ tailWord_254117) baseStart_254117 baseEnd_254117 := by
    simpa [prefixWord, tailWord_254117, baseEnd_254117] using wordTrace_append hprefix tailTrace_254117
  have hstable : (prefixWord ++ tailWord_254117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254117).length < 2 ^ (prefixWord ++ tailWord_254117).sum := by decide
  have hdescent : baseEnd_254117 < baseStart_254117 := by decide
  rcases family_descends (prefixWord ++ tailWord_254117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254122 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_254122 : Nat := 118140960795 + 254122 * 2 ^ 59
def prefixEnd_254122 : Nat := 4983230072969 + 3 ^ 40 * 254122 * 2
def baseEnd_254122 : Nat := 130486730881959980206321

theorem tailTrace_254122 : CollatzResearch.WordTrace tailWord_254122 prefixEnd_254122 130486730881959980206321 := by
  unfold tailWord_254122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317147696341717356853155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6179060523577912951608413 2317147696341717356853155)
  ·
    refine ⟨3475721544512576035279733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2317147696341717356853155 3475721544512576035279733)
    ·
      refine ⟨325848894798054003307475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3475721544512576035279733 325848894798054003307475)
      ·
        refine ⟨488773342197081004961213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325848894798054003307475 488773342197081004961213)
        ·
          refine ⟨183290003323905376860455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488773342197081004961213 183290003323905376860455)
          ·
            refine ⟨274935004985858065290683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183290003323905376860455 274935004985858065290683)
            ·
              refine ⟨412402507478787097936025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274935004985858065290683 412402507478787097936025)
              ·
                refine ⟨309301880609090323452019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412402507478787097936025 309301880609090323452019)
                ·
                  refine ⟨463952820913635485178029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309301880609090323452019 463952820913635485178029)
                  ·
                    refine ⟨173982307842613306941761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463952820913635485178029 173982307842613306941761)
                    ·
                      refine ⟨130486730881959980206321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 173982307842613306941761 130486730881959980206321)
                      ·
                        rfl

theorem cell23_254122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_254122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254122 prefixEnd_254122 := by exact prefixLift 254122
  have htrace : WordTrace (prefixWord ++ tailWord_254122) baseStart_254122 baseEnd_254122 := by
    simpa [prefixWord, tailWord_254122, baseEnd_254122] using wordTrace_append hprefix tailTrace_254122
  have hstable : (prefixWord ++ tailWord_254122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254122).length < 2 ^ (prefixWord ++ tailWord_254122).sum := by decide
  have hdescent : baseEnd_254122 < baseStart_254122 := by decide
  rcases family_descends (prefixWord ++ tailWord_254122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254158 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_254158 : Nat := 118140960795 + 254158 * 2 ^ 59
def prefixEnd_254158 : Nat := 4983230072969 + 3 ^ 40 * 254158 * 2
def baseEnd_254158 : Nat := 14500579576169093261795

theorem tailTrace_254158 : CollatzResearch.WordTrace tailWord_254158 prefixEnd_254158 14500579576169093261795 := by
  unfold tailWord_254158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158737976654555946965391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6179935875490965050482085 1158737976654555946965391)
  ·
    refine ⟨1738106964981833920448087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1158737976654555946965391 1738106964981833920448087)
    ·
      refine ⟨2607160447472750880672131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738106964981833920448087 2607160447472750880672131)
      ·
        refine ⟨3910740671209126321008197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607160447472750880672131 3910740671209126321008197)
        ·
          refine ⟨733263875851711185189037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3910740671209126321008197 733263875851711185189037)
          ·
            refine ⟨274973953444391694445889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733263875851711185189037 274973953444391694445889)
            ·
              refine ⟨206230465083293770834417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274973953444391694445889 206230465083293770834417)
              ·
                refine ⟨154672848812470328125813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206230465083293770834417 154672848812470328125813)
                ·
                  refine ⟨14500579576169093261795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154672848812470328125813 14500579576169093261795)
                  ·
                    rfl

theorem cell23_254158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_254158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254158 prefixEnd_254158 := by exact prefixLift 254158
  have htrace : WordTrace (prefixWord ++ tailWord_254158) baseStart_254158 baseEnd_254158 := by
    simpa [prefixWord, tailWord_254158, baseEnd_254158] using wordTrace_append hprefix tailTrace_254158
  have hstable : (prefixWord ++ tailWord_254158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254158).length < 2 ^ (prefixWord ++ tailWord_254158).sum := by decide
  have hdescent : baseEnd_254158 < baseStart_254158 := by decide
  rcases family_descends (prefixWord ++ tailWord_254158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254184 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_254184 : Nat := 118140960795 + 254184 * 2 ^ 59
def prefixEnd_254184 : Nat := 4983230072969 + 3 ^ 40 * 254184 * 2
def baseEnd_254184 : Nat := 43506188894179579210345

theorem tailTrace_254184 : CollatzResearch.WordTrace tailWord_254184 prefixEnd_254184 43506188894179579210345 := by
  unfold tailWord_254184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635426055571127008084803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6180568074094836010779737 4635426055571127008084803)
  ·
    refine ⟨6953139083356690512127205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4635426055571127008084803 6953139083356690512127205)
    ·
      refine ⟨1303713578129379471023851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6953139083356690512127205 1303713578129379471023851)
      ·
        refine ⟨1955570367194069206535777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303713578129379471023851 1955570367194069206535777)
        ·
          refine ⟨1466677775395551904901833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955570367194069206535777 1466677775395551904901833)
          ·
            refine ⟨1100008331546663928676375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466677775395551904901833 1100008331546663928676375)
            ·
              refine ⟨1650012497319995893014563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100008331546663928676375 1650012497319995893014563)
              ·
                refine ⟨2475018745979993839521845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650012497319995893014563 2475018745979993839521845)
                ·
                  refine ⟨232033007435624422455173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2475018745979993839521845 232033007435624422455173)
                  ·
                    refine ⟨43506188894179579210345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232033007435624422455173 43506188894179579210345)
                    ·
                      rfl

theorem cell23_254184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_254184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254184 prefixEnd_254184 := by exact prefixLift 254184
  have htrace : WordTrace (prefixWord ++ tailWord_254184) baseStart_254184 baseEnd_254184 := by
    simpa [prefixWord, tailWord_254184, baseEnd_254184] using wordTrace_append hprefix tailTrace_254184
  have hstable : (prefixWord ++ tailWord_254184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254184).length < 2 ^ (prefixWord ++ tailWord_254184).sum := by decide
  have hdescent : baseEnd_254184 < baseStart_254184 := by decide
  rcases family_descends (prefixWord ++ tailWord_254184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254191 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_254191 : Nat := 118140960795 + 254191 * 2 ^ 59
def prefixEnd_254191 : Nat := 4983230072969 + 3 ^ 40 * 254191 * 2
def baseEnd_254191 : Nat := 130522161047120210243503

theorem tailTrace_254191 : CollatzResearch.WordTrace tailWord_254191 prefixEnd_254191 130522161047120210243503 := by
  unfold tailWord_254191
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271107422116894211674427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6180738281411262807782951 9271107422116894211674427)
  ·
    refine ⟨13906661133175341317511641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9271107422116894211674427 13906661133175341317511641)
    ·
      refine ⟨10429995849881505988133731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13906661133175341317511641 10429995849881505988133731)
      ·
        refine ⟨15644993774822258982200597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10429995849881505988133731 15644993774822258982200597)
        ·
          refine ⟨733359083194793389790653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15644993774822258982200597 733359083194793389790653)
          ·
            refine ⟨275009656198047521171495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733359083194793389790653 275009656198047521171495)
            ·
              refine ⟨412514484297071281757243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275009656198047521171495 412514484297071281757243)
              ·
                refine ⟨618771726445606922635865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412514484297071281757243 618771726445606922635865)
                ·
                  refine ⟨464078794834205191976899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618771726445606922635865 464078794834205191976899)
                  ·
                    refine ⟨696118192251307787965349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464078794834205191976899 696118192251307787965349)
                    ·
                      refine ⟨130522161047120210243503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 696118192251307787965349 130522161047120210243503)
                      ·
                        rfl

theorem cell23_254191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_254191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254191 prefixEnd_254191 := by exact prefixLift 254191
  have htrace : WordTrace (prefixWord ++ tailWord_254191) baseStart_254191 baseEnd_254191 := by
    simpa [prefixWord, tailWord_254191, baseEnd_254191] using wordTrace_append hprefix tailTrace_254191
  have hstable : (prefixWord ++ tailWord_254191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254191).length < 2 ^ (prefixWord ++ tailWord_254191).sum := by decide
  have hdescent : baseEnd_254191 < baseStart_254191 := by decide
  rcases family_descends (prefixWord ++ tailWord_254191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254217 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_254217 : Nat := 118140960795 + 254217 * 2 ^ 59
def prefixEnd_254217 : Nat := 4983230072969 + 3 ^ 40 * 254217 * 2
def baseEnd_254217 : Nat := 130535511544137108518383

theorem tailTrace_254217 : CollatzResearch.WordTrace tailWord_254217 prefixEnd_254217 130535511544137108518383 := by
  unfold tailWord_254217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272055720022700652120905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6181370480015133768080603 9272055720022700652120905)
  ·
    refine ⟨6954041790017025489090679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9272055720022700652120905 6954041790017025489090679)
    ·
      refine ⟨10431062685025538233636019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954041790017025489090679 10431062685025538233636019)
      ·
        refine ⟨15646594027538307350454029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431062685025538233636019 15646594027538307350454029)
        ·
          refine ⟨5867472760326865256420261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15646594027538307350454029 5867472760326865256420261)
          ·
            refine ⟨1100151142561287235578799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5867472760326865256420261 1100151142561287235578799)
            ·
              refine ⟨1650226713841930853368199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100151142561287235578799 1650226713841930853368199)
              ·
                refine ⟨2475340070762896280052299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650226713841930853368199 2475340070762896280052299)
                ·
                  refine ⟨3713010106144344420078449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475340070762896280052299 3713010106144344420078449)
                  ·
                    refine ⟨2784757579608258315058837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713010106144344420078449 2784757579608258315058837)
                    ·
                      refine ⟨130535511544137108518383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2784757579608258315058837 130535511544137108518383)
                      ·
                        rfl

theorem cell23_254217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_254217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254217 prefixEnd_254217 := by exact prefixLift 254217
  have htrace : WordTrace (prefixWord ++ tailWord_254217) baseStart_254217 baseEnd_254217 := by
    simpa [prefixWord, tailWord_254217, baseEnd_254217] using wordTrace_append hprefix tailTrace_254217
  have hstable : (prefixWord ++ tailWord_254217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254217).length < 2 ^ (prefixWord ++ tailWord_254217).sum := by decide
  have hdescent : baseEnd_254217 < baseStart_254217 := by decide
  rcases family_descends (prefixWord ++ tailWord_254217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254227 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 5, 5]
def baseStart_254227 : Nat := 118140960795 + 254227 * 2 ^ 59
def prefixEnd_254227 : Nat := 4983230072969 + 3 ^ 40 * 254227 * 2
def baseEnd_254227 : Nat := 43513548783560689797779

theorem tailTrace_254227 : CollatzResearch.WordTrace tailWord_254227 prefixEnd_254227 43513548783560689797779 := by
  unfold tailWord_254227
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272420449986472359984935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6181613633324314906656623 9272420449986472359984935)
  ·
    refine ⟨13908630674979708539977403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272420449986472359984935 13908630674979708539977403)
    ·
      refine ⟨20862946012469562809966105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13908630674979708539977403 20862946012469562809966105)
      ·
        refine ⟨15647209509352172107474579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20862946012469562809966105 15647209509352172107474579)
        ·
          refine ⟨23470814264028258161211869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15647209509352172107474579 23470814264028258161211869)
          ·
            refine ⟨8801555349010596810454451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23470814264028258161211869 8801555349010596810454451)
            ·
              refine ⟨13202333023515895215681677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801555349010596810454451 13202333023515895215681677)
              ·
                refine ⟨4950874883818460705880629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13202333023515895215681677 4950874883818460705880629)
                ·
                  refine ⟨464144520357980691176309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950874883818460705880629 464144520357980691176309)
                  ·
                    refine ⟨43513548783560689797779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 464144520357980691176309 43513548783560689797779)
                    ·
                      rfl

theorem cell23_254227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 5].length) (baseStart_254227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254227 prefixEnd_254227 := by exact prefixLift 254227
  have htrace : WordTrace (prefixWord ++ tailWord_254227) baseStart_254227 baseEnd_254227 := by
    simpa [prefixWord, tailWord_254227, baseEnd_254227] using wordTrace_append hprefix tailTrace_254227
  have hstable : (prefixWord ++ tailWord_254227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254227).length < 2 ^ (prefixWord ++ tailWord_254227).sum := by decide
  have hdescent : baseEnd_254227 < baseStart_254227 := by decide
  rcases family_descends (prefixWord ++ tailWord_254227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254231 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 6]
def baseStart_254231 : Nat := 118140960795 + 254231 * 2 ^ 59
def prefixEnd_254231 : Nat := 4983230072969 + 3 ^ 40 * 254231 * 2
def baseEnd_254231 : Nat := 14504744474811117082591

theorem tailTrace_254231 : CollatzResearch.WordTrace tailWord_254231 prefixEnd_254231 14504744474811117082591 := by
  unfold tailWord_254231
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272566341971981043130547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6181710894647987362087031 9272566341971981043130547)
  ·
    refine ⟨13908849512957971564695821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272566341971981043130547 13908849512957971564695821)
    ·
      refine ⟨5215818567359239336760933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13908849512957971564695821 5215818567359239336760933)
      ·
        refine ⟨977965981379857375642675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5215818567359239336760933 977965981379857375642675)
        ·
          refine ⟨1466948972069786063464013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977965981379857375642675 1466948972069786063464013)
          ·
            refine ⟨550105864526169773799005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1466948972069786063464013 550105864526169773799005)
            ·
              refine ⟨206289699197313665174627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550105864526169773799005 206289699197313665174627)
              ·
                refine ⟨309434548795970497761941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206289699197313665174627 309434548795970497761941)
                ·
                  refine ⟨14504744474811117082591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 309434548795970497761941 14504744474811117082591)
                  ·
                    rfl

theorem cell23_254231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 6].length) (baseStart_254231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254231 prefixEnd_254231 := by exact prefixLift 254231
  have htrace : WordTrace (prefixWord ++ tailWord_254231) baseStart_254231 baseEnd_254231 := by
    simpa [prefixWord, tailWord_254231, baseEnd_254231] using wordTrace_append hprefix tailTrace_254231
  have hstable : (prefixWord ++ tailWord_254231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254231).length < 2 ^ (prefixWord ++ tailWord_254231).sum := by decide
  have hdescent : baseEnd_254231 < baseStart_254231 := by decide
  rcases family_descends (prefixWord ++ tailWord_254231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254241 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_254241 : Nat := 118140960795 + 254241 * 2 ^ 59
def prefixEnd_254241 : Nat := 4983230072969 + 3 ^ 40 * 254241 * 2
def baseEnd_254241 : Nat := 130547835079845014618273

theorem tailTrace_254241 : CollatzResearch.WordTrace tailWord_254241 prefixEnd_254241 130547835079845014618273 := by
  unfold tailWord_254241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272931071935752750994577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6181954047957168500663051 9272931071935752750994577)
  ·
    refine ⟨6954698303951814563245933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9272931071935752750994577 6954698303951814563245933)
    ·
      refine ⟨2608011863981930461217225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6954698303951814563245933 2608011863981930461217225)
      ·
        refine ⟨1956008897986447845912919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2608011863981930461217225 1956008897986447845912919)
        ·
          refine ⟨2934013346979671768869379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956008897986447845912919 2934013346979671768869379)
          ·
            refine ⟨4401020020469507653304069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934013346979671768869379 4401020020469507653304069)
            ·
              refine ⟨825191253838032684994513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4401020020469507653304069 825191253838032684994513)
              ·
                refine ⟨618893440378524513745885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825191253838032684994513 618893440378524513745885)
                ·
                  refine ⟨232085040141946692654707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618893440378524513745885 232085040141946692654707)
                  ·
                    refine ⟨348127560212920038982061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232085040141946692654707 348127560212920038982061)
                    ·
                      refine ⟨130547835079845014618273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348127560212920038982061 130547835079845014618273)
                      ·
                        rfl

theorem cell23_254241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_254241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254241 prefixEnd_254241 := by exact prefixLift 254241
  have htrace : WordTrace (prefixWord ++ tailWord_254241) baseStart_254241 baseEnd_254241 := by
    simpa [prefixWord, tailWord_254241, baseEnd_254241] using wordTrace_append hprefix tailTrace_254241
  have hstable : (prefixWord ++ tailWord_254241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254241).length < 2 ^ (prefixWord ++ tailWord_254241).sum := by decide
  have hdescent : baseEnd_254241 < baseStart_254241 := by decide
  rcases family_descends (prefixWord ++ tailWord_254241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254284 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_254284 : Nat := 118140960795 + 254284 * 2 ^ 59
def prefixEnd_254284 : Nat := 4983230072969 + 3 ^ 40 * 254284 * 2
def baseEnd_254284 : Nat := 130569914747988346380575

theorem tailTrace_254284 : CollatzResearch.WordTrace tailWord_254284 prefixEnd_254284 130569914747988346380575 := by
  unfold tailWord_254284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637249705389985547404953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6182999607186647396539937 4637249705389985547404953)
  ·
    refine ⟨3477937279042489160553715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4637249705389985547404953 3477937279042489160553715)
    ·
      refine ⟨5216905918563733740830573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477937279042489160553715 5216905918563733740830573)
      ·
        refine ⟨1956339719461400152811465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5216905918563733740830573 1956339719461400152811465)
        ·
          refine ⟨1467254789596050114608599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1956339719461400152811465 1467254789596050114608599)
          ·
            refine ⟨2200882184394075171912899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467254789596050114608599 2200882184394075171912899)
            ·
              refine ⟨3301323276591112757869349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200882184394075171912899 3301323276591112757869349)
              ·
                refine ⟨618998114360833642100503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3301323276591112757869349 618998114360833642100503)
                ·
                  refine ⟨928497171541250463150755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618998114360833642100503 928497171541250463150755)
                  ·
                    refine ⟨1392745757311875694726133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928497171541250463150755 1392745757311875694726133)
                    ·
                      refine ⟨130569914747988346380575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1392745757311875694726133 130569914747988346380575)
                      ·
                        rfl

theorem cell23_254284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_254284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254284 prefixEnd_254284 := by exact prefixLift 254284
  have htrace : WordTrace (prefixWord ++ tailWord_254284) baseStart_254284 baseEnd_254284 := by
    simpa [prefixWord, tailWord_254284, baseEnd_254284] using wordTrace_append hprefix tailTrace_254284
  have hstable : (prefixWord ++ tailWord_254284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254284).length < 2 ^ (prefixWord ++ tailWord_254284).sum := by decide
  have hdescent : baseEnd_254284 < baseStart_254284 := by decide
  rcases family_descends (prefixWord ++ tailWord_254284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254311 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_254311 : Nat := 118140960795 + 254311 * 2 ^ 59
def prefixEnd_254311 : Nat := 4983230072969 + 3 ^ 40 * 254311 * 2
def baseEnd_254311 : Nat := 130583778725659740742951

theorem tailTrace_254311 : CollatzResearch.WordTrace tailWord_254311 prefixEnd_254311 130583778725659740742951 := by
  unfold tailWord_254311
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275484181682154706042787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6183656121121436470695191 9275484181682154706042787)
  ·
    refine ⟨13913226272523232059064181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9275484181682154706042787 13913226272523232059064181)
    ·
      refine ⟨1304364963049053005537267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13913226272523232059064181 1304364963049053005537267)
      ·
        refine ⟨1956547444573579508305901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304364963049053005537267 1956547444573579508305901)
        ·
          refine ⟨733705291715092315614713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1956547444573579508305901 733705291715092315614713)
          ·
            refine ⟨550278968786319236711035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733705291715092315614713 550278968786319236711035)
            ·
              refine ⟨825418453179478855066553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550278968786319236711035 825418453179478855066553)
              ·
                refine ⟨619063839884609141299915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825418453179478855066553 619063839884609141299915)
                ·
                  refine ⟨928595759826913711949873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619063839884609141299915 928595759826913711949873)
                  ·
                    refine ⟨696446819870185283962405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928595759826913711949873 696446819870185283962405)
                    ·
                      refine ⟨130583778725659740742951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 696446819870185283962405 130583778725659740742951)
                      ·
                        rfl

theorem cell23_254311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_254311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254311 prefixEnd_254311 := by exact prefixLift 254311
  have htrace : WordTrace (prefixWord ++ tailWord_254311) baseStart_254311 baseEnd_254311 := by
    simpa [prefixWord, tailWord_254311, baseEnd_254311] using wordTrace_append hprefix tailTrace_254311
  have hstable : (prefixWord ++ tailWord_254311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254311).length < 2 ^ (prefixWord ++ tailWord_254311).sum := by decide
  have hdescent : baseEnd_254311 < baseStart_254311 := by decide
  rcases family_descends (prefixWord ++ tailWord_254311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254326 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_254326 : Nat := 118140960795 + 254326 * 2 ^ 59
def prefixEnd_254326 : Nat := 4983230072969 + 3 ^ 40 * 254326 * 2
def baseEnd_254326 : Nat := 130591480935477182055383

theorem tailTrace_254326 : CollatzResearch.WordTrace tailWord_254326 prefixEnd_254326 130591480935477182055383 := by
  unfold tailWord_254326
  simp only [CollatzResearch.WordTrace]
  refine ⟨579751954789238266739927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6184020851085208178559221 579751954789238266739927)
  ·
    refine ⟨869627932183857400109891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 579751954789238266739927 869627932183857400109891)
    ·
      refine ⟨1304441898275786100164837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869627932183857400109891 1304441898275786100164837)
      ·
        refine ⟨244582855926709893780907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1304441898275786100164837 244582855926709893780907)
        ·
          refine ⟨366874283890064840671361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244582855926709893780907 366874283890064840671361)
          ·
            refine ⟨275155712917548630503521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366874283890064840671361 275155712917548630503521)
            ·
              refine ⟨206366784688161472877641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275155712917548630503521 206366784688161472877641)
              ·
                refine ⟨154775088516121104658231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206366784688161472877641 154775088516121104658231)
                ·
                  refine ⟨232162632774181656987347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154775088516121104658231 232162632774181656987347)
                  ·
                    refine ⟨348243949161272485481021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232162632774181656987347 348243949161272485481021)
                    ·
                      refine ⟨130591480935477182055383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348243949161272485481021 130591480935477182055383)
                      ·
                        rfl

theorem cell23_254326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_254326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254326 prefixEnd_254326 := by exact prefixLift 254326
  have htrace : WordTrace (prefixWord ++ tailWord_254326) baseStart_254326 baseEnd_254326 := by
    simpa [prefixWord, tailWord_254326, baseEnd_254326] using wordTrace_append hprefix tailTrace_254326
  have hstable : (prefixWord ++ tailWord_254326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254326).length < 2 ^ (prefixWord ++ tailWord_254326).sum := by decide
  have hdescent : baseEnd_254326 < baseStart_254326 := by decide
  rcases family_descends (prefixWord ++ tailWord_254326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254348 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_254348 : Nat := 118140960795 + 254348 * 2 ^ 59
def prefixEnd_254348 : Nat := 4983230072969 + 3 ^ 40 * 254348 * 2
def baseEnd_254348 : Nat := 130602777509876095980281

theorem tailTrace_254348 : CollatzResearch.WordTrace tailWord_254348 prefixEnd_254348 130602777509876095980281 := by
  unfold tailWord_254348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638416841274055012569849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6184555788365406683426465 4638416841274055012569849)
  ·
    refine ⟨3478812630955541259427387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4638416841274055012569849 3478812630955541259427387)
    ·
      refine ⟨5218218946433311889141081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478812630955541259427387 5218218946433311889141081)
      ·
        refine ⟨3913664209824983916855811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5218218946433311889141081 3913664209824983916855811)
        ·
          refine ⟨5870496314737475875283717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913664209824983916855811 5870496314737475875283717)
          ·
            refine ⟨1100718059013276726615697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5870496314737475875283717 1100718059013276726615697)
            ·
              refine ⟨825538544259957544961773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100718059013276726615697 825538544259957544961773)
              ·
                refine ⟨309576954097484079360665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825538544259957544961773 309576954097484079360665)
                ·
                  refine ⟨232182715573113059520499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309576954097484079360665 232182715573113059520499)
                  ·
                    refine ⟨348274073359669589280749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232182715573113059520499 348274073359669589280749)
                    ·
                      refine ⟨130602777509876095980281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348274073359669589280749 130602777509876095980281)
                      ·
                        rfl

theorem cell23_254348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_254348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254348 prefixEnd_254348 := by exact prefixLift 254348
  have htrace : WordTrace (prefixWord ++ tailWord_254348) baseStart_254348 baseEnd_254348 := by
    simpa [prefixWord, tailWord_254348, baseEnd_254348] using wordTrace_append hprefix tailTrace_254348
  have hstable : (prefixWord ++ tailWord_254348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254348).length < 2 ^ (prefixWord ++ tailWord_254348).sum := by decide
  have hdescent : baseEnd_254348 < baseStart_254348 := by decide
  rcases family_descends (prefixWord ++ tailWord_254348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254369 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_254369 : Nat := 118140960795 + 254369 * 2 ^ 59
def prefixEnd_254369 : Nat := 4983230072969 + 3 ^ 40 * 254369 * 2
def baseEnd_254369 : Nat := 130613560603620513817685

theorem tailTrace_254369 : CollatzResearch.WordTrace tailWord_254369 prefixEnd_254369 130613560603620513817685 := by
  unfold tailWord_254369
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277599615472030611654161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6185066410314687074436107 9277599615472030611654161)
  ·
    refine ⟨6958199711604022958740621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9277599615472030611654161 6958199711604022958740621)
    ·
      refine ⟨2609324891851508609527733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6958199711604022958740621 2609324891851508609527733)
      ·
        refine ⟨244624208611078932143225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2609324891851508609527733 244624208611078932143225)
        ·
          refine ⟨183468156458309199107419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244624208611078932143225 183468156458309199107419)
          ·
            refine ⟨275202234687463798661129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183468156458309199107419 275202234687463798661129)
            ·
              refine ⟨206401676015597848995847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275202234687463798661129 206401676015597848995847)
              ·
                refine ⟨309602514023396773493771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206401676015597848995847 309602514023396773493771)
                ·
                  refine ⟨464403771035095160240657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309602514023396773493771 464403771035095160240657)
                  ·
                    refine ⟨348302828276321370180493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464403771035095160240657 348302828276321370180493)
                    ·
                      refine ⟨130613560603620513817685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348302828276321370180493 130613560603620513817685)
                      ·
                        rfl

theorem cell23_254369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_254369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254369 prefixEnd_254369 := by exact prefixLift 254369
  have htrace : WordTrace (prefixWord ++ tailWord_254369) baseStart_254369 baseEnd_254369 := by
    simpa [prefixWord, tailWord_254369, baseEnd_254369] using wordTrace_append hprefix tailTrace_254369
  have hstable : (prefixWord ++ tailWord_254369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254369).length < 2 ^ (prefixWord ++ tailWord_254369).sum := by decide
  have hdescent : baseEnd_254369 < baseStart_254369 := by decide
  rcases family_descends (prefixWord ++ tailWord_254369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254375 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_254375 : Nat := 118140960795 + 254375 * 2 ^ 59
def prefixEnd_254375 : Nat := 4983230072969 + 3 ^ 40 * 254375 * 2
def baseEnd_254375 : Nat := 130616641487547490342657

theorem tailTrace_254375 : CollatzResearch.WordTrace tailWord_254375 prefixEnd_254375 130616641487547490342657 := by
  unfold tailWord_254375
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277818453450293636372579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6185212302300195757581719 9277818453450293636372579)
  ·
    refine ⟨13916727680175440454558869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9277818453450293636372579 13916727680175440454558869)
    ·
      refine ⟨652346610008223771307447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13916727680175440454558869 652346610008223771307447)
      ·
        refine ⟨978519915012335656961171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652346610008223771307447 978519915012335656961171)
        ·
          refine ⟨1467779872518503485441757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978519915012335656961171 1467779872518503485441757)
          ·
            refine ⟨550417452194438807040659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1467779872518503485441757 550417452194438807040659)
            ·
              refine ⟨825626178291658210560989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550417452194438807040659 825626178291658210560989)
              ·
                refine ⟨309609816859371828960371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825626178291658210560989 309609816859371828960371)
                ·
                  refine ⟨464414725289057743440557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309609816859371828960371 464414725289057743440557)
                  ·
                    refine ⟨174155521983396653790209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464414725289057743440557 174155521983396653790209)
                    ·
                      refine ⟨130616641487547490342657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174155521983396653790209 130616641487547490342657)
                      ·
                        rfl

theorem cell23_254375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_254375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254375 prefixEnd_254375 := by exact prefixLift 254375
  have htrace : WordTrace (prefixWord ++ tailWord_254375) baseStart_254375 baseEnd_254375 := by
    simpa [prefixWord, tailWord_254375, baseEnd_254375] using wordTrace_append hprefix tailTrace_254375
  have hstable : (prefixWord ++ tailWord_254375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254375).length < 2 ^ (prefixWord ++ tailWord_254375).sum := by decide
  have hdescent : baseEnd_254375 < baseStart_254375 := by decide
  rcases family_descends (prefixWord ++ tailWord_254375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254461 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_254461 : Nat := 118140960795 + 254461 * 2 ^ 59
def prefixEnd_254461 : Nat := 4983230072969 + 3 ^ 40 * 254461 * 2
def baseEnd_254461 : Nat := 130660800823834153867261

theorem tailTrace_254461 : CollatzResearch.WordTrace tailWord_254461 prefixEnd_254461 130660800823834153867261 := by
  unfold tailWord_254461
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280955131138730324003237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6187303420759153549335491 9280955131138730324003237)
  ·
    refine ⟨1740179087088511935750607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9280955131138730324003237 1740179087088511935750607)
    ·
      refine ⟨2610268630632767903625911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740179087088511935750607 2610268630632767903625911)
      ·
        refine ⟨3915402945949151855438867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610268630632767903625911 3915402945949151855438867)
        ·
          refine ⟨5873104418923727783158301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915402945949151855438867 5873104418923727783158301)
          ·
            refine ⟨2202414157096397918684363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5873104418923727783158301 2202414157096397918684363)
            ·
              refine ⟨3303621235644596878026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202414157096397918684363 3303621235644596878026545)
              ·
                refine ⟨2477715926733447658519909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303621235644596878026545 2477715926733447658519909)
                ·
                  refine ⟨464571736262521435972483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477715926733447658519909 464571736262521435972483)
                  ·
                    refine ⟨696857604393782153958725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464571736262521435972483 696857604393782153958725)
                    ·
                      refine ⟨130660800823834153867261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 696857604393782153958725 130660800823834153867261)
                      ·
                        rfl

theorem cell23_254461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_254461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254461 prefixEnd_254461 := by exact prefixLift 254461
  have htrace : WordTrace (prefixWord ++ tailWord_254461) baseStart_254461 baseEnd_254461 := by
    simpa [prefixWord, tailWord_254461, baseEnd_254461] using wordTrace_append hprefix tailTrace_254461
  have hstable : (prefixWord ++ tailWord_254461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254461).length < 2 ^ (prefixWord ++ tailWord_254461).sum := by decide
  have hdescent : baseEnd_254461 < baseStart_254461 := by decide
  rcases family_descends (prefixWord ++ tailWord_254461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254464 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_254464 : Nat := 118140960795 + 254464 * 2 ^ 59
def prefixEnd_254464 : Nat := 4983230072969 + 3 ^ 40 * 254464 * 2
def baseEnd_254464 : Nat := 130662341265797642129747

theorem tailTrace_254464 : CollatzResearch.WordTrace tailWord_254464 prefixEnd_254464 130662341265797642129747 := by
  unfold tailWord_254464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640532275063930918181223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6187376366751907890908297 4640532275063930918181223)
  ·
    refine ⟨6960798412595896377271835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640532275063930918181223 6960798412595896377271835)
    ·
      refine ⟨10441197618893844565907753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6960798412595896377271835 10441197618893844565907753)
      ·
        refine ⟨7830898214170383424430815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10441197618893844565907753 7830898214170383424430815)
        ·
          refine ⟨11746347321255575136646223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830898214170383424430815 11746347321255575136646223)
          ·
            refine ⟨17619520981883362704969335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746347321255575136646223 17619520981883362704969335)
            ·
              refine ⟨26429281472825044057454003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619520981883362704969335 26429281472825044057454003)
              ·
                refine ⟨39643922209237566086181005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26429281472825044057454003 39643922209237566086181005)
                ·
                  refine ⟨14866470828464087282317877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39643922209237566086181005 14866470828464087282317877)
                  ·
                    refine ⟨1393731640168508182717301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14866470828464087282317877 1393731640168508182717301)
                    ·
                      refine ⟨130662341265797642129747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1393731640168508182717301 130662341265797642129747)
                      ·
                        rfl

theorem cell23_254464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_254464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254464 prefixEnd_254464 := by exact prefixLift 254464
  have htrace : WordTrace (prefixWord ++ tailWord_254464) baseStart_254464 baseEnd_254464 := by
    simpa [prefixWord, tailWord_254464, baseEnd_254464] using wordTrace_append hprefix tailTrace_254464
  have hstable : (prefixWord ++ tailWord_254464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254464).length < 2 ^ (prefixWord ++ tailWord_254464).sum := by decide
  have hdescent : baseEnd_254464 < baseStart_254464 := by decide
  rcases family_descends (prefixWord ++ tailWord_254464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254478 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_254478 : Nat := 118140960795 + 254478 * 2 ^ 59
def prefixEnd_254478 : Nat := 4983230072969 + 3 ^ 40 * 254478 * 2
def baseEnd_254478 : Nat := 130669529994960587354683

theorem tailTrace_254478 : CollatzResearch.WordTrace tailWord_254478 prefixEnd_254478 130669529994960587354683 := by
  unfold tailWord_254478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160196896509642778421511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6187716781384761484914725 1160196896509642778421511)
  ·
    refine ⟨1740295344764464167632267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1160196896509642778421511 1740295344764464167632267)
    ·
      refine ⟨2610443017146696251448401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740295344764464167632267 2610443017146696251448401)
      ·
        refine ⟨1957832262860022188586301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610443017146696251448401 1957832262860022188586301)
        ·
          refine ⟨734187098572508320719863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1957832262860022188586301 734187098572508320719863)
          ·
            refine ⟨1101280647858762481079795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734187098572508320719863 1101280647858762481079795)
            ·
              refine ⟨1651920971788143721619693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101280647858762481079795 1651920971788143721619693)
              ·
                refine ⟨619470364420553895607385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1651920971788143721619693 619470364420553895607385)
                ·
                  refine ⟨464602773315415421705539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619470364420553895607385 464602773315415421705539)
                  ·
                    refine ⟨696904159973123132558309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464602773315415421705539 696904159973123132558309)
                    ·
                      refine ⟨130669529994960587354683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 696904159973123132558309 130669529994960587354683)
                      ·
                        rfl

theorem cell23_254478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_254478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254478 prefixEnd_254478 := by exact prefixLift 254478
  have htrace : WordTrace (prefixWord ++ tailWord_254478) baseStart_254478 baseEnd_254478 := by
    simpa [prefixWord, tailWord_254478, baseEnd_254478] using wordTrace_append hprefix tailTrace_254478
  have hstable : (prefixWord ++ tailWord_254478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254478).length < 2 ^ (prefixWord ++ tailWord_254478).sum := by decide
  have hdescent : baseEnd_254478 < baseStart_254478 := by decide
  rcases family_descends (prefixWord ++ tailWord_254478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254501 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 6]
def baseStart_254501 : Nat := 118140960795 + 254501 * 2 ^ 59
def prefixEnd_254501 : Nat := 4983230072969 + 3 ^ 40 * 254501 * 2
def baseEnd_254501 : Nat := 14520148894445999707453

theorem tailTrace_254501 : CollatzResearch.WordTrace tailWord_254501 prefixEnd_254501 14520148894445999707453 := by
  unfold tailWord_254501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282414050993817155459357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6188276033995878103639571 9282414050993817155459357)
  ·
    refine ⟨3480905269122681433297259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9282414050993817155459357 3480905269122681433297259)
    ·
      refine ⟨5221357903684022149945889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480905269122681433297259 5221357903684022149945889)
      ·
        refine ⟨3916018427763016612459417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5221357903684022149945889 3916018427763016612459417)
        ·
          refine ⟨2937013820822262459344563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916018427763016612459417 2937013820822262459344563)
          ·
            refine ⟨4405520731233393689016845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937013820822262459344563 4405520731233393689016845)
            ·
              refine ⟨1652070274212522633381317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4405520731233393689016845 1652070274212522633381317)
              ·
                refine ⟨309763176414847993758997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1652070274212522633381317 309763176414847993758997)
                ·
                  refine ⟨14520148894445999707453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 309763176414847993758997 14520148894445999707453)
                  ·
                    rfl

theorem cell23_254501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_254501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254501 prefixEnd_254501 := by exact prefixLift 254501
  have htrace : WordTrace (prefixWord ++ tailWord_254501) baseStart_254501 baseEnd_254501 := by
    simpa [prefixWord, tailWord_254501, baseEnd_254501] using wordTrace_append hprefix tailTrace_254501
  have hstable : (prefixWord ++ tailWord_254501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254501).length < 2 ^ (prefixWord ++ tailWord_254501).sum := by decide
  have hdescent : baseEnd_254501 < baseStart_254501 := by decide
  rcases family_descends (prefixWord ++ tailWord_254501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254528 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3]
def baseStart_254528 : Nat := 118140960795 + 254528 * 2 ^ 59
def prefixEnd_254528 : Nat := 4983230072969 + 3 ^ 40 * 254528 * 2
def baseEnd_254528 : Nat := 130695204027685391729453

theorem tailTrace_254528 : CollatzResearch.WordTrace tailWord_254528 prefixEnd_254528 130695204027685391729453 := by
  unfold tailWord_254528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641699410948000383346119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6188932547930667177794825 4641699410948000383346119)
  ·
    refine ⟨6962549116422000575019179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641699410948000383346119 6962549116422000575019179)
    ·
      refine ⟨10443823674633000862528769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6962549116422000575019179 10443823674633000862528769)
      ·
        refine ⟨7832867755974750646896577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10443823674633000862528769 7832867755974750646896577)
        ·
          refine ⟨5874650816981062985172433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7832867755974750646896577 5874650816981062985172433)
          ·
            refine ⟨4405988112735797238879325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5874650816981062985172433 4405988112735797238879325)
            ·
              refine ⟨1652245542275923964579747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4405988112735797238879325 1652245542275923964579747)
              ·
                refine ⟨2478368313413885946869621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652245542275923964579747 2478368313413885946869621)
                ·
                  refine ⟨232347029382551807519027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478368313413885946869621 232347029382551807519027)
                  ·
                    refine ⟨348520544073827711278541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232347029382551807519027 348520544073827711278541)
                    ·
                      refine ⟨130695204027685391729453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348520544073827711278541 130695204027685391729453)
                      ·
                        rfl

theorem cell23_254528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_254528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254528 prefixEnd_254528 := by exact prefixLift 254528
  have htrace : WordTrace (prefixWord ++ tailWord_254528) baseStart_254528 baseEnd_254528 := by
    simpa [prefixWord, tailWord_254528, baseEnd_254528] using wordTrace_append hprefix tailTrace_254528
  have hstable : (prefixWord ++ tailWord_254528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254528).length < 2 ^ (prefixWord ++ tailWord_254528).sum := by decide
  have hdescent : baseEnd_254528 < baseStart_254528 := by decide
  rcases family_descends (prefixWord ++ tailWord_254528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254571 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3]
def baseStart_254571 : Nat := 118140960795 + 254571 * 2 ^ 59
def prefixEnd_254571 : Nat := 4983230072969 + 3 ^ 40 * 254571 * 2
def baseEnd_254571 : Nat := 130717283695828723491755

theorem tailTrace_254571 : CollatzResearch.WordTrace tailWord_254571 prefixEnd_254571 130717283695828723491755 := by
  unfold tailWord_254571
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284967160740219110507567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6189978107160146073671711 9284967160740219110507567)
  ·
    refine ⟨13927450741110328665761351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9284967160740219110507567 13927450741110328665761351)
    ·
      refine ⟨20891176111665492998642027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13927450741110328665761351 20891176111665492998642027)
      ·
        refine ⟨31336764167498239497963041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20891176111665492998642027 31336764167498239497963041)
        ·
          refine ⟨23502573125623679623472281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31336764167498239497963041 23502573125623679623472281)
          ·
            refine ⟨17626929844217759717604211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23502573125623679623472281 17626929844217759717604211)
            ·
              refine ⟨26440394766326639576406317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626929844217759717604211 26440394766326639576406317)
              ·
                refine ⟨9915148037372489841152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26440394766326639576406317 9915148037372489841152369)
                ·
                  refine ⟨7436361028029367380864277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915148037372489841152369 7436361028029367380864277)
                  ·
                    refine ⟨348579423188876595978013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7436361028029367380864277 348579423188876595978013)
                    ·
                      refine ⟨130717283695828723491755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348579423188876595978013 130717283695828723491755)
                      ·
                        rfl

theorem cell23_254571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3].length) (baseStart_254571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254571 prefixEnd_254571 := by exact prefixLift 254571
  have htrace : WordTrace (prefixWord ++ tailWord_254571) baseStart_254571 baseEnd_254571 := by
    simpa [prefixWord, tailWord_254571, baseEnd_254571] using wordTrace_append hprefix tailTrace_254571
  have hstable : (prefixWord ++ tailWord_254571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254571).length < 2 ^ (prefixWord ++ tailWord_254571).sum := by decide
  have hdescent : baseEnd_254571 < baseStart_254571 := by decide
  rcases family_descends (prefixWord ++ tailWord_254571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254582 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_254582 : Nat := 118140960795 + 254582 * 2 ^ 59
def prefixEnd_254582 : Nat := 4983230072969 + 3 ^ 40 * 254582 * 2
def baseEnd_254582 : Nat := 43574310661009393484735

theorem tailTrace_254582 : CollatzResearch.WordTrace tailWord_254582 prefixEnd_254582 43574310661009393484735 := by
  unfold tailWord_254582
  simp only [CollatzResearch.WordTrace]
  refine ⟨580335522731272999322375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6190245575800245326105333 580335522731272999322375)
  ·
    refine ⟨870503284096909498983563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580335522731272999322375 870503284096909498983563)
    ·
      refine ⟨1305754926145364248475345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870503284096909498983563 1305754926145364248475345)
      ·
        refine ⟨979316194609023186356509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305754926145364248475345 979316194609023186356509)
        ·
          refine ⟨367243572978383694883691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 979316194609023186356509 367243572978383694883691)
          ·
            refine ⟨550865359467575542325537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367243572978383694883691 550865359467575542325537)
            ·
              refine ⟨413149019600681656744153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550865359467575542325537 413149019600681656744153)
              ·
                refine ⟨309861764700511242558115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413149019600681656744153 309861764700511242558115)
                ·
                  refine ⟨464792647050766863837173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309861764700511242558115 464792647050766863837173)
                  ·
                    refine ⟨43574310661009393484735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 464792647050766863837173 43574310661009393484735)
                    ·
                      rfl

theorem cell23_254582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_254582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254582 prefixEnd_254582 := by exact prefixLift 254582
  have htrace : WordTrace (prefixWord ++ tailWord_254582) baseStart_254582 baseEnd_254582 := by
    simpa [prefixWord, tailWord_254582, baseEnd_254582] using wordTrace_append hprefix tailTrace_254582
  have hstable : (prefixWord ++ tailWord_254582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254582).length < 2 ^ (prefixWord ++ tailWord_254582).sum := by decide
  have hdescent : baseEnd_254582 < baseStart_254582 := by decide
  rcases family_descends (prefixWord ++ tailWord_254582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254585 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_254585 : Nat := 118140960795 + 254585 * 2 ^ 59
def prefixEnd_254585 : Nat := 4983230072969 + 3 ^ 40 * 254585 * 2
def baseEnd_254585 : Nat := 130724472424991668716691

theorem tailTrace_254585 : CollatzResearch.WordTrace tailWord_254585 prefixEnd_254585 130724472424991668716691 := by
  unfold tailWord_254585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285477782689499501517209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6190318521792999667678139 9285477782689499501517209)
  ·
    refine ⟨6964108337017124626137907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9285477782689499501517209 6964108337017124626137907)
    ·
      refine ⟨10446162505525686939206861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964108337017124626137907 10446162505525686939206861)
      ·
        refine ⟨3917310939572132602202573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10446162505525686939206861 3917310939572132602202573)
        ·
          refine ⟨1468991602339549725825965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3917310939572132602202573 1468991602339549725825965)
          ·
            refine ⟨550871850877331147184737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1468991602339549725825965 550871850877331147184737)
            ·
              refine ⟨413153888157998360388553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550871850877331147184737 413153888157998360388553)
              ·
                refine ⟨309865416118498770291415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413153888157998360388553 309865416118498770291415)
                ·
                  refine ⟨464798124177748155437123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309865416118498770291415 464798124177748155437123)
                  ·
                    refine ⟨697197186266622233155685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464798124177748155437123 697197186266622233155685)
                    ·
                      refine ⟨130724472424991668716691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 697197186266622233155685 130724472424991668716691)
                      ·
                        rfl

theorem cell23_254585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_254585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254585 prefixEnd_254585 := by exact prefixLift 254585
  have htrace : WordTrace (prefixWord ++ tailWord_254585) baseStart_254585 baseEnd_254585 := by
    simpa [prefixWord, tailWord_254585, baseEnd_254585] using wordTrace_append hprefix tailTrace_254585
  have hstable : (prefixWord ++ tailWord_254585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254585).length < 2 ^ (prefixWord ++ tailWord_254585).sum := by decide
  have hdescent : baseEnd_254585 < baseStart_254585 := by decide
  rcases family_descends (prefixWord ++ tailWord_254585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254588 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_254588 : Nat := 118140960795 + 254588 * 2 ^ 59
def prefixEnd_254588 : Nat := 4983230072969 + 3 ^ 40 * 254588 * 2
def baseEnd_254588 : Nat := 130726012866955156979177

theorem tailTrace_254588 : CollatzResearch.WordTrace tailWord_254588 prefixEnd_254588 130726012866955156979177 := by
  unfold tailWord_254588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642793600839315506938209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6190391467785754009250945 4642793600839315506938209)
  ·
    refine ⟨3482095200629486630203657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4642793600839315506938209 3482095200629486630203657)
    ·
      refine ⟨2611571400472114972652743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3482095200629486630203657 2611571400472114972652743)
      ·
        refine ⟨3917357100708172458979115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611571400472114972652743 3917357100708172458979115)
        ·
          refine ⟨5876035651062258688468673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917357100708172458979115 5876035651062258688468673)
          ·
            refine ⟨4407026738296694016351505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5876035651062258688468673 4407026738296694016351505)
            ·
              refine ⟨3305270053722520512263629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4407026738296694016351505 3305270053722520512263629)
              ·
                refine ⟨1239476270145945192098861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305270053722520512263629 1239476270145945192098861)
                ·
                  refine ⟨464803601304729447037073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239476270145945192098861 464803601304729447037073)
                  ·
                    refine ⟨348602700978547085277805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464803601304729447037073 348602700978547085277805)
                    ·
                      refine ⟨130726012866955156979177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348602700978547085277805 130726012866955156979177)
                      ·
                        rfl

theorem cell23_254588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_254588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254588 prefixEnd_254588 := by exact prefixLift 254588
  have htrace : WordTrace (prefixWord ++ tailWord_254588) baseStart_254588 baseEnd_254588 := by
    simpa [prefixWord, tailWord_254588, baseEnd_254588] using wordTrace_append hprefix tailTrace_254588
  have hstable : (prefixWord ++ tailWord_254588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254588).length < 2 ^ (prefixWord ++ tailWord_254588).sum := by decide
  have hdescent : baseEnd_254588 < baseStart_254588 := by decide
  rcases family_descends (prefixWord ++ tailWord_254588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254651 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 6, 6]
def baseStart_254651 : Nat := 118140960795 + 254651 * 2 ^ 59
def prefixEnd_254651 : Nat := 4983230072969 + 3 ^ 40 * 254651 * 2
def baseEnd_254651 : Nat := 43586120716062803497129

theorem tailTrace_254651 : CollatzResearch.WordTrace tailWord_254651 prefixEnd_254651 43586120716062803497129 := by
  unfold tailWord_254651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287885000450392773419807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6191923333633595182279871 9287885000450392773419807)
  ·
    refine ⟨13931827500675589160129711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9287885000450392773419807 13931827500675589160129711)
    ·
      refine ⟨20897741251013383740194567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13931827500675589160129711 20897741251013383740194567)
      ·
        refine ⟨31346611876520075610291851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20897741251013383740194567 31346611876520075610291851)
        ·
          refine ⟨47019917814780113415437777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31346611876520075610291851 47019917814780113415437777)
          ·
            refine ⟨35264938361085085061578333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47019917814780113415437777 35264938361085085061578333)
            ·
              refine ⟨13224351885406906898091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35264938361085085061578333 13224351885406906898091875)
              ·
                refine ⟨19836527828110360347137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224351885406906898091875 19836527828110360347137813)
                ·
                  refine ⟨929837241942673141272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19836527828110360347137813 929837241942673141272085)
                  ·
                    refine ⟨43586120716062803497129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 929837241942673141272085 43586120716062803497129)
                    ·
                      rfl

theorem cell23_254651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_254651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254651 prefixEnd_254651 := by exact prefixLift 254651
  have htrace : WordTrace (prefixWord ++ tailWord_254651) baseStart_254651 baseEnd_254651 := by
    simpa [prefixWord, tailWord_254651, baseEnd_254651] using wordTrace_append hprefix tailTrace_254651
  have hstable : (prefixWord ++ tailWord_254651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254651).length < 2 ^ (prefixWord ++ tailWord_254651).sum := by decide
  have hdescent : baseEnd_254651 < baseStart_254651 := by decide
  rcases family_descends (prefixWord ++ tailWord_254651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254671 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_254671 : Nat := 118140960795 + 254671 * 2 ^ 59
def prefixEnd_254671 : Nat := 4983230072969 + 3 ^ 40 * 254671 * 2
def baseEnd_254671 : Nat := 130768631761278332241295

theorem tailTrace_254671 : CollatzResearch.WordTrace tailWord_254671 prefixEnd_254671 130768631761278332241295 := by
  unfold tailWord_254671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288614460377936189147867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6192409640251957459431911 9288614460377936189147867)
  ·
    refine ⟨13932921690566904283721801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9288614460377936189147867 13932921690566904283721801)
    ·
      refine ⟨10449691267925178212791351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13932921690566904283721801 10449691267925178212791351)
      ·
        refine ⟨15674536901887767319187027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10449691267925178212791351 15674536901887767319187027)
        ·
          refine ⟨23511805352831650978780541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15674536901887767319187027 23511805352831650978780541)
          ·
            refine ⟨8816927007311869117042703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23511805352831650978780541 8816927007311869117042703)
            ·
              refine ⟨13225390510967803675564055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816927007311869117042703 13225390510967803675564055)
              ·
                refine ⟨19838085766451705513346083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13225390510967803675564055 19838085766451705513346083)
                ·
                  refine ⟨29757128649677558270019125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19838085766451705513346083 29757128649677558270019125)
                  ·
                    refine ⟨2789730810907271087814293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29757128649677558270019125 2789730810907271087814293)
                    ·
                      refine ⟨130768631761278332241295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2789730810907271087814293 130768631761278332241295)
                      ·
                        rfl

theorem cell23_254671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_254671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254671 prefixEnd_254671 := by exact prefixLift 254671
  have htrace : WordTrace (prefixWord ++ tailWord_254671) baseStart_254671 baseEnd_254671 := by
    simpa [prefixWord, tailWord_254671, baseEnd_254671] using wordTrace_append hprefix tailTrace_254671
  have hstable : (prefixWord ++ tailWord_254671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254671).length < 2 ^ (prefixWord ++ tailWord_254671).sum := by decide
  have hdescent : baseEnd_254671 < baseStart_254671 := by decide
  rcases family_descends (prefixWord ++ tailWord_254671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254692 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_254692 : Nat := 118140960795 + 254692 * 2 ^ 59
def prefixEnd_254692 : Nat := 4983230072969 + 3 ^ 40 * 254692 * 2
def baseEnd_254692 : Nat := 130779414855022750078699

theorem tailTrace_254692 : CollatzResearch.WordTrace tailWord_254692 prefixEnd_254692 130779414855022750078699 := by
  unfold tailWord_254692
  simp only [CollatzResearch.WordTrace]
  refine ⟨4644690196650928387831165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6192920262201237850441553 4644690196650928387831165)
  ·
    refine ⟨1741758823744098145436687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4644690196650928387831165 1741758823744098145436687)
    ·
      refine ⟨2612638235616147218155031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1741758823744098145436687 2612638235616147218155031)
      ·
        refine ⟨3918957353424220827232547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612638235616147218155031 3918957353424220827232547)
        ·
          refine ⟨5878436030136331240848821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918957353424220827232547 5878436030136331240848821)
          ·
            refine ⟨551103377825281053829577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5878436030136331240848821 551103377825281053829577)
            ·
              refine ⟨413327533368960790372183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551103377825281053829577 413327533368960790372183)
              ·
                refine ⟨619991300053441185558275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413327533368960790372183 619991300053441185558275)
                ·
                  refine ⟨929986950080161778337413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619991300053441185558275 929986950080161778337413)
                  ·
                    refine ⟨174372553140030333438265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929986950080161778337413 174372553140030333438265)
                    ·
                      refine ⟨130779414855022750078699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174372553140030333438265 130779414855022750078699)
                      ·
                        rfl

theorem cell23_254692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_254692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254692 prefixEnd_254692 := by exact prefixLift 254692
  have htrace : WordTrace (prefixWord ++ tailWord_254692) baseStart_254692 baseEnd_254692 := by
    simpa [prefixWord, tailWord_254692, baseEnd_254692] using wordTrace_append hprefix tailTrace_254692
  have hstable : (prefixWord ++ tailWord_254692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254692).length < 2 ^ (prefixWord ++ tailWord_254692).sum := by decide
  have hdescent : baseEnd_254692 < baseStart_254692 := by decide
  rcases family_descends (prefixWord ++ tailWord_254692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254805 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 6]
def baseStart_254805 : Nat := 118140960795 + 254805 * 2 ^ 59
def prefixEnd_254805 : Nat := 4983230072969 + 3 ^ 40 * 254805 * 2
def baseEnd_254805 : Nat := 14537493129886756440631

theorem tailTrace_254805 : CollatzResearch.WordTrace tailWord_254805 prefixEnd_254805 14537493129886756440631 := by
  unfold tailWord_254805
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293501841892477074525869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6195667894594984716350579 9293501841892477074525869)
  ·
    refine ⟨3485063190709678902947201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9293501841892477074525869 3485063190709678902947201)
    ·
      refine ⟨2613797393032259177210401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3485063190709678902947201 2613797393032259177210401)
      ·
        refine ⟨1960348044774194382907801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613797393032259177210401 1960348044774194382907801)
        ·
          refine ⟨1470261033580645787180851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960348044774194382907801 1470261033580645787180851)
          ·
            refine ⟨2205391550370968680771277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470261033580645787180851 2205391550370968680771277)
            ·
              refine ⟨827021831389113255289229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2205391550370968680771277 827021831389113255289229)
              ·
                refine ⟨310133186770917470733461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827021831389113255289229 310133186770917470733461)
                ·
                  refine ⟨14537493129886756440631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310133186770917470733461 14537493129886756440631)
                  ·
                    rfl

theorem cell23_254805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_254805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254805 prefixEnd_254805 := by exact prefixLift 254805
  have htrace : WordTrace (prefixWord ++ tailWord_254805) baseStart_254805 baseEnd_254805 := by
    simpa [prefixWord, tailWord_254805, baseEnd_254805] using wordTrace_append hprefix tailTrace_254805
  have hstable : (prefixWord ++ tailWord_254805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254805).length < 2 ^ (prefixWord ++ tailWord_254805).sum := by decide
  have hdescent : baseEnd_254805 < baseStart_254805 := by decide
  rcases family_descends (prefixWord ++ tailWord_254805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254808 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_254808 : Nat := 118140960795 + 254808 * 2 ^ 59
def prefixEnd_254808 : Nat := 4983230072969 + 3 ^ 40 * 254808 * 2
def baseEnd_254808 : Nat := 130838978610944296228165

theorem tailTrace_254808 : CollatzResearch.WordTrace tailWord_254808 prefixEnd_254808 130838978610944296228165 := by
  unfold tailWord_254808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646805630440804293442539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6195740840587739057923385 4646805630440804293442539)
  ·
    refine ⟨6970208445661206440163809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4646805630440804293442539 6970208445661206440163809)
    ·
      refine ⟨5227656334245904830122857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6970208445661206440163809 5227656334245904830122857)
      ·
        refine ⟨3920742250684428622592143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227656334245904830122857 3920742250684428622592143)
        ·
          refine ⟨5881113376026642933888215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920742250684428622592143 5881113376026642933888215)
          ·
            refine ⟨8821670064039964400832323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881113376026642933888215 8821670064039964400832323)
            ·
              refine ⟨13232505096059946601248485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821670064039964400832323 13232505096059946601248485)
              ·
                refine ⟨2481094705511239987734091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13232505096059946601248485 2481094705511239987734091)
                ·
                  refine ⟨3721642058266859981601137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481094705511239987734091 3721642058266859981601137)
                  ·
                    refine ⟨2791231543700144986200853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3721642058266859981601137 2791231543700144986200853)
                    ·
                      refine ⟨130838978610944296228165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2791231543700144986200853 130838978610944296228165)
                      ·
                        rfl

theorem cell23_254808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_254808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254808 prefixEnd_254808 := by exact prefixLift 254808
  have htrace : WordTrace (prefixWord ++ tailWord_254808) baseStart_254808 baseEnd_254808 := by
    simpa [prefixWord, tailWord_254808, baseEnd_254808] using wordTrace_append hprefix tailTrace_254808
  have hstable : (prefixWord ++ tailWord_254808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254808).length < 2 ^ (prefixWord ++ tailWord_254808).sum := by decide
  have hdescent : baseEnd_254808 < baseStart_254808 := by decide
  rcases family_descends (prefixWord ++ tailWord_254808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254835 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 1, 5]
def baseStart_254835 : Nat := 118140960795 + 254835 * 2 ^ 59
def prefixEnd_254835 : Nat := 4983230072969 + 3 ^ 40 * 254835 * 2
def baseEnd_254835 : Nat := 43617614196205230196847

theorem tailTrace_254835 : CollatzResearch.WordTrace tailWord_254835 prefixEnd_254835 43617614196205230196847 := by
  unfold tailWord_254835
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294596031783792198117959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196397354522528132078639 9294596031783792198117959)
  ·
    refine ⟨13941894047675688297176939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9294596031783792198117959 13941894047675688297176939)
    ·
      refine ⟨20912841071513532445765409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13941894047675688297176939 20912841071513532445765409)
      ·
        refine ⟨15684630803635149334324057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20912841071513532445765409 15684630803635149334324057)
        ·
          refine ⟨11763473102726362000743043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15684630803635149334324057 11763473102726362000743043)
          ·
            refine ⟨17645209654089543001114565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763473102726362000743043 17645209654089543001114565)
            ·
              refine ⟨3308476810141789312708981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17645209654089543001114565 3308476810141789312708981)
              ·
                refine ⟨310169700950792748066467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3308476810141789312708981 310169700950792748066467)
                ·
                  refine ⟨465254551426189122099701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310169700950792748066467 465254551426189122099701)
                  ·
                    refine ⟨43617614196205230196847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 465254551426189122099701 43617614196205230196847)
                    ·
                      rfl

theorem cell23_254835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 5].length) (baseStart_254835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254835 prefixEnd_254835 := by exact prefixLift 254835
  have htrace : WordTrace (prefixWord ++ tailWord_254835) baseStart_254835 baseEnd_254835 := by
    simpa [prefixWord, tailWord_254835, baseEnd_254835] using wordTrace_append hprefix tailTrace_254835
  have hstable : (prefixWord ++ tailWord_254835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254835).length < 2 ^ (prefixWord ++ tailWord_254835).sum := by decide
  have hdescent : baseEnd_254835 < baseStart_254835 := by decide
  rcases family_descends (prefixWord ++ tailWord_254835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254865 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_254865 : Nat := 118140960795 + 254865 * 2 ^ 59
def prefixEnd_254865 : Nat := 4983230072969 + 3 ^ 40 * 254865 * 2
def baseEnd_254865 : Nat := 43622749002750191071801

theorem tailTrace_254865 : CollatzResearch.WordTrace tailWord_254865 prefixEnd_254865 43622749002750191071801 := by
  unfold tailWord_254865
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295690221675107321710049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6197126814450071547806699 9295690221675107321710049)
  ·
    refine ⟨6971767666256330491282537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9295690221675107321710049 6971767666256330491282537)
    ·
      refine ⟨5228825749692247868461903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6971767666256330491282537 5228825749692247868461903)
      ·
        refine ⟨7843238624538371802692855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228825749692247868461903 7843238624538371802692855)
        ·
          refine ⟨11764857936807557704039283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7843238624538371802692855 11764857936807557704039283)
          ·
            refine ⟨17647286905211336556058925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11764857936807557704039283 17647286905211336556058925)
            ·
              refine ⟨6617732589454251208522097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17647286905211336556058925 6617732589454251208522097)
              ·
                refine ⟨4963299442090688406391573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617732589454251208522097 4963299442090688406391573)
                ·
                  refine ⟨232654661348001019049605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4963299442090688406391573 232654661348001019049605)
                  ·
                    refine ⟨43622749002750191071801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232654661348001019049605 43622749002750191071801)
                    ·
                      rfl

theorem cell23_254865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_254865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254865 prefixEnd_254865 := by exact prefixLift 254865
  have htrace : WordTrace (prefixWord ++ tailWord_254865) baseStart_254865 baseEnd_254865 := by
    simpa [prefixWord, tailWord_254865, baseEnd_254865] using wordTrace_append hprefix tailTrace_254865
  have hstable : (prefixWord ++ tailWord_254865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254865).length < 2 ^ (prefixWord ++ tailWord_254865).sum := by decide
  have hdescent : baseEnd_254865 < baseStart_254865 := by decide
  rcases family_descends (prefixWord ++ tailWord_254865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254866 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_254866 : Nat := 118140960795 + 254866 * 2 ^ 59
def prefixEnd_254866 : Nat := 4983230072969 + 3 ^ 40 * 254866 * 2
def baseEnd_254866 : Nat := 130868760488905069302899

theorem tailTrace_254866 : CollatzResearch.WordTrace tailWord_254866 prefixEnd_254866 130868760488905069302899 := by
  unfold tailWord_254866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323931673667871123124113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6197151129780989661664301 2323931673667871123124113)
  ·
    refine ⟨1742948755250903342343085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2323931673667871123124113 1742948755250903342343085)
    ·
      refine ⟨653605783219088753378657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1742948755250903342343085 653605783219088753378657)
      ·
        refine ⟨490204337414316565033993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653605783219088753378657 490204337414316565033993)
        ·
          refine ⟨367653253060737423775495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490204337414316565033993 367653253060737423775495)
          ·
            refine ⟨551479879591106135663243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367653253060737423775495 551479879591106135663243)
            ·
              refine ⟨827219819386659203494865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551479879591106135663243 827219819386659203494865)
              ·
                refine ⟨620414864539994402621149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827219819386659203494865 620414864539994402621149)
                ·
                  refine ⟨232655574202497900982931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620414864539994402621149 232655574202497900982931)
                  ·
                    refine ⟨348983361303746851474397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232655574202497900982931 348983361303746851474397)
                    ·
                      refine ⟨130868760488905069302899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 348983361303746851474397 130868760488905069302899)
                      ·
                        rfl

theorem cell23_254866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_254866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254866 prefixEnd_254866 := by exact prefixLift 254866
  have htrace : WordTrace (prefixWord ++ tailWord_254866) baseStart_254866 baseEnd_254866 := by
    simpa [prefixWord, tailWord_254866, baseEnd_254866] using wordTrace_append hprefix tailTrace_254866
  have hstable : (prefixWord ++ tailWord_254866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254866).length < 2 ^ (prefixWord ++ tailWord_254866).sum := by decide
  have hdescent : baseEnd_254866 < baseStart_254866 := by decide
  rcases family_descends (prefixWord ++ tailWord_254866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254882 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_254882 : Nat := 118140960795 + 254882 * 2 ^ 59
def prefixEnd_254882 : Nat := 4983230072969 + 3 ^ 40 * 254882 * 2
def baseEnd_254882 : Nat := 43625658726459002234275

theorem tailTrace_254882 : CollatzResearch.WordTrace tailWord_254882 prefixEnd_254882 43625658726459002234275 := by
  unfold tailWord_254882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324077565653379806269725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6197540175075679483385933 2324077565653379806269725)
  ·
    refine ⟨871529087120017427351147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2324077565653379806269725 871529087120017427351147)
    ·
      refine ⟨1307293630680026141026721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871529087120017427351147 1307293630680026141026721)
      ·
        refine ⟨980470223010019605770041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307293630680026141026721 980470223010019605770041)
        ·
          refine ⟨735352667257514704327531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980470223010019605770041 735352667257514704327531)
          ·
            refine ⟨1103029000886272056491297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735352667257514704327531 1103029000886272056491297)
            ·
              refine ⟨827271750664704042368473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103029000886272056491297 827271750664704042368473)
              ·
                refine ⟨620453812998528031776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827271750664704042368473 620453812998528031776355)
                ·
                  refine ⟨930680719497792047664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620453812998528031776355 930680719497792047664533)
                  ·
                    refine ⟨43625658726459002234275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 930680719497792047664533 43625658726459002234275)
                    ·
                      rfl

theorem cell23_254882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_254882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254882 prefixEnd_254882 := by exact prefixLift 254882
  have htrace : WordTrace (prefixWord ++ tailWord_254882) baseStart_254882 baseEnd_254882 := by
    simpa [prefixWord, tailWord_254882, baseEnd_254882] using wordTrace_append hprefix tailTrace_254882
  have hstable : (prefixWord ++ tailWord_254882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254882).length < 2 ^ (prefixWord ++ tailWord_254882).sum := by decide
  have hdescent : baseEnd_254882 < baseStart_254882 := by decide
  rcases family_descends (prefixWord ++ tailWord_254882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254892 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_254892 : Nat := 118140960795 + 254892 * 2 ^ 59
def prefixEnd_254892 : Nat := 4983230072969 + 3 ^ 40 * 254892 * 2
def baseEnd_254892 : Nat := 130882110985921967577779

theorem tailTrace_254892 : CollatzResearch.WordTrace tailWord_254892 prefixEnd_254892 130882110985921967577779 := by
  unfold tailWord_254892
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648337496288645466471465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6197783328384860621961953 4648337496288645466471465)
  ·
    refine ⟨3486253122216484099853599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4648337496288645466471465 3486253122216484099853599)
    ·
      refine ⟨5229379683324726149780399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486253122216484099853599 5229379683324726149780399)
      ·
        refine ⟨7844069524987089224670599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229379683324726149780399 7844069524987089224670599)
        ·
          refine ⟨11766104287480633837005899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844069524987089224670599 11766104287480633837005899)
          ·
            refine ⟨17649156431220950755508849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766104287480633837005899 17649156431220950755508849)
            ·
              refine ⟨13236867323415713066631637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17649156431220950755508849 13236867323415713066631637)
              ·
                refine ⟨310239077892555774999179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13236867323415713066631637 310239077892555774999179)
                ·
                  refine ⟨465358616838833662498769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310239077892555774999179 465358616838833662498769)
                  ·
                    refine ⟨349018962629125246874077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465358616838833662498769 349018962629125246874077)
                    ·
                      refine ⟨130882110985921967577779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349018962629125246874077 130882110985921967577779)
                      ·
                        rfl

theorem cell23_254892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_254892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254892 prefixEnd_254892 := by exact prefixLift 254892
  have htrace : WordTrace (prefixWord ++ tailWord_254892) baseStart_254892 baseEnd_254892 := by
    simpa [prefixWord, tailWord_254892, baseEnd_254892] using wordTrace_append hprefix tailTrace_254892
  have hstable : (prefixWord ++ tailWord_254892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254892).length < 2 ^ (prefixWord ++ tailWord_254892).sum := by decide
  have hdescent : baseEnd_254892 < baseStart_254892 := by decide
  rcases family_descends (prefixWord ++ tailWord_254892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254906 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2]
def baseStart_254906 : Nat := 118140960795 + 254906 * 2 ^ 59
def prefixEnd_254906 : Nat := 4983230072969 + 3 ^ 40 * 254906 * 2
def baseEnd_254906 : Nat := 130889299715084912802715

theorem tailTrace_254906 : CollatzResearch.WordTrace tailWord_254906 prefixEnd_254906 130889299715084912802715 := by
  unfold tailWord_254906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324296403631642830988143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6198123743017714215968381 2324296403631642830988143)
  ·
    refine ⟨3486444605447464246482215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324296403631642830988143 3486444605447464246482215)
    ·
      refine ⟨5229666908171196369723323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486444605447464246482215 5229666908171196369723323)
      ·
        refine ⟨7844500362256794554584985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229666908171196369723323 7844500362256794554584985)
        ·
          refine ⟨5883375271692595915938739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7844500362256794554584985 5883375271692595915938739)
          ·
            refine ⟨8825062907538893873908109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883375271692595915938739 8825062907538893873908109)
            ·
              refine ⟨3309398590327085202715541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8825062907538893873908109 3309398590327085202715541)
              ·
                refine ⟨155128058921582118877291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3309398590327085202715541 155128058921582118877291)
                ·
                  refine ⟨232692088382373178315937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155128058921582118877291 232692088382373178315937)
                  ·
                    refine ⟨174519066286779883736953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 232692088382373178315937 174519066286779883736953)
                    ·
                      refine ⟨130889299715084912802715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174519066286779883736953 130889299715084912802715)
                      ·
                        rfl

theorem cell23_254906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_254906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254906 prefixEnd_254906 := by exact prefixLift 254906
  have htrace : WordTrace (prefixWord ++ tailWord_254906) baseStart_254906 baseEnd_254906 := by
    simpa [prefixWord, tailWord_254906, baseEnd_254906] using wordTrace_append hprefix tailTrace_254906
  have hstable : (prefixWord ++ tailWord_254906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254906).length < 2 ^ (prefixWord ++ tailWord_254906).sum := by decide
  have hdescent : baseEnd_254906 < baseStart_254906 := by decide
  rcases family_descends (prefixWord ++ tailWord_254906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254916 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_254916 : Nat := 118140960795 + 254916 * 2 ^ 59
def prefixEnd_254916 : Nat := 4983230072969 + 3 ^ 40 * 254916 * 2
def baseEnd_254916 : Nat := 43631478173876624559223

theorem tailTrace_254916 : CollatzResearch.WordTrace tailWord_254916 prefixEnd_254916 43631478173876624559223 := by
  unfold tailWord_254916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648775172245171515908301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6198366896326895354544401 4648775172245171515908301)
  ·
    refine ⟨1743290689591939318465613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4648775172245171515908301 1743290689591939318465613)
    ·
      refine ⟨653734008596977244424605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1743290689591939318465613 653734008596977244424605)
      ·
        refine ⟨245150253223866466659227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653734008596977244424605 245150253223866466659227)
        ·
          refine ⟨367725379835799699988841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245150253223866466659227 367725379835799699988841)
          ·
            refine ⟨275794034876849774991631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367725379835799699988841 275794034876849774991631)
            ·
              refine ⟨413691052315274662487447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275794034876849774991631 413691052315274662487447)
              ·
                refine ⟨620536578472911993731171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413691052315274662487447 620536578472911993731171)
                ·
                  refine ⟨930804867709367990596757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620536578472911993731171 930804867709367990596757)
                  ·
                    refine ⟨43631478173876624559223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 930804867709367990596757 43631478173876624559223)
                    ·
                      rfl

theorem cell23_254916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_254916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254916 prefixEnd_254916 := by exact prefixLift 254916
  have htrace : WordTrace (prefixWord ++ tailWord_254916) baseStart_254916 baseEnd_254916 := by
    simpa [prefixWord, tailWord_254916, baseEnd_254916] using wordTrace_append hprefix tailTrace_254916
  have hstable : (prefixWord ++ tailWord_254916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254916).length < 2 ^ (prefixWord ++ tailWord_254916).sum := by decide
  have hdescent : baseEnd_254916 < baseStart_254916 := by decide
  rcases family_descends (prefixWord ++ tailWord_254916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254945 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_254945 : Nat := 118140960795 + 254945 * 2 ^ 59
def prefixEnd_254945 : Nat := 4983230072969 + 3 ^ 40 * 254945 * 2
def baseEnd_254945 : Nat := 130909325460610260215035

theorem tailTrace_254945 : CollatzResearch.WordTrace tailWord_254945 prefixEnd_254945 130909325460610260215035 := by
  unfold tailWord_254945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298608061385280984622289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6199072040923520656414859 9298608061385280984622289)
  ·
    refine ⟨6973956046038960738466717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9298608061385280984622289 6973956046038960738466717)
    ·
      refine ⟨2615233517264610276925019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6973956046038960738466717 2615233517264610276925019)
      ·
        refine ⟨3922850275896915415387529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615233517264610276925019 3922850275896915415387529)
        ·
          refine ⟨2942137706922686561540647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3922850275896915415387529 2942137706922686561540647)
          ·
            refine ⟨4413206560384029842310971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942137706922686561540647 4413206560384029842310971)
            ·
              refine ⟨6619809840576044763466457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413206560384029842310971 6619809840576044763466457)
              ·
                refine ⟨4964857380432033572599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619809840576044763466457 4964857380432033572599843)
                ·
                  refine ⟨7447286070648050358899765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964857380432033572599843 7447286070648050358899765)
                  ·
                    refine ⟨698183069123254721146853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7447286070648050358899765 698183069123254721146853)
                    ·
                      refine ⟨130909325460610260215035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 698183069123254721146853 130909325460610260215035)
                      ·
                        rfl

theorem cell23_254945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_254945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254945 prefixEnd_254945 := by exact prefixLift 254945
  have htrace : WordTrace (prefixWord ++ tailWord_254945) baseStart_254945 baseEnd_254945 := by
    simpa [prefixWord, tailWord_254945, baseEnd_254945] using wordTrace_append hprefix tailTrace_254945
  have hstable : (prefixWord ++ tailWord_254945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254945).length < 2 ^ (prefixWord ++ tailWord_254945).sum := by decide
  have hdescent : baseEnd_254945 < baseStart_254945 := by decide
  rcases family_descends (prefixWord ++ tailWord_254945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254985 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 7]
def baseStart_254985 : Nat := 118140960795 + 254985 * 2 ^ 59
def prefixEnd_254985 : Nat := 4983230072969 + 3 ^ 40 * 254985 * 2
def baseEnd_254985 : Nat := 14547762742976678190539

theorem tailTrace_254985 : CollatzResearch.WordTrace tailWord_254985 prefixEnd_254985 14547762742976678190539 := by
  unfold tailWord_254985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300066981240367816078409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6200044654160245210718939 9300066981240367816078409)
  ·
    refine ⟨6975050235930275862058807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9300066981240367816078409 6975050235930275862058807)
    ·
      refine ⟨10462575353895413793088211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975050235930275862058807 10462575353895413793088211)
      ·
        refine ⟨15693863030843120689632317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10462575353895413793088211 15693863030843120689632317)
        ·
          refine ⟨5885198636566170258612119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15693863030843120689632317 5885198636566170258612119)
          ·
            refine ⟨8827797954849255387918179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885198636566170258612119 8827797954849255387918179)
            ·
              refine ⟨13241696932273883081877269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827797954849255387918179 13241696932273883081877269)
              ·
                refine ⟨620704543700338269462997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13241696932273883081877269 620704543700338269462997)
                ·
                  refine ⟨14547762742976678190539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 620704543700338269462997 14547762742976678190539)
                  ·
                    rfl

theorem cell23_254985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_254985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_254985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_254985 prefixEnd_254985 := by exact prefixLift 254985
  have htrace : WordTrace (prefixWord ++ tailWord_254985) baseStart_254985 baseEnd_254985 := by
    simpa [prefixWord, tailWord_254985, baseEnd_254985] using wordTrace_append hprefix tailTrace_254985
  have hstable : (prefixWord ++ tailWord_254985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254985).length < 2 ^ (prefixWord ++ tailWord_254985).sum := by decide
  have hdescent : baseEnd_254985 < baseStart_254985 := by decide
  rcases family_descends (prefixWord ++ tailWord_254985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255055 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_255055 : Nat := 118140960795 + 255055 * 2 ^ 59
def prefixEnd_255055 : Nat := 4983230072969 + 3 ^ 40 * 255055 * 2
def baseEnd_255055 : Nat := 130965808332604829839529

theorem tailTrace_255055 : CollatzResearch.WordTrace tailWord_255055 prefixEnd_255055 130965808332604829839529 := by
  unfold tailWord_255055
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302620090986769771126619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6201746727324513180751079 9302620090986769771126619)
  ·
    refine ⟨13953930136480154656689929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302620090986769771126619 13953930136480154656689929)
    ·
      refine ⟨10465447602360115992517447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13953930136480154656689929 10465447602360115992517447)
      ·
        refine ⟨15698171403540173988776171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465447602360115992517447 15698171403540173988776171)
        ·
          refine ⟨23547257105310260983164257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15698171403540173988776171 23547257105310260983164257)
          ·
            refine ⟨17660442828982695737373193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23547257105310260983164257 17660442828982695737373193)
            ·
              refine ⟨13245332121737021803029895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17660442828982695737373193 13245332121737021803029895)
              ·
                refine ⟨19867998182605532704544843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13245332121737021803029895 19867998182605532704544843)
                ·
                  refine ⟨29801997273908299056817265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19867998182605532704544843 29801997273908299056817265)
                  ·
                    refine ⟨22351497955431224292612949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29801997273908299056817265 22351497955431224292612949)
                    ·
                      refine ⟨130965808332604829839529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 22351497955431224292612949 130965808332604829839529)
                      ·
                        rfl

theorem cell23_255055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_255055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255055 prefixEnd_255055 := by exact prefixLift 255055
  have htrace : WordTrace (prefixWord ++ tailWord_255055) baseStart_255055 baseEnd_255055 := by
    simpa [prefixWord, tailWord_255055, baseEnd_255055] using wordTrace_append hprefix tailTrace_255055
  have hstable : (prefixWord ++ tailWord_255055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255055).length < 2 ^ (prefixWord ++ tailWord_255055).sum := by decide
  have hdescent : baseEnd_255055 < baseStart_255055 := by decide
  rcases family_descends (prefixWord ++ tailWord_255055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255079 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 3, 4]
def baseStart_255079 : Nat := 118140960795 + 255079 * 2 ^ 59
def prefixEnd_255079 : Nat := 4983230072969 + 3 ^ 40 * 255079 * 2
def baseEnd_255079 : Nat := 43659377289437578646473

theorem tailTrace_255079 : CollatzResearch.WordTrace tailWord_255079 prefixEnd_255079 43659377289437578646473 := by
  unfold tailWord_255079
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303495442899821870000291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6202330295266547913333527 9303495442899821870000291)
  ·
    refine ⟨13955243164349732805000437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303495442899821870000291 13955243164349732805000437)
    ·
      refine ⟨1308304046657787450468791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13955243164349732805000437 1308304046657787450468791)
      ·
        refine ⟨1962456069986681175703187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308304046657787450468791 1962456069986681175703187)
        ·
          refine ⟨2943684104980021763554781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962456069986681175703187 2943684104980021763554781)
          ·
            refine ⟨1103881539367508161333043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2943684104980021763554781 1103881539367508161333043)
            ·
              refine ⟨1655822309051262241999565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103881539367508161333043 1655822309051262241999565)
              ·
                refine ⟨620933365894223340749837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655822309051262241999565 620933365894223340749837)
                ·
                  refine ⟨232850012210333752781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620933365894223340749837 232850012210333752781189)
                  ·
                    refine ⟨43659377289437578646473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232850012210333752781189 43659377289437578646473)
                    ·
                      rfl

theorem cell23_255079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_255079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255079 prefixEnd_255079 := by exact prefixLift 255079
  have htrace : WordTrace (prefixWord ++ tailWord_255079) baseStart_255079 baseEnd_255079 := by
    simpa [prefixWord, tailWord_255079, baseEnd_255079] using wordTrace_append hprefix tailTrace_255079
  have hstable : (prefixWord ++ tailWord_255079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255079).length < 2 ^ (prefixWord ++ tailWord_255079).sum := by decide
  have hdescent : baseEnd_255079 < baseStart_255079 := by decide
  rcases family_descends (prefixWord ++ tailWord_255079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255086 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_255086 : Nat := 118140960795 + 255086 * 2 ^ 59
def prefixEnd_255086 : Nat := 4983230072969 + 3 ^ 40 * 255086 * 2
def baseEnd_255086 : Nat := 130981726232894208551887

theorem tailTrace_255086 : CollatzResearch.WordTrace tailWord_255086 prefixEnd_255086 130981726232894208551887 := by
  unfold tailWord_255086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162968844234307758188139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6202500502582974710336741 1162968844234307758188139)
  ·
    refine ⟨1744453266351461637282209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162968844234307758188139 1744453266351461637282209)
    ·
      refine ⟨1308339949763596227961657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1744453266351461637282209 1308339949763596227961657)
      ·
        refine ⟨981254962322697170971243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1308339949763596227961657 981254962322697170971243)
        ·
          refine ⟨1471882443484045756456865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981254962322697170971243 1471882443484045756456865)
          ·
            refine ⟨1103911832613034317342649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471882443484045756456865 1103911832613034317342649)
            ·
              refine ⟨827933874459775738006987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103911832613034317342649 827933874459775738006987)
              ·
                refine ⟨1241900811689663607010481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827933874459775738006987 1241900811689663607010481)
                ·
                  refine ⟨931425608767247705257861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241900811689663607010481 931425608767247705257861)
                  ·
                    refine ⟨174642301643858944735849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931425608767247705257861 174642301643858944735849)
                    ·
                      refine ⟨130981726232894208551887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174642301643858944735849 130981726232894208551887)
                      ·
                        rfl

theorem cell23_255086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_255086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255086 prefixEnd_255086 := by exact prefixLift 255086
  have htrace : WordTrace (prefixWord ++ tailWord_255086) baseStart_255086 baseEnd_255086 := by
    simpa [prefixWord, tailWord_255086, baseEnd_255086] using wordTrace_append hprefix tailTrace_255086
  have hstable : (prefixWord ++ tailWord_255086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255086).length < 2 ^ (prefixWord ++ tailWord_255086).sum := by decide
  have hdescent : baseEnd_255086 < baseStart_255086 := by decide
  rcases family_descends (prefixWord ++ tailWord_255086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255113 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 1, 4]
def baseStart_255113 : Nat := 118140960795 + 255113 * 2 ^ 59
def prefixEnd_255113 : Nat := 4983230072969 + 3 ^ 40 * 255113 * 2
def baseEnd_255113 : Nat := 43665196736855200971421

theorem tailTrace_255113 : CollatzResearch.WordTrace tailWord_255113 prefixEnd_255113 43665196736855200971421 := by
  unfold tailWord_255113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304735524776645676737993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6203157016517763784491995 9304735524776645676737993)
  ·
    refine ⟨6978551643582484257553495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9304735524776645676737993 6978551643582484257553495)
    ·
      refine ⟨10467827465373726386330243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978551643582484257553495 10467827465373726386330243)
      ·
        refine ⟨15701741198060589579495365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467827465373726386330243 15701741198060589579495365)
        ·
          refine ⟨2944076474636360546155381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15701741198060589579495365 2944076474636360546155381)
          ·
            refine ⟨276007169497158801202067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2944076474636360546155381 276007169497158801202067)
            ·
              refine ⟨414010754245738201803101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276007169497158801202067 414010754245738201803101)
              ·
                refine ⟨155254032842151825676163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414010754245738201803101 155254032842151825676163)
                ·
                  refine ⟨232881049263227738514245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155254032842151825676163 232881049263227738514245)
                  ·
                    refine ⟨43665196736855200971421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232881049263227738514245 43665196736855200971421)
                    ·
                      rfl

theorem cell23_255113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 4].length) (baseStart_255113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255113 prefixEnd_255113 := by exact prefixLift 255113
  have htrace : WordTrace (prefixWord ++ tailWord_255113) baseStart_255113 baseEnd_255113 := by
    simpa [prefixWord, tailWord_255113, baseEnd_255113] using wordTrace_append hprefix tailTrace_255113
  have hstable : (prefixWord ++ tailWord_255113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255113).length < 2 ^ (prefixWord ++ tailWord_255113).sum := by decide
  have hdescent : baseEnd_255113 < baseStart_255113 := by decide
  rcases family_descends (prefixWord ++ tailWord_255113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255130 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_255130 : Nat := 118140960795 + 255130 * 2 ^ 59
def prefixEnd_255130 : Nat := 4983230072969 + 3 ^ 40 * 255130 * 2
def baseEnd_255130 : Nat := 43668106460564012133895

theorem tailTrace_255130 : CollatzResearch.WordTrace tailWord_255130 prefixEnd_255130 43668106460564012133895 := by
  unfold tailWord_255130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326338891428764395026711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6203570377143371720071229 2326338891428764395026711)
  ·
    refine ⟨3489508337143146592540067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326338891428764395026711 3489508337143146592540067)
    ·
      refine ⟨5234262505714719888810101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3489508337143146592540067 5234262505714719888810101)
      ·
        refine ⟨490712109910754989575947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5234262505714719888810101 490712109910754989575947)
        ·
          refine ⟨736068164866132484363921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490712109910754989575947 736068164866132484363921)
          ·
            refine ⟨552051123649599363272941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736068164866132484363921 552051123649599363272941)
            ·
              refine ⟨207019171368599761227353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552051123649599363272941 207019171368599761227353)
              ·
                refine ⟨155264378526449820920515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207019171368599761227353 155264378526449820920515)
                ·
                  refine ⟨232896567789674731380773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155264378526449820920515 232896567789674731380773)
                  ·
                    refine ⟨43668106460564012133895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232896567789674731380773 43668106460564012133895)
                    ·
                      rfl

theorem cell23_255130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_255130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255130 prefixEnd_255130 := by exact prefixLift 255130
  have htrace : WordTrace (prefixWord ++ tailWord_255130) baseStart_255130 baseEnd_255130 := by
    simpa [prefixWord, tailWord_255130, baseEnd_255130] using wordTrace_append hprefix tailTrace_255130
  have hstable : (prefixWord ++ tailWord_255130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255130).length < 2 ^ (prefixWord ++ tailWord_255130).sum := by decide
  have hdescent : baseEnd_255130 < baseStart_255130 := by decide
  rcases family_descends (prefixWord ++ tailWord_255130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255143 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 6]
def baseStart_255143 : Nat := 118140960795 + 255143 * 2 ^ 59
def prefixEnd_255143 : Nat := 4983230072969 + 3 ^ 40 * 255143 * 2
def baseEnd_255143 : Nat := 14556777181133387282125

theorem tailTrace_255143 : CollatzResearch.WordTrace tailWord_255143 prefixEnd_255143 14556777181133387282125 := by
  unfold tailWord_255143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305829714667960800330083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6203886476445307200220055 9305829714667960800330083)
  ·
    refine ⟨13958744572001941200495125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9305829714667960800330083 13958744572001941200495125)
    ·
      refine ⟨654316151812590993773209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13958744572001941200495125 654316151812590993773209)
      ·
        refine ⟨490737113859443245329907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654316151812590993773209 490737113859443245329907)
        ·
          refine ⟨736105670789164867994861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490737113859443245329907 736105670789164867994861)
          ·
            refine ⟨276039626545936825498073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736105670789164867994861 276039626545936825498073)
            ·
              refine ⟨207029719909452619123555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276039626545936825498073 207029719909452619123555)
              ·
                refine ⟨310544579864178928685333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207029719909452619123555 310544579864178928685333)
                ·
                  refine ⟨14556777181133387282125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310544579864178928685333 14556777181133387282125)
                  ·
                    rfl

theorem cell23_255143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 6].length) (baseStart_255143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255143 prefixEnd_255143 := by exact prefixLift 255143
  have htrace : WordTrace (prefixWord ++ tailWord_255143) baseStart_255143 baseEnd_255143 := by
    simpa [prefixWord, tailWord_255143, baseEnd_255143] using wordTrace_append hprefix tailTrace_255143
  have hstable : (prefixWord ++ tailWord_255143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255143).length < 2 ^ (prefixWord ++ tailWord_255143).sum := by decide
  have hdescent : baseEnd_255143 < baseStart_255143 := by decide
  rcases family_descends (prefixWord ++ tailWord_255143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255159 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_255159 : Nat := 118140960795 + 255159 * 2 ^ 59
def prefixEnd_255159 : Nat := 4983230072969 + 3 ^ 40 * 255159 * 2
def baseEnd_255159 : Nat := 131019210320672422939051

theorem tailTrace_255159 : CollatzResearch.WordTrace tailWord_255159 prefixEnd_255159 131019210320672422939051 := by
  unfold tailWord_255159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306413282609995532912531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6204275521739997021941687 9306413282609995532912531)
  ·
    refine ⟨13959619923914993299368797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9306413282609995532912531 13959619923914993299368797)
    ·
      refine ⟨5234857471468122487263299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13959619923914993299368797 5234857471468122487263299)
      ·
        refine ⟨7852286207202183730894949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234857471468122487263299 7852286207202183730894949)
        ·
          refine ⟨1472303663850409449542803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7852286207202183730894949 1472303663850409449542803)
          ·
            refine ⟨2208455495775614174314205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472303663850409449542803 2208455495775614174314205)
            ·
              refine ⟨828170810915855315367827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2208455495775614174314205 828170810915855315367827)
              ·
                refine ⟨1242256216373782973051741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828170810915855315367827 1242256216373782973051741)
                ·
                  refine ⟨465846081140168614894403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242256216373782973051741 465846081140168614894403)
                  ·
                    refine ⟨698769121710252922341605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465846081140168614894403 698769121710252922341605)
                    ·
                      refine ⟨131019210320672422939051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 698769121710252922341605 131019210320672422939051)
                      ·
                        rfl

theorem cell23_255159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_255159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255159 prefixEnd_255159 := by exact prefixLift 255159
  have htrace : WordTrace (prefixWord ++ tailWord_255159) baseStart_255159 baseEnd_255159 := by
    simpa [prefixWord, tailWord_255159, baseEnd_255159] using wordTrace_append hprefix tailTrace_255159
  have hstable : (prefixWord ++ tailWord_255159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255159).length < 2 ^ (prefixWord ++ tailWord_255159).sum := by decide
  have hdescent : baseEnd_255159 < baseStart_255159 := by decide
  rcases family_descends (prefixWord ++ tailWord_255159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
