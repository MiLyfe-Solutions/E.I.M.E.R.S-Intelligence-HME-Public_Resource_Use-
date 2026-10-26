import V185TrunkScan20Chunk001

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_11278 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_11278 : Nat := 118140960795 + 11278 * 2 ^ 59
def prefixEnd_11278 : Nat := 4983230072969 + 3 ^ 40 * 11278 * 2
def baseEnd_11278 : Nat := 5147586508010763087235

theorem tailTrace_11278 : CollatzResearch.WordTrace tailWord_11278 prefixEnd_11278 5147586508010763087235 := by
  unfold tailWord_11278
  simp only [CollatzResearch.WordTrace]
  refine ⟨51417806643650871770311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 274228302099471316108325 51417806643650871770311)
  ·
    refine ⟨77126709965476307655467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51417806643650871770311 77126709965476307655467)
    ·
      refine ⟨115690064948214461483201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77126709965476307655467 115690064948214461483201)
      ·
        refine ⟨86767548711160846112401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115690064948214461483201 86767548711160846112401)
        ·
          refine ⟨65075661533370634584301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86767548711160846112401 65075661533370634584301)
          ·
            refine ⟨24403373075013987969113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65075661533370634584301 24403373075013987969113)
            ·
              refine ⟨18302529806260490976835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24403373075013987969113 18302529806260490976835)
              ·
                refine ⟨27453794709390736465253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18302529806260490976835 27453794709390736465253)
                ·
                  refine ⟨5147586508010763087235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27453794709390736465253 5147586508010763087235)
                  ·
                    rfl

theorem cell20_11278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_11278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11278 prefixEnd_11278 := by exact prefixLift 11278
  have htrace : WordTrace (prefixWord ++ tailWord_11278) baseStart_11278 baseEnd_11278 := by
    simpa [prefixWord, tailWord_11278, baseEnd_11278] using wordTrace_append hprefix tailTrace_11278
  have hstable : (prefixWord ++ tailWord_11278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11278).length < 2 ^ (prefixWord ++ tailWord_11278).sum := by decide
  have hdescent : baseEnd_11278 < baseStart_11278 := by decide
  rcases family_descends (prefixWord ++ tailWord_11278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11299 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_11299 : Nat := 118140960795 + 11299 * 2 ^ 59
def prefixEnd_11299 : Nat := 4983230072969 + 3 ^ 40 * 11299 * 2
def baseEnd_11299 : Nat := 5157171480228023387149

theorem tailTrace_11299 : CollatzResearch.WordTrace tailWord_11299 prefixEnd_11299 5157171480228023387149 := by
  unfold tailWord_11299
  simp only [CollatzResearch.WordTrace]
  refine ⟨412108386073127560676951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 274738924048751707117967 412108386073127560676951)
  ·
    refine ⟨618162579109691341015427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412108386073127560676951 618162579109691341015427)
    ·
      refine ⟨927243868664537011523141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618162579109691341015427 927243868664537011523141)
      ·
        refine ⟨173858225374600689660589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 927243868664537011523141 173858225374600689660589)
        ·
          refine ⟨65196834515475258622721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173858225374600689660589 65196834515475258622721)
          ·
            refine ⟨48897625886606443967041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65196834515475258622721 48897625886606443967041)
            ·
              refine ⟨36673219414954832975281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48897625886606443967041 36673219414954832975281)
              ·
                refine ⟨27504914561216124731461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36673219414954832975281 27504914561216124731461)
                ·
                  refine ⟨5157171480228023387149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27504914561216124731461 5157171480228023387149)
                  ·
                    rfl

theorem cell20_11299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_11299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11299 prefixEnd_11299 := by exact prefixLift 11299
  have htrace : WordTrace (prefixWord ++ tailWord_11299) baseStart_11299 baseEnd_11299 := by
    simpa [prefixWord, tailWord_11299, baseEnd_11299] using wordTrace_append hprefix tailTrace_11299
  have hstable : (prefixWord ++ tailWord_11299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11299).length < 2 ^ (prefixWord ++ tailWord_11299).sum := by decide
  have hdescent : baseEnd_11299 < baseStart_11299 := by decide
  rcases family_descends (prefixWord ++ tailWord_11299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11313 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_11313 : Nat := 118140960795 + 11313 * 2 ^ 59
def prefixEnd_11313 : Nat := 4983230072969 + 3 ^ 40 * 11313 * 2
def baseEnd_11313 : Nat := 5163561461706196920425

theorem tailTrace_11313 : CollatzResearch.WordTrace tailWord_11313 prefixEnd_11313 5163561461706196920425 := by
  unfold tailWord_11313
  simp only [CollatzResearch.WordTrace]
  refine ⟨412619008022407951686593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275079338681605301124395 412619008022407951686593)
  ·
    refine ⟨309464256016805963764945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412619008022407951686593 309464256016805963764945)
    ·
      refine ⟨232098192012604472823709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309464256016805963764945 232098192012604472823709)
      ·
        refine ⟨87036822004726677308891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232098192012604472823709 87036822004726677308891)
        ·
          refine ⟨130555233007090015963337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87036822004726677308891 130555233007090015963337)
          ·
            refine ⟨97916424755317511972503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130555233007090015963337 97916424755317511972503)
            ·
              refine ⟨146874637132976267958755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97916424755317511972503 146874637132976267958755)
              ·
                refine ⟨220311955699464401938133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146874637132976267958755 220311955699464401938133)
                ·
                  refine ⟨5163561461706196920425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220311955699464401938133 5163561461706196920425)
                  ·
                    rfl

theorem cell20_11313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_11313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11313 prefixEnd_11313 := by exact prefixLift 11313
  have htrace : WordTrace (prefixWord ++ tailWord_11313) baseStart_11313 baseEnd_11313 := by
    simpa [prefixWord, tailWord_11313, baseEnd_11313] using wordTrace_append hprefix tailTrace_11313
  have hstable : (prefixWord ++ tailWord_11313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11313).length < 2 ^ (prefixWord ++ tailWord_11313).sum := by decide
  have hdescent : baseEnd_11313 < baseStart_11313 := by decide
  rcases family_descends (prefixWord ++ tailWord_11313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11385 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_11385 : Nat := 118140960795 + 11385 * 2 ^ 59
def prefixEnd_11385 : Nat := 4983230072969 + 3 ^ 40 * 11385 * 2
def baseEnd_11385 : Nat := 5196424223593946520131

theorem tailTrace_11385 : CollatzResearch.WordTrace tailWord_11385 prefixEnd_11385 5196424223593946520131 := by
  unfold tailWord_11385
  simp only [CollatzResearch.WordTrace]
  refine ⟨415245063761564248307609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 276830042507709498871739 415245063761564248307609)
  ·
    refine ⟨311433797821173186230707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 415245063761564248307609 311433797821173186230707)
    ·
      refine ⟨467150696731759779346061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311433797821173186230707 467150696731759779346061)
      ·
        refine ⟨175181511274409917254773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467150696731759779346061 175181511274409917254773)
        ·
          refine ⟨16423266681975929742635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175181511274409917254773 16423266681975929742635)
          ·
            refine ⟨24634900022963894613953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16423266681975929742635 24634900022963894613953)
            ·
              refine ⟨18476175017222920960465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24634900022963894613953 18476175017222920960465)
              ·
                refine ⟨13857131262917190720349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18476175017222920960465 13857131262917190720349)
                ·
                  refine ⟨5196424223593946520131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13857131262917190720349 5196424223593946520131)
                  ·
                    rfl

theorem cell20_11385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_11385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11385 prefixEnd_11385 := by exact prefixLift 11385
  have htrace : WordTrace (prefixWord ++ tailWord_11385) baseStart_11385 baseEnd_11385 := by
    simpa [prefixWord, tailWord_11385, baseEnd_11385] using wordTrace_append hprefix tailTrace_11385
  have hstable : (prefixWord ++ tailWord_11385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11385).length < 2 ^ (prefixWord ++ tailWord_11385).sum := by decide
  have hdescent : baseEnd_11385 < baseStart_11385 := by decide
  rcases family_descends (prefixWord ++ tailWord_11385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11426 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_11426 : Nat := 118140960795 + 11426 * 2 ^ 59
def prefixEnd_11426 : Nat := 4983230072969 + 3 ^ 40 * 11426 * 2
def baseEnd_11426 : Nat := 5215137740780026153297

theorem tailTrace_11426 : CollatzResearch.WordTrace tailWord_11426 prefixEnd_11426 5215137740780026153297 := by
  unfold tailWord_11426
  simp only [CollatzResearch.WordTrace]
  refine ⟨104185114153257062637533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 277826971075352167033421 104185114153257062637533)
  ·
    refine ⟨39069417807471398489075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104185114153257062637533 39069417807471398489075)
    ·
      refine ⟨58604126711207097733613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39069417807471398489075 58604126711207097733613)
      ·
        refine ⟨21976547516702661650105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58604126711207097733613 21976547516702661650105)
        ·
          refine ⟨16482410637526996237579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21976547516702661650105 16482410637526996237579)
          ·
            refine ⟨24723615956290494356369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16482410637526996237579 24723615956290494356369)
            ·
              refine ⟨18542711967217870767277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24723615956290494356369 18542711967217870767277)
              ·
                refine ⟨6953516987706701537729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18542711967217870767277 6953516987706701537729)
                ·
                  refine ⟨5215137740780026153297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953516987706701537729 5215137740780026153297)
                  ·
                    rfl

theorem cell20_11426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_11426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11426 prefixEnd_11426 := by exact prefixLift 11426
  have htrace : WordTrace (prefixWord ++ tailWord_11426) baseStart_11426 baseEnd_11426 := by
    simpa [prefixWord, tailWord_11426, baseEnd_11426] using wordTrace_append hprefix tailTrace_11426
  have hstable : (prefixWord ++ tailWord_11426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11426).length < 2 ^ (prefixWord ++ tailWord_11426).sum := by decide
  have hdescent : baseEnd_11426 < baseStart_11426 := by decide
  rcases family_descends (prefixWord ++ tailWord_11426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11437 : List Nat := [1, 5, 2, 1, 3, 1, 7]
def baseStart_11437 : Nat := 118140960795 + 11437 * 2 ^ 59
def prefixEnd_11437 : Nat := 4983230072969 + 3 ^ 40 * 11437 * 2
def baseEnd_11437 : Nat := 580017604501430754065

theorem tailTrace_11437 : CollatzResearch.WordTrace tailWord_11437 prefixEnd_11437 580017604501430754065 := by
  unfold tailWord_11437
  simp only [CollatzResearch.WordTrace]
  refine ⟨417141659573177129200565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 278094439715451419467043 417141659573177129200565)
  ·
    refine ⟨39107030584985355862553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 417141659573177129200565 39107030584985355862553)
    ·
      refine ⟨29330272938739016896915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39107030584985355862553 29330272938739016896915)
      ·
        refine ⟨43995409408108525345373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29330272938739016896915 43995409408108525345373)
        ·
          refine ⟨16498278528040697004515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43995409408108525345373 16498278528040697004515)
          ·
            refine ⟨24747417792061045506773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16498278528040697004515 24747417792061045506773)
            ·
              refine ⟨580017604501430754065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24747417792061045506773 580017604501430754065)
              ·
                rfl

theorem cell20_11437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_11437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11437 prefixEnd_11437 := by exact prefixLift 11437
  have htrace : WordTrace (prefixWord ++ tailWord_11437) baseStart_11437 baseEnd_11437 := by
    simpa [prefixWord, tailWord_11437, baseEnd_11437] using wordTrace_append hprefix tailTrace_11437
  have hstable : (prefixWord ++ tailWord_11437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11437).length < 2 ^ (prefixWord ++ tailWord_11437).sum := by decide
  have hdescent : baseEnd_11437 < baseStart_11437 := by decide
  rcases family_descends (prefixWord ++ tailWord_11437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11516 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_11516 : Nat := 118140960795 + 11516 * 2 ^ 59
def prefixEnd_11516 : Nat := 4983230072969 + 3 ^ 40 * 11516 * 2
def baseEnd_11516 : Nat := 5256216193139713152929

theorem tailTrace_11516 : CollatzResearch.WordTrace tailWord_11516 prefixEnd_11516 5256216193139713152929 := by
  unfold tailWord_11516
  simp only [CollatzResearch.WordTrace]
  refine ⟨210011513143486810663201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 280015350857982414217601 210011513143486810663201)
  ·
    refine ⟨157508634857615107997401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210011513143486810663201 157508634857615107997401)
    ·
      refine ⟨118131476143211330998051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157508634857615107997401 118131476143211330998051)
      ·
        refine ⟨177197214214816996497077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118131476143211330998051 177197214214816996497077)
        ·
          refine ⟨16612238832639093421601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177197214214816996497077 16612238832639093421601)
          ·
            refine ⟨12459179124479320066201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16612238832639093421601 12459179124479320066201)
            ·
              refine ⟨9344384343359490049651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12459179124479320066201 9344384343359490049651)
              ·
                refine ⟨14016576515039235074477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344384343359490049651 14016576515039235074477)
                ·
                  refine ⟨5256216193139713152929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14016576515039235074477 5256216193139713152929)
                  ·
                    rfl

theorem cell20_11516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_11516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11516 prefixEnd_11516 := by exact prefixLift 11516
  have htrace : WordTrace (prefixWord ++ tailWord_11516) baseStart_11516 baseEnd_11516 := by
    simpa [prefixWord, tailWord_11516, baseEnd_11516] using wordTrace_append hprefix tailTrace_11516
  have hstable : (prefixWord ++ tailWord_11516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11516).length < 2 ^ (prefixWord ++ tailWord_11516).sum := by decide
  have hdescent : baseEnd_11516 < baseStart_11516 := by decide
  rcases family_descends (prefixWord ++ tailWord_11516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11534 : List Nat := [4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_11534 : Nat := 118140960795 + 11534 * 2 ^ 59
def prefixEnd_11534 : Nat := 4983230072969 + 3 ^ 40 * 11534 * 2
def baseEnd_11534 : Nat := 1754810627870550184285

theorem tailTrace_11534 : CollatzResearch.WordTrace tailWord_11534 prefixEnd_11534 1754810627870550184285 := by
  unfold tailWord_11534
  simp only [CollatzResearch.WordTrace]
  refine ⟨52584942527720336935207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 280453026814508463654437 52584942527720336935207)
  ·
    refine ⟨78877413791580505402811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52584942527720336935207 78877413791580505402811)
    ·
      refine ⟨118316120687370758104217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78877413791580505402811 118316120687370758104217)
      ·
        refine ⟨88737090515528068578163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118316120687370758104217 88737090515528068578163)
        ·
          refine ⟨133105635773292102867245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88737090515528068578163 133105635773292102867245)
          ·
            refine ⟨49914613414984538575217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133105635773292102867245 49914613414984538575217)
            ·
              refine ⟨37435960061238403931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49914613414984538575217 37435960061238403931413)
              ·
                refine ⟨1754810627870550184285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37435960061238403931413 1754810627870550184285)
                ·
                  rfl

theorem cell20_11534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_11534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11534 prefixEnd_11534 := by exact prefixLift 11534
  have htrace : WordTrace (prefixWord ++ tailWord_11534) baseStart_11534 baseEnd_11534 := by
    simpa [prefixWord, tailWord_11534, baseEnd_11534] using wordTrace_append hprefix tailTrace_11534
  have hstable : (prefixWord ++ tailWord_11534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11534).length < 2 ^ (prefixWord ++ tailWord_11534).sum := by decide
  have hdescent : baseEnd_11534 < baseStart_11534 := by decide
  rcases family_descends (prefixWord ++ tailWord_11534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11555 : List Nat := [1, 1, 1, 4, 2, 11]
def baseStart_11555 : Nat := 118140960795 + 11555 * 2 ^ 59
def prefixEnd_11555 : Nat := 4983230072969 + 3 ^ 40 * 11555 * 2
def baseEnd_11555 : Nat := 195333957623292994547

theorem tailTrace_11555 : CollatzResearch.WordTrace tailWord_11555 prefixEnd_11555 195333957623292994547 := by
  unfold tailWord_11555
  simp only [CollatzResearch.WordTrace]
  refine ⟨421445473145683281996119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 280963648763788854664079 421445473145683281996119)
  ·
    refine ⟨632168209718524922994179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 421445473145683281996119 632168209718524922994179)
    ·
      refine ⟨948252314577787384491269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632168209718524922994179 948252314577787384491269)
      ·
        refine ⟨177797308983335134592113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 948252314577787384491269 177797308983335134592113)
        ·
          refine ⟨133347981737501350944085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177797308983335134592113 133347981737501350944085)
          ·
            refine ⟨195333957623292994547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 133347981737501350944085 195333957623292994547)
            ·
              rfl

theorem cell20_11555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 11].length) (baseStart_11555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11555 prefixEnd_11555 := by exact prefixLift 11555
  have htrace : WordTrace (prefixWord ++ tailWord_11555) baseStart_11555 baseEnd_11555 := by
    simpa [prefixWord, tailWord_11555, baseEnd_11555] using wordTrace_append hprefix tailTrace_11555
  have hstable : (prefixWord ++ tailWord_11555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11555).length < 2 ^ (prefixWord ++ tailWord_11555).sum := by decide
  have hdescent : baseEnd_11555 < baseStart_11555 := by decide
  rcases family_descends (prefixWord ++ tailWord_11555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11593 : List Nat := [1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_11593 : Nat := 118140960795 + 11593 * 2 ^ 59
def prefixEnd_11593 : Nat := 4983230072969 + 3 ^ 40 * 11593 * 2
def baseEnd_11593 : Nat := 1763787030423222528649

theorem tailTrace_11593 : CollatzResearch.WordTrace tailWord_11593 prefixEnd_11593 1763787030423222528649 := by
  unfold tailWord_11593
  simp only [CollatzResearch.WordTrace]
  refine ⟨422831447008015771879433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 281887631338677181252955 422831447008015771879433)
  ·
    refine ⟨317123585256011828909575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 422831447008015771879433 317123585256011828909575)
    ·
      refine ⟨475685377884017743364363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317123585256011828909575 475685377884017743364363)
      ·
        refine ⟨713528066826026615046545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475685377884017743364363 713528066826026615046545)
        ·
          refine ⟨535146050119519961284909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713528066826026615046545 535146050119519961284909)
          ·
            refine ⟨200679768794819985481841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535146050119519961284909 200679768794819985481841)
            ·
              refine ⟨150509826596114989111381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200679768794819985481841 150509826596114989111381)
              ·
                refine ⟨1763787030423222528649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 150509826596114989111381 1763787030423222528649)
                ·
                  rfl

theorem cell20_11593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_11593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11593 prefixEnd_11593 := by exact prefixLift 11593
  have htrace : WordTrace (prefixWord ++ tailWord_11593) baseStart_11593 baseEnd_11593 := by
    simpa [prefixWord, tailWord_11593, baseEnd_11593] using wordTrace_append hprefix tailTrace_11593
  have hstable : (prefixWord ++ tailWord_11593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11593).length < 2 ^ (prefixWord ++ tailWord_11593).sum := by decide
  have hdescent : baseEnd_11593 < baseStart_11593 := by decide
  rcases family_descends (prefixWord ++ tailWord_11593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11620 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_11620 : Nat := 118140960795 + 11620 * 2 ^ 59
def prefixEnd_11620 : Nat := 4983230072969 + 3 ^ 40 * 11620 * 2
def baseEnd_11620 : Nat := 5303684626977573685837

theorem tailTrace_11620 : CollatzResearch.WordTrace tailWord_11620 prefixEnd_11620 5303684626977573685837 := by
  unfold tailWord_11620
  simp only [CollatzResearch.WordTrace]
  refine ⟨211908108955099691556157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 282544145273466255408209 211908108955099691556157)
  ·
    refine ⟨79465540858162384333559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211908108955099691556157 79465540858162384333559)
    ·
      refine ⟨119198311287243576500339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79465540858162384333559 119198311287243576500339)
      ·
        refine ⟨178797466930865364750509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119198311287243576500339 178797466930865364750509)
        ·
          refine ⟨67049050099074511781441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178797466930865364750509 67049050099074511781441)
          ·
            refine ⟨50286787574305883836081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67049050099074511781441 50286787574305883836081)
            ·
              refine ⟨37715090680729412877061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50286787574305883836081 37715090680729412877061)
              ·
                refine ⟨7071579502636764914449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37715090680729412877061 7071579502636764914449)
                ·
                  refine ⟨5303684626977573685837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071579502636764914449 5303684626977573685837)
                  ·
                    rfl

theorem cell20_11620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_11620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11620 prefixEnd_11620 := by exact prefixLift 11620
  have htrace : WordTrace (prefixWord ++ tailWord_11620) baseStart_11620 baseEnd_11620 := by
    simpa [prefixWord, tailWord_11620, baseEnd_11620] using wordTrace_append hprefix tailTrace_11620
  have hstable : (prefixWord ++ tailWord_11620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11620).length < 2 ^ (prefixWord ++ tailWord_11620).sum := by decide
  have hdescent : baseEnd_11620 < baseStart_11620 := by decide
  rcases family_descends (prefixWord ++ tailWord_11620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11631 : List Nat := [1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_11631 : Nat := 118140960795 + 11631 * 2 ^ 59
def prefixEnd_11631 : Nat := 4983230072969 + 3 ^ 40 * 11631 * 2
def baseEnd_11631 : Nat := 1769568442236808106375

theorem tailTrace_11631 : CollatzResearch.WordTrace tailWord_11631 prefixEnd_11631 1769568442236808106375 := by
  unfold tailWord_11631
  simp only [CollatzResearch.WordTrace]
  refine ⟨424217420870348261762747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 282811613913565507841831 424217420870348261762747)
  ·
    refine ⟨636326131305522392644121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424217420870348261762747 636326131305522392644121)
    ·
      refine ⟨477244598479141794483091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636326131305522392644121 477244598479141794483091)
      ·
        refine ⟨715866897718712691724637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477244598479141794483091 715866897718712691724637)
        ·
          refine ⟨268450086644517259396739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 715866897718712691724637 268450086644517259396739)
          ·
            refine ⟨402675129966775889095109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268450086644517259396739 402675129966775889095109)
            ·
              refine ⟨75501586868770479205333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 402675129966775889095109 75501586868770479205333)
              ·
                refine ⟨1769568442236808106375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75501586868770479205333 1769568442236808106375)
                ·
                  rfl

theorem cell20_11631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_11631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11631 prefixEnd_11631 := by exact prefixLift 11631
  have htrace : WordTrace (prefixWord ++ tailWord_11631) baseStart_11631 baseEnd_11631 := by
    simpa [prefixWord, tailWord_11631, baseEnd_11631] using wordTrace_append hprefix tailTrace_11631
  have hstable : (prefixWord ++ tailWord_11631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11631).length < 2 ^ (prefixWord ++ tailWord_11631).sum := by decide
  have hdescent : baseEnd_11631 < baseStart_11631 := by decide
  rcases family_descends (prefixWord ++ tailWord_11631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11655 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_11655 : Nat := 118140960795 + 11655 * 2 ^ 59
def prefixEnd_11655 : Nat := 4983230072969 + 3 ^ 40 * 11655 * 2
def baseEnd_11655 : Nat := 5319659580673007519027

theorem tailTrace_11655 : CollatzResearch.WordTrace tailWord_11655 prefixEnd_11655 5319659580673007519027 := by
  unfold tailWord_11655
  simp only [CollatzResearch.WordTrace]
  refine ⟨425092772783400360636419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 283395181855600240424279 425092772783400360636419)
  ·
    refine ⟨637639159175100540954629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425092772783400360636419 637639159175100540954629)
    ·
      refine ⟨119557342345331351428993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 637639159175100540954629 119557342345331351428993)
      ·
        refine ⟨89668006758998513571745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119557342345331351428993 89668006758998513571745)
        ·
          refine ⟨67251005069248885178809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89668006758998513571745 67251005069248885178809)
          ·
            refine ⟨50438253801936663884107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67251005069248885178809 50438253801936663884107)
            ·
              refine ⟨75657380702904995826161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50438253801936663884107 75657380702904995826161)
              ·
                refine ⟨56743035527178746869621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75657380702904995826161 56743035527178746869621)
                ·
                  refine ⟨5319659580673007519027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56743035527178746869621 5319659580673007519027)
                  ·
                    rfl

theorem cell20_11655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_11655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11655 prefixEnd_11655 := by exact prefixLift 11655
  have htrace : WordTrace (prefixWord ++ tailWord_11655) baseStart_11655 baseEnd_11655 := by
    simpa [prefixWord, tailWord_11655, baseEnd_11655] using wordTrace_append hprefix tailTrace_11655
  have hstable : (prefixWord ++ tailWord_11655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11655).length < 2 ^ (prefixWord ++ tailWord_11655).sum := by decide
  have hdescent : baseEnd_11655 < baseStart_11655 := by decide
  rcases family_descends (prefixWord ++ tailWord_11655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11669 : List Nat := [1, 3, 2, 1, 1, 2, 10]
def baseStart_11669 : Nat := 118140960795 + 11669 * 2 ^ 59
def prefixEnd_11669 : Nat := 4983230072969 + 3 ^ 40 * 11669 * 2
def baseEnd_11669 : Nat := 591783284683464561367

theorem tailTrace_11669 : CollatzResearch.WordTrace tailWord_11669 prefixEnd_11669 591783284683464561367 := by
  unfold tailWord_11669
  simp only [CollatzResearch.WordTrace]
  refine ⟨425603394732680751646061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 283735596488453834430707 425603394732680751646061)
  ·
    refine ⟨159601273024755281867273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 425603394732680751646061 159601273024755281867273)
    ·
      refine ⟨119700954768566461400455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159601273024755281867273 119700954768566461400455)
      ·
        refine ⟨179551432152849692100683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119700954768566461400455 179551432152849692100683)
        ·
          refine ⟨269327148229274538151025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179551432152849692100683 269327148229274538151025)
          ·
            refine ⟨201995361171955903613269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269327148229274538151025 201995361171955903613269)
            ·
              refine ⟨591783284683464561367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 201995361171955903613269 591783284683464561367)
              ·
                rfl

theorem cell20_11669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_11669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11669 prefixEnd_11669 := by exact prefixLift 11669
  have htrace : WordTrace (prefixWord ++ tailWord_11669) baseStart_11669 baseEnd_11669 := by
    simpa [prefixWord, tailWord_11669, baseEnd_11669] using wordTrace_append hprefix tailTrace_11669
  have hstable : (prefixWord ++ tailWord_11669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11669).length < 2 ^ (prefixWord ++ tailWord_11669).sum := by decide
  have hdescent : baseEnd_11669 < baseStart_11669 := by decide
  rcases family_descends (prefixWord ++ tailWord_11669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11679 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_11679 : Nat := 118140960795 + 11679 * 2 ^ 59
def prefixEnd_11679 : Nat := 4983230072969 + 3 ^ 40 * 11679 * 2
def baseEnd_11679 : Nat := 5330613834635590718929

theorem tailTrace_11679 : CollatzResearch.WordTrace tailWord_11679 prefixEnd_11679 5330613834635590718929 := by
  unfold tailWord_11679
  simp only [CollatzResearch.WordTrace]
  refine ⟨425968124696452459510091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 283978749797634973006727 425968124696452459510091)
  ·
    refine ⟨638952187044678689265137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425968124696452459510091 638952187044678689265137)
    ·
      refine ⟨479214140283509016948853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638952187044678689265137 479214140283509016948853)
      ·
        refine ⟨44926325651578970338955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 479214140283509016948853 44926325651578970338955)
        ·
          refine ⟨67389488477368455508433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44926325651578970338955 67389488477368455508433)
          ·
            refine ⟨50542116358026341631325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67389488477368455508433 50542116358026341631325)
            ·
              refine ⟨18953293634259878111747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50542116358026341631325 18953293634259878111747)
              ·
                refine ⟨28429940451389817167621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18953293634259878111747 28429940451389817167621)
                ·
                  refine ⟨5330613834635590718929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28429940451389817167621 5330613834635590718929)
                  ·
                    rfl

theorem cell20_11679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_11679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11679 prefixEnd_11679 := by exact prefixLift 11679
  have htrace : WordTrace (prefixWord ++ tailWord_11679) baseStart_11679 baseEnd_11679 := by
    simpa [prefixWord, tailWord_11679, baseEnd_11679] using wordTrace_append hprefix tailTrace_11679
  have hstable : (prefixWord ++ tailWord_11679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11679).length < 2 ^ (prefixWord ++ tailWord_11679).sum := by decide
  have hdescent : baseEnd_11679 < baseStart_11679 := by decide
  rcases family_descends (prefixWord ++ tailWord_11679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11741 : List Nat := [1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_11741 : Nat := 118140960795 + 11741 * 2 ^ 59
def prefixEnd_11741 : Nat := 4983230072969 + 3 ^ 40 * 11741 * 2
def baseEnd_11741 : Nat := 1786304108012976884003

theorem tailTrace_11741 : CollatzResearch.WordTrace tailWord_11741 prefixEnd_11741 1786304108012976884003 := by
  unfold tailWord_11741
  simp only [CollatzResearch.WordTrace]
  refine ⟨428229450471837048267077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 285486300314558032178051 428229450471837048267077)
  ·
    refine ⟨80293021963469446550077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 428229450471837048267077 80293021963469446550077)
    ·
      refine ⟨30109883236301042456279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80293021963469446550077 30109883236301042456279)
      ·
        refine ⟨45164824854451563684419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30109883236301042456279 45164824854451563684419)
        ·
          refine ⟨67747237281677345526629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45164824854451563684419 67747237281677345526629)
          ·
            refine ⟨12702606990314502286243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67747237281677345526629 12702606990314502286243)
            ·
              refine ⟨19053910485471753429365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702606990314502286243 19053910485471753429365)
              ·
                refine ⟨1786304108012976884003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19053910485471753429365 1786304108012976884003)
                ·
                  rfl

theorem cell20_11741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_11741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11741 prefixEnd_11741 := by exact prefixLift 11741
  have htrace : WordTrace (prefixWord ++ tailWord_11741) baseStart_11741 baseEnd_11741 := by
    simpa [prefixWord, tailWord_11741, baseEnd_11741] using wordTrace_append hprefix tailTrace_11741
  have hstable : (prefixWord ++ tailWord_11741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11741).length < 2 ^ (prefixWord ++ tailWord_11741).sum := by decide
  have hdescent : baseEnd_11741 < baseStart_11741 := by decide
  rcases family_descends (prefixWord ++ tailWord_11741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11786 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_11786 : Nat := 118140960795 + 11786 * 2 ^ 59
def prefixEnd_11786 : Nat := 4983230072969 + 3 ^ 40 * 11786 * 2
def baseEnd_11786 : Nat := 5379451550218774151825

theorem tailTrace_11786 : CollatzResearch.WordTrace tailWord_11786 prefixEnd_11786 5379451550218774151825 := by
  unfold tailWord_11786
  simp only [CollatzResearch.WordTrace]
  refine ⟨107467683827202433413803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 286580490205873155770141 107467683827202433413803)
  ·
    refine ⟨161201525740803650120705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107467683827202433413803 161201525740803650120705)
    ·
      refine ⟨120901144305602737590529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161201525740803650120705 120901144305602737590529)
      ·
        refine ⟨90675858229202053192897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120901144305602737590529 90675858229202053192897)
        ·
          refine ⟨68006893671901539894673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90675858229202053192897 68006893671901539894673)
          ·
            refine ⟨51005170253926154921005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68006893671901539894673 51005170253926154921005)
            ·
              refine ⟨19126938845222308095377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51005170253926154921005 19126938845222308095377)
              ·
                refine ⟨14345204133916731071533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19126938845222308095377 14345204133916731071533)
                ·
                  refine ⟨5379451550218774151825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14345204133916731071533 5379451550218774151825)
                  ·
                    rfl

theorem cell20_11786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_11786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11786 prefixEnd_11786 := by exact prefixLift 11786
  have htrace : WordTrace (prefixWord ++ tailWord_11786) baseStart_11786 baseEnd_11786 := by
    simpa [prefixWord, tailWord_11786, baseEnd_11786] using wordTrace_append hprefix tailTrace_11786
  have hstable : (prefixWord ++ tailWord_11786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11786).length < 2 ^ (prefixWord ++ tailWord_11786).sum := by decide
  have hdescent : baseEnd_11786 < baseStart_11786 := by decide
  rcases family_descends (prefixWord ++ tailWord_11786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11793 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 2]
def baseStart_11793 : Nat := 118140960795 + 11793 * 2 ^ 59
def prefixEnd_11793 : Nat := 4983230072969 + 3 ^ 40 * 11793 * 2
def baseEnd_11793 : Nat := 5382646540957860918463

theorem tailTrace_11793 : CollatzResearch.WordTrace tailWord_11793 prefixEnd_11793 5382646540957860918463 := by
  unfold tailWord_11793
  simp only [CollatzResearch.WordTrace]
  refine ⟨430126046283449929160033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 286750697522299952773355 430126046283449929160033)
  ·
    refine ⟨322594534712587446870025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 430126046283449929160033 322594534712587446870025)
    ·
      refine ⟨241945901034440585152519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322594534712587446870025 241945901034440585152519)
      ·
        refine ⟨362918851551660877728779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241945901034440585152519 362918851551660877728779)
        ·
          refine ⟨544378277327491316593169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362918851551660877728779 544378277327491316593169)
          ·
            refine ⟨408283707995618487444877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544378277327491316593169 408283707995618487444877)
            ·
              refine ⟨153106390498356932791829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408283707995618487444877 153106390498356932791829)
              ·
                refine ⟨7176862054610481224617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153106390498356932791829 7176862054610481224617)
                ·
                  refine ⟨5382646540957860918463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7176862054610481224617 5382646540957860918463)
                  ·
                    rfl

theorem cell20_11793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_11793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11793 prefixEnd_11793 := by exact prefixLift 11793
  have htrace : WordTrace (prefixWord ++ tailWord_11793) baseStart_11793 baseEnd_11793 := by
    simpa [prefixWord, tailWord_11793, baseEnd_11793] using wordTrace_append hprefix tailTrace_11793
  have hstable : (prefixWord ++ tailWord_11793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11793).length < 2 ^ (prefixWord ++ tailWord_11793).sum := by decide
  have hdescent : baseEnd_11793 < baseStart_11793 := by decide
  rcases family_descends (prefixWord ++ tailWord_11793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11807 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_11807 : Nat := 118140960795 + 11807 * 2 ^ 59
def prefixEnd_11807 : Nat := 4983230072969 + 3 ^ 40 * 11807 * 2
def baseEnd_11807 : Nat := 5389036522436034451739

theorem tailTrace_11807 : CollatzResearch.WordTrace tailWord_11807 prefixEnd_11807 5389036522436034451739 := by
  unfold tailWord_11807
  simp only [CollatzResearch.WordTrace]
  refine ⟨430636668232730320169675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 287091112155153546779783 430636668232730320169675)
  ·
    refine ⟨645955002349095480254513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 430636668232730320169675 645955002349095480254513)
    ·
      refine ⟨484466251761821610190885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 645955002349095480254513 484466251761821610190885)
      ·
        refine ⟨90837422205341551910791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 484466251761821610190885 90837422205341551910791)
        ·
          refine ⟨136256133308012327866187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90837422205341551910791 136256133308012327866187)
          ·
            refine ⟨204384199962018491799281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136256133308012327866187 204384199962018491799281)
            ·
              refine ⟨153288149971513868849461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204384199962018491799281 153288149971513868849461)
              ·
                refine ⟨14370764059829425204637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153288149971513868849461 14370764059829425204637)
                ·
                  refine ⟨5389036522436034451739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14370764059829425204637 5389036522436034451739)
                  ·
                    rfl

theorem cell20_11807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_11807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11807 prefixEnd_11807 := by exact prefixLift 11807
  have htrace : WordTrace (prefixWord ++ tailWord_11807) baseStart_11807 baseEnd_11807 := by
    simpa [prefixWord, tailWord_11807, baseEnd_11807] using wordTrace_append hprefix tailTrace_11807
  have hstable : (prefixWord ++ tailWord_11807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11807).length < 2 ^ (prefixWord ++ tailWord_11807).sum := by decide
  have hdescent : baseEnd_11807 < baseStart_11807 := by decide
  rcases family_descends (prefixWord ++ tailWord_11807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11845 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_11845 : Nat := 118140960795 + 11845 * 2 ^ 59
def prefixEnd_11845 : Nat := 4983230072969 + 3 ^ 40 * 11845 * 2
def baseEnd_11845 : Nat := 5406380757876791184917

theorem tailTrace_11845 : CollatzResearch.WordTrace tailWord_11845 prefixEnd_11845 5406380757876791184917 := by
  unfold tailWord_11845
  simp only [CollatzResearch.WordTrace]
  refine ⟨432022642095062810052989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 288015094730041873368659 432022642095062810052989)
  ·
    refine ⟨162008490785648553769871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 432022642095062810052989 162008490785648553769871)
    ·
      refine ⟨243012736178472830654807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162008490785648553769871 243012736178472830654807)
      ·
        refine ⟨364519104267709245982211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243012736178472830654807 364519104267709245982211)
        ·
          refine ⟨546778656401563868973317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364519104267709245982211 546778656401563868973317)
          ·
            refine ⟨102520998075293225432497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 546778656401563868973317 102520998075293225432497)
            ·
              refine ⟨76890748556469919074373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102520998075293225432497 76890748556469919074373)
              ·
                refine ⟨14417015354338109826445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76890748556469919074373 14417015354338109826445)
                ·
                  refine ⟨5406380757876791184917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14417015354338109826445 5406380757876791184917)
                  ·
                    rfl

theorem cell20_11845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_11845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11845 prefixEnd_11845 := by exact prefixLift 11845
  have htrace : WordTrace (prefixWord ++ tailWord_11845) baseStart_11845 baseEnd_11845 := by
    simpa [prefixWord, tailWord_11845, baseEnd_11845] using wordTrace_append hprefix tailTrace_11845
  have hstable : (prefixWord ++ tailWord_11845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11845).length < 2 ^ (prefixWord ++ tailWord_11845).sum := by decide
  have hdescent : baseEnd_11845 < baseStart_11845 := by decide
  rcases family_descends (prefixWord ++ tailWord_11845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11914 : List Nat := [3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_11914 : Nat := 118140960795 + 11914 * 2 ^ 59
def prefixEnd_11914 : Nat := 4983230072969 + 3 ^ 40 * 11914 * 2
def baseEnd_11914 : Nat := 1812624746006405961545

theorem tailTrace_11914 : CollatzResearch.WordTrace tailWord_11914 prefixEnd_11914 1812624746006405961545 := by
  unfold tailWord_11914
  simp only [CollatzResearch.WordTrace]
  refine ⟨108634819711271898578699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 289692852563391729543197 108634819711271898578699)
  ·
    refine ⟨162952229566907847868049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108634819711271898578699 162952229566907847868049)
    ·
      refine ⟨122214172175180885901037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162952229566907847868049 122214172175180885901037)
      ·
        refine ⟨45830314565692832212889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122214172175180885901037 45830314565692832212889)
        ·
          refine ⟨34372735924269624159667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45830314565692832212889 34372735924269624159667)
          ·
            refine ⟨51559103886404436239501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34372735924269624159667 51559103886404436239501)
            ·
              refine ⟨19334663957401663589813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51559103886404436239501 19334663957401663589813)
              ·
                refine ⟨1812624746006405961545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19334663957401663589813 1812624746006405961545)
                ·
                  rfl

theorem cell20_11914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_11914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11914 prefixEnd_11914 := by exact prefixLift 11914
  have htrace : WordTrace (prefixWord ++ tailWord_11914) baseStart_11914 baseEnd_11914 := by
    simpa [prefixWord, tailWord_11914, baseEnd_11914] using wordTrace_append hprefix tailTrace_11914
  have hstable : (prefixWord ++ tailWord_11914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11914).length < 2 ^ (prefixWord ++ tailWord_11914).sum := by decide
  have hdescent : baseEnd_11914 < baseStart_11914 := by decide
  rcases family_descends (prefixWord ++ tailWord_11914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11924 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_11924 : Nat := 118140960795 + 11924 * 2 ^ 59
def prefixEnd_11924 : Nat := 4983230072969 + 3 ^ 40 * 11924 * 2
def baseEnd_11924 : Nat := 5442438510503627551261

theorem tailTrace_11924 : CollatzResearch.WordTrace tailWord_11924 prefixEnd_11924 5442438510503627551261 := by
  unfold tailWord_11924
  simp only [CollatzResearch.WordTrace]
  refine ⟨217452004404429651089413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 289936005872572868119217 217452004404429651089413)
  ·
    refine ⟨40772250825830559579265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217452004404429651089413 40772250825830559579265)
    ·
      refine ⟨30579188119372919684449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40772250825830559579265 30579188119372919684449)
      ·
        refine ⟨22934391089529689763337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30579188119372919684449 22934391089529689763337)
        ·
          refine ⟨17200793317147267322503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22934391089529689763337 17200793317147267322503)
          ·
            refine ⟨25801189975720900983755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17200793317147267322503 25801189975720900983755)
            ·
              refine ⟨38701784963581351475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25801189975720900983755 38701784963581351475633)
              ·
                refine ⟨29026338722686013606725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38701784963581351475633 29026338722686013606725)
                ·
                  refine ⟨5442438510503627551261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29026338722686013606725 5442438510503627551261)
                  ·
                    rfl

theorem cell20_11924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_11924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11924 prefixEnd_11924 := by exact prefixLift 11924
  have htrace : WordTrace (prefixWord ++ tailWord_11924) baseStart_11924 baseEnd_11924 := by
    simpa [prefixWord, tailWord_11924, baseEnd_11924] using wordTrace_append hprefix tailTrace_11924
  have hstable : (prefixWord ++ tailWord_11924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11924).length < 2 ^ (prefixWord ++ tailWord_11924).sum := by decide
  have hdescent : baseEnd_11924 < baseStart_11924 := by decide
  rcases family_descends (prefixWord ++ tailWord_11924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11928 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_11928 : Nat := 118140960795 + 11928 * 2 ^ 59
def prefixEnd_11928 : Nat := 4983230072969 + 3 ^ 40 * 11928 * 2
def baseEnd_11928 : Nat := 5444264219497391417911

theorem tailTrace_11928 : CollatzResearch.WordTrace tailWord_11928 prefixEnd_11928 5444264219497391417911 := by
  unfold tailWord_11928
  simp only [CollatzResearch.WordTrace]
  refine ⟨217524950397183992662219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 290033267196245323549625 217524950397183992662219)
  ·
    refine ⟨326287425595775988993329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217524950397183992662219 326287425595775988993329)
    ·
      refine ⟨244715569196831991744997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326287425595775988993329 244715569196831991744997)
      ·
        refine ⟨45884169224405998452187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244715569196831991744997 45884169224405998452187)
        ·
          refine ⟨68826253836608997678281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45884169224405998452187 68826253836608997678281)
          ·
            refine ⟨51619690377456748258711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68826253836608997678281 51619690377456748258711)
            ·
              refine ⟨77429535566185122388067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51619690377456748258711 77429535566185122388067)
              ·
                refine ⟨116144303349277683582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77429535566185122388067 116144303349277683582101)
                ·
                  refine ⟨5444264219497391417911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116144303349277683582101 5444264219497391417911)
                  ·
                    rfl

theorem cell20_11928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_11928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11928 prefixEnd_11928 := by exact prefixLift 11928
  have htrace : WordTrace (prefixWord ++ tailWord_11928) baseStart_11928 baseEnd_11928 := by
    simpa [prefixWord, tailWord_11928, baseEnd_11928] using wordTrace_append hprefix tailTrace_11928
  have hstable : (prefixWord ++ tailWord_11928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11928).length < 2 ^ (prefixWord ++ tailWord_11928).sum := by decide
  have hdescent : baseEnd_11928 < baseStart_11928 := by decide
  rcases family_descends (prefixWord ++ tailWord_11928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11959 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_11959 : Nat := 118140960795 + 11959 * 2 ^ 59
def prefixEnd_11959 : Nat := 4983230072969 + 3 ^ 40 * 11959 * 2
def baseEnd_11959 : Nat := 5458413464199061384451

theorem tailTrace_11959 : CollatzResearch.WordTrace tailWord_11959 prefixEnd_11959 5458413464199061384451 := by
  unfold tailWord_11959
  simp only [CollatzResearch.WordTrace]
  refine ⟨436180563682060279702931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 290787042454706853135287 436180563682060279702931)
  ·
    refine ⟨654270845523090419554397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436180563682060279702931 654270845523090419554397)
    ·
      refine ⟨245351567071158907332899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 654270845523090419554397 245351567071158907332899)
      ·
        refine ⟨368027350606738360999349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245351567071158907332899 368027350606738360999349)
        ·
          refine ⟨34502564119381721343689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 368027350606738360999349 34502564119381721343689)
          ·
            refine ⟨25876923089536291007767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34502564119381721343689 25876923089536291007767)
            ·
              refine ⟨38815384634304436511651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25876923089536291007767 38815384634304436511651)
              ·
                refine ⟨58223076951456654767477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38815384634304436511651 58223076951456654767477)
                ·
                  refine ⟨5458413464199061384451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58223076951456654767477 5458413464199061384451)
                  ·
                    rfl

theorem cell20_11959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_11959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11959 prefixEnd_11959 := by exact prefixLift 11959
  have htrace : WordTrace (prefixWord ++ tailWord_11959) baseStart_11959 baseEnd_11959 := by
    simpa [prefixWord, tailWord_11959, baseEnd_11959] using wordTrace_append hprefix tailTrace_11959
  have hstable : (prefixWord ++ tailWord_11959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11959).length < 2 ^ (prefixWord ++ tailWord_11959).sum := by decide
  have hdescent : baseEnd_11959 < baseStart_11959 := by decide
  rcases family_descends (prefixWord ++ tailWord_11959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11976 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_11976 : Nat := 118140960795 + 11976 * 2 ^ 59
def prefixEnd_11976 : Nat := 4983230072969 + 3 ^ 40 * 11976 * 2
def baseEnd_11976 : Nat := 5466172727422557817715

theorem tailTrace_11976 : CollatzResearch.WordTrace tailWord_11976 prefixEnd_11976 5466172727422557817715 := by
  unfold tailWord_11976
  simp only [CollatzResearch.WordTrace]
  refine ⟨218400302310236091535891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 291200403080314788714521 218400302310236091535891)
  ·
    refine ⟨327600453465354137303837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218400302310236091535891 327600453465354137303837)
    ·
      refine ⟨122850170049507801488939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327600453465354137303837 122850170049507801488939)
      ·
        refine ⟨184275255074261702233409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122850170049507801488939 184275255074261702233409)
        ·
          refine ⟨138206441305696276675057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184275255074261702233409 138206441305696276675057)
          ·
            refine ⟨103654830979272207506293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138206441305696276675057 103654830979272207506293)
            ·
              refine ⟨9717640404306769453715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103654830979272207506293 9717640404306769453715)
              ·
                refine ⟨14576460606460154180573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717640404306769453715 14576460606460154180573)
                ·
                  refine ⟨5466172727422557817715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14576460606460154180573 5466172727422557817715)
                  ·
                    rfl

theorem cell20_11976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_11976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11976 prefixEnd_11976 := by exact prefixLift 11976
  have htrace : WordTrace (prefixWord ++ tailWord_11976) baseStart_11976 baseEnd_11976 := by
    simpa [prefixWord, tailWord_11976, baseEnd_11976] using wordTrace_append hprefix tailTrace_11976
  have hstable : (prefixWord ++ tailWord_11976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11976).length < 2 ^ (prefixWord ++ tailWord_11976).sum := by decide
  have hdescent : baseEnd_11976 < baseStart_11976 := by decide
  rcases family_descends (prefixWord ++ tailWord_11976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11987 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_11987 : Nat := 118140960795 + 11987 * 2 ^ 59
def prefixEnd_11987 : Nat := 4983230072969 + 3 ^ 40 * 11987 * 2
def baseEnd_11987 : Nat := 5471193427155408451003

theorem tailTrace_11987 : CollatzResearch.WordTrace tailWord_11987 prefixEnd_11987 5471193427155408451003 := by
  unfold tailWord_11987
  simp only [CollatzResearch.WordTrace]
  refine ⟨437201807580621061722215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 291467871720414041148143 437201807580621061722215)
  ·
    refine ⟨655802711370931592583323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437201807580621061722215 655802711370931592583323)
    ·
      refine ⟨983704067056397388874985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655802711370931592583323 983704067056397388874985)
      ·
        refine ⟨737778050292298041656239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983704067056397388874985 737778050292298041656239)
        ·
          refine ⟨1106667075438447062484359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737778050292298041656239 1106667075438447062484359)
          ·
            refine ⟨1660000613157670593726539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106667075438447062484359 1660000613157670593726539)
            ·
              refine ⟨2490000919736505890589809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660000613157670593726539 2490000919736505890589809)
              ·
                refine ⟨1867500689802379417942357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490000919736505890589809 1867500689802379417942357)
                ·
                  refine ⟨5471193427155408451003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1867500689802379417942357 5471193427155408451003)
                  ·
                    rfl

theorem cell20_11987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_11987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11987 prefixEnd_11987 := by exact prefixLift 11987
  have htrace : WordTrace (prefixWord ++ tailWord_11987) baseStart_11987 baseEnd_11987 := by
    simpa [prefixWord, tailWord_11987, baseEnd_11987] using wordTrace_append hprefix tailTrace_11987
  have hstable : (prefixWord ++ tailWord_11987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11987).length < 2 ^ (prefixWord ++ tailWord_11987).sum := by decide
  have hdescent : baseEnd_11987 < baseStart_11987 := by decide
  rcases family_descends (prefixWord ++ tailWord_11987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11996 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_11996 : Nat := 118140960795 + 11996 * 2 ^ 59
def prefixEnd_11996 : Nat := 4983230072969 + 3 ^ 40 * 11996 * 2
def baseEnd_11996 : Nat := 5475301272391377150967

theorem tailTrace_11996 : CollatzResearch.WordTrace tailWord_11996 prefixEnd_11996 5475301272391377150967 := by
  unfold tailWord_11996
  simp only [CollatzResearch.WordTrace]
  refine ⟨218765032274007799399921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 291686709698677065866561 218765032274007799399921)
  ·
    refine ⟨164073774205505849549941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218765032274007799399921 164073774205505849549941)
    ·
      refine ⟨15381916331766173395307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164073774205505849549941 15381916331766173395307)
      ·
        refine ⟨23072874497649260092961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15381916331766173395307 23072874497649260092961)
        ·
          refine ⟨17304655873236945069721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23072874497649260092961 17304655873236945069721)
          ·
            refine ⟨12978491904927708802291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17304655873236945069721 12978491904927708802291)
            ·
              refine ⟨19467737857391563203437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978491904927708802291 19467737857391563203437)
              ·
                refine ⟨7300401696521836201289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19467737857391563203437 7300401696521836201289)
                ·
                  refine ⟨5475301272391377150967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300401696521836201289 5475301272391377150967)
                  ·
                    rfl

theorem cell20_11996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_11996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11996 prefixEnd_11996 := by exact prefixLift 11996
  have htrace : WordTrace (prefixWord ++ tailWord_11996) baseStart_11996 baseEnd_11996 := by
    simpa [prefixWord, tailWord_11996, baseEnd_11996] using wordTrace_append hprefix tailTrace_11996
  have hstable : (prefixWord ++ tailWord_11996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11996).length < 2 ^ (prefixWord ++ tailWord_11996).sum := by decide
  have hdescent : baseEnd_11996 < baseStart_11996 := by decide
  rcases family_descends (prefixWord ++ tailWord_11996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12007 : List Nat := [1, 1, 5, 4, 1, 2, 6]
def baseStart_12007 : Nat := 118140960795 + 12007 * 2 ^ 59
def prefixEnd_12007 : Nat := 4983230072969 + 3 ^ 40 * 12007 * 2
def baseEnd_12007 : Nat := 608924663569358642695

theorem tailTrace_12007 : CollatzResearch.WordTrace tailWord_12007 prefixEnd_12007 608924663569358642695 := by
  unfold tailWord_12007
  simp only [CollatzResearch.WordTrace]
  refine ⟨437931267508164477450275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 291954178338776318300183 437931267508164477450275)
  ·
    refine ⟨656896901262246716175413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437931267508164477450275 656896901262246716175413)
    ·
      refine ⟨61584084493335629641445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 656896901262246716175413 61584084493335629641445)
      ·
        refine ⟨11547015842500430557771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61584084493335629641445 11547015842500430557771)
        ·
          refine ⟨17320523763750645836657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11547015842500430557771 17320523763750645836657)
          ·
            refine ⟨12990392822812984377493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17320523763750645836657 12990392822812984377493)
            ·
              refine ⟨608924663569358642695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12990392822812984377493 608924663569358642695)
              ·
                rfl

theorem cell20_12007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_12007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12007 prefixEnd_12007 := by exact prefixLift 12007
  have htrace : WordTrace (prefixWord ++ tailWord_12007) baseStart_12007 baseEnd_12007 := by
    simpa [prefixWord, tailWord_12007, baseEnd_12007] using wordTrace_append hprefix tailTrace_12007
  have hstable : (prefixWord ++ tailWord_12007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12007).length < 2 ^ (prefixWord ++ tailWord_12007).sum := by decide
  have hdescent : baseEnd_12007 < baseStart_12007 := by decide
  rcases family_descends (prefixWord ++ tailWord_12007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12056 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_12056 : Nat := 118140960795 + 12056 * 2 ^ 59
def prefixEnd_12056 : Nat := 4983230072969 + 3 ^ 40 * 12056 * 2
def baseEnd_12056 : Nat := 5502686907297835150721

theorem tailTrace_12056 : CollatzResearch.WordTrace tailWord_12056 prefixEnd_12056 5502686907297835150721 := by
  unfold tailWord_12056
  simp only [CollatzResearch.WordTrace]
  refine ⟨219859222165322922992011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 293145629553763897322681 219859222165322922992011)
  ·
    refine ⟨329788833247984384488017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219859222165322922992011 329788833247984384488017)
    ·
      refine ⟨247341624935988288366013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329788833247984384488017 247341624935988288366013)
      ·
        refine ⟨92753109350995608137255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247341624935988288366013 92753109350995608137255)
        ·
          refine ⟨139129664026493412205883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92753109350995608137255 139129664026493412205883)
          ·
            refine ⟨208694496039740118308825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139129664026493412205883 208694496039740118308825)
            ·
              refine ⟨156520872029805088731619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208694496039740118308825 156520872029805088731619)
              ·
                refine ⟨234781308044707633097429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156520872029805088731619 234781308044707633097429)
                ·
                  refine ⟨5502686907297835150721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 234781308044707633097429 5502686907297835150721)
                  ·
                    rfl

theorem cell20_12056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_12056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12056 prefixEnd_12056 := by exact prefixLift 12056
  have htrace : WordTrace (prefixWord ++ tailWord_12056) baseStart_12056 baseEnd_12056 := by
    simpa [prefixWord, tailWord_12056, baseEnd_12056] using wordTrace_append hprefix tailTrace_12056
  have hstable : (prefixWord ++ tailWord_12056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12056).length < 2 ^ (prefixWord ++ tailWord_12056).sum := by decide
  have hdescent : baseEnd_12056 < baseStart_12056 := by decide
  rcases family_descends (prefixWord ++ tailWord_12056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12062 : List Nat := [4, 3, 2, 2, 2, 7]
def baseStart_12062 : Nat := 118140960795 + 12062 * 2 ^ 59
def prefixEnd_12062 : Nat := 4983230072969 + 3 ^ 40 * 12062 * 2
def baseEnd_12062 : Nat := 203904647066240035211

theorem tailTrace_12062 : CollatzResearch.WordTrace tailWord_12062 prefixEnd_12062 203904647066240035211 := by
  unfold tailWord_12062
  simp only [CollatzResearch.WordTrace]
  refine ⟨54992160288613608837805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 293291521539272580468293 54992160288613608837805)
  ·
    refine ⟨20622060108230103314177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54992160288613608837805 20622060108230103314177)
    ·
      refine ⟨15466545081172577485633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20622060108230103314177 15466545081172577485633)
      ·
        refine ⟨11599908810879433114225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15466545081172577485633 11599908810879433114225)
        ·
          refine ⟨8699931608159574835669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11599908810879433114225 8699931608159574835669)
          ·
            refine ⟨203904647066240035211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8699931608159574835669 203904647066240035211)
            ·
              rfl

theorem cell20_12062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 7].length) (baseStart_12062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12062 prefixEnd_12062 := by exact prefixLift 12062
  have htrace : WordTrace (prefixWord ++ tailWord_12062) baseStart_12062 baseEnd_12062 := by
    simpa [prefixWord, tailWord_12062, baseEnd_12062] using wordTrace_append hprefix tailTrace_12062
  have hstable : (prefixWord ++ tailWord_12062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12062).length < 2 ^ (prefixWord ++ tailWord_12062).sum := by decide
  have hdescent : baseEnd_12062 < baseStart_12062 := by decide
  rcases family_descends (prefixWord ++ tailWord_12062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12076 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_12076 : Nat := 118140960795 + 12076 * 2 ^ 59
def prefixEnd_12076 : Nat := 4983230072969 + 3 ^ 40 * 12076 * 2
def baseEnd_12076 : Nat := 5511815452266654483973

theorem tailTrace_12076 : CollatzResearch.WordTrace tailWord_12076 prefixEnd_12076 5511815452266654483973 := by
  unfold tailWord_12076
  simp only [CollatzResearch.WordTrace]
  refine ⟨220223952129094630856041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 293631936172126174474721 220223952129094630856041)
  ·
    refine ⟨165167964096820973142031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220223952129094630856041 165167964096820973142031)
    ·
      refine ⟨247751946145231459713047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165167964096820973142031 247751946145231459713047)
      ·
        refine ⟨371627919217847189569571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247751946145231459713047 371627919217847189569571)
        ·
          refine ⟨557441878826770784354357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371627919217847189569571 557441878826770784354357)
          ·
            refine ⟨52260176140009761033221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 557441878826770784354357 52260176140009761033221)
            ·
              refine ⟨9798783026251830193729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52260176140009761033221 9798783026251830193729)
              ·
                refine ⟨7349087269688872645297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798783026251830193729 7349087269688872645297)
                ·
                  refine ⟨5511815452266654483973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7349087269688872645297 5511815452266654483973)
                  ·
                    rfl

theorem cell20_12076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_12076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12076 prefixEnd_12076 := by exact prefixLift 12076
  have htrace : WordTrace (prefixWord ++ tailWord_12076) baseStart_12076 baseEnd_12076 := by
    simpa [prefixWord, tailWord_12076, baseEnd_12076] using wordTrace_append hprefix tailTrace_12076
  have hstable : (prefixWord ++ tailWord_12076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12076).length < 2 ^ (prefixWord ++ tailWord_12076).sum := by decide
  have hdescent : baseEnd_12076 < baseStart_12076 := by decide
  rcases family_descends (prefixWord ++ tailWord_12076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12083 : List Nat := [1, 1, 1, 2, 8, 1, 1, 5]
def baseStart_12083 : Nat := 118140960795 + 12083 * 2 ^ 59
def prefixEnd_12083 : Nat := 4983230072969 + 3 ^ 40 * 12083 * 2
def baseEnd_12083 : Nat := 1838336814335247083537

theorem tailTrace_12083 : CollatzResearch.WordTrace tailWord_12083 prefixEnd_12083 1838336814335247083537 := by
  unfold tailWord_12083
  simp only [CollatzResearch.WordTrace]
  refine ⟨440703215232829457216903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 293802143488552971477935 440703215232829457216903)
  ·
    refine ⟨661054822849244185825355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440703215232829457216903 661054822849244185825355)
    ·
      refine ⟨991582234273866278738033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661054822849244185825355 991582234273866278738033)
      ·
        refine ⟨743686675705399709053525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 991582234273866278738033 743686675705399709053525)
        ·
          refine ⟨8715078230922652840471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 743686675705399709053525 8715078230922652840471)
          ·
            refine ⟨13072617346383979260707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715078230922652840471 13072617346383979260707)
            ·
              refine ⟨19608926019575968891061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13072617346383979260707 19608926019575968891061)
              ·
                refine ⟨1838336814335247083537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19608926019575968891061 1838336814335247083537)
                ·
                  rfl

theorem cell20_12083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_12083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12083 prefixEnd_12083 := by exact prefixLift 12083
  have htrace : WordTrace (prefixWord ++ tailWord_12083) baseStart_12083 baseEnd_12083 := by
    simpa [prefixWord, tailWord_12083, baseEnd_12083] using wordTrace_append hprefix tailTrace_12083
  have hstable : (prefixWord ++ tailWord_12083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12083).length < 2 ^ (prefixWord ++ tailWord_12083).sum := by decide
  have hdescent : baseEnd_12083 < baseStart_12083 := by decide
  rcases family_descends (prefixWord ++ tailWord_12083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12104 : List Nat := [2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_12104 : Nat := 118140960795 + 12104 * 2 ^ 59
def prefixEnd_12104 : Nat := 4983230072969 + 3 ^ 40 * 12104 * 2
def baseEnd_12104 : Nat := 1841531805074333850175

theorem tailTrace_12104 : CollatzResearch.WordTrace tailWord_12104 prefixEnd_12104 1841531805074333850175 := by
  unfold tailWord_12104
  simp only [CollatzResearch.WordTrace]
  refine ⟨220734574078375021865683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 294312765437833362487577 220734574078375021865683)
  ·
    refine ⟨331101861117562532798525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220734574078375021865683 331101861117562532798525)
    ·
      refine ⟨124163197919085949799447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331101861117562532798525 124163197919085949799447)
      ·
        refine ⟨186244796878628924699171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124163197919085949799447 186244796878628924699171)
        ·
          refine ⟨279367195317943387048757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186244796878628924699171 279367195317943387048757)
          ·
            refine ⟨26190674561057192535821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279367195317943387048757 26190674561057192535821)
            ·
              refine ⟨9821502960396447200933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26190674561057192535821 9821502960396447200933)
              ·
                refine ⟨1841531805074333850175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9821502960396447200933 1841531805074333850175)
                ·
                  rfl

theorem cell20_12104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_12104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12104 prefixEnd_12104 := by exact prefixLift 12104
  have htrace : WordTrace (prefixWord ++ tailWord_12104) baseStart_12104 baseEnd_12104 := by
    simpa [prefixWord, tailWord_12104, baseEnd_12104] using wordTrace_append hprefix tailTrace_12104
  have hstable : (prefixWord ++ tailWord_12104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12104).length < 2 ^ (prefixWord ++ tailWord_12104).sum := by decide
  have hdescent : baseEnd_12104 < baseStart_12104 := by decide
  rcases family_descends (prefixWord ++ tailWord_12104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12114 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_12114 : Nat := 118140960795 + 12114 * 2 ^ 59
def prefixEnd_12114 : Nat := 4983230072969 + 3 ^ 40 * 12114 * 2
def baseEnd_12114 : Nat := 5529159687707411217151

theorem tailTrace_12114 : CollatzResearch.WordTrace tailWord_12114 prefixEnd_12114 5529159687707411217151 := by
  unfold tailWord_12114
  simp only [CollatzResearch.WordTrace]
  refine ⟨110458469530130437898849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 294555918747014501063597 110458469530130437898849)
  ·
    refine ⟨82843852147597828424137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110458469530130437898849 82843852147597828424137)
    ·
      refine ⟨62132889110698371318103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82843852147597828424137 62132889110698371318103)
      ·
        refine ⟨93199333666047556977155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62132889110698371318103 93199333666047556977155)
        ·
          refine ⟨139799000499071335465733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93199333666047556977155 139799000499071335465733)
          ·
            refine ⟨26212312593575875399825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139799000499071335465733 26212312593575875399825)
            ·
              refine ⟨19659234445181906549869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26212312593575875399825 19659234445181906549869)
              ·
                refine ⟨7372212916943214956201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19659234445181906549869 7372212916943214956201)
                ·
                  refine ⟨5529159687707411217151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372212916943214956201 5529159687707411217151)
                  ·
                    rfl

theorem cell20_12114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_12114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12114 prefixEnd_12114 := by exact prefixLift 12114
  have htrace : WordTrace (prefixWord ++ tailWord_12114) baseStart_12114 baseEnd_12114 := by
    simpa [prefixWord, tailWord_12114, baseEnd_12114] using wordTrace_append hprefix tailTrace_12114
  have hstable : (prefixWord ++ tailWord_12114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12114).length < 2 ^ (prefixWord ++ tailWord_12114).sum := by decide
  have hdescent : baseEnd_12114 < baseStart_12114 := by decide
  rcases family_descends (prefixWord ++ tailWord_12114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12124 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_12124 : Nat := 118140960795 + 12124 * 2 ^ 59
def prefixEnd_12124 : Nat := 4983230072969 + 3 ^ 40 * 12124 * 2
def baseEnd_12124 : Nat := 5533723960191820883777

theorem tailTrace_12124 : CollatzResearch.WordTrace tailWord_12124 prefixEnd_12124 5533723960191820883777 := by
  unfold tailWord_12124
  simp only [CollatzResearch.WordTrace]
  refine ⟨221099304042146729729713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 294799072056195639639617 221099304042146729729713)
  ·
    refine ⟨165824478031610047297285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221099304042146729729713 165824478031610047297285)
    ·
      refine ⟨31092089630926883868241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165824478031610047297285 31092089630926883868241)
      ·
        refine ⟨23319067223195162901181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31092089630926883868241 23319067223195162901181)
        ·
          refine ⟨8744650208698186087943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23319067223195162901181 8744650208698186087943)
          ·
            refine ⟨13116975313047279131915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8744650208698186087943 13116975313047279131915)
            ·
              refine ⟨19675462969570918697873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13116975313047279131915 19675462969570918697873)
              ·
                refine ⟨14756597227178189023405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19675462969570918697873 14756597227178189023405)
                ·
                  refine ⟨5533723960191820883777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14756597227178189023405 5533723960191820883777)
                  ·
                    rfl

theorem cell20_12124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_12124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12124 prefixEnd_12124 := by exact prefixLift 12124
  have htrace : WordTrace (prefixWord ++ tailWord_12124) baseStart_12124 baseEnd_12124 := by
    simpa [prefixWord, tailWord_12124, baseEnd_12124] using wordTrace_append hprefix tailTrace_12124
  have hstable : (prefixWord ++ tailWord_12124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12124).length < 2 ^ (prefixWord ++ tailWord_12124).sum := by decide
  have hdescent : baseEnd_12124 < baseStart_12124 := by decide
  rcases family_descends (prefixWord ++ tailWord_12124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12128 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_12128 : Nat := 118140960795 + 12128 * 2 ^ 59
def prefixEnd_12128 : Nat := 4983230072969 + 3 ^ 40 * 12128 * 2
def baseEnd_12128 : Nat := 5535549669185584750427

theorem tailTrace_12128 : CollatzResearch.WordTrace tailWord_12128 prefixEnd_12128 5535549669185584750427 := by
  unfold tailWord_12128
  simp only [CollatzResearch.WordTrace]
  refine ⟨221172250034901071302519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 294896333379868095070025 221172250034901071302519)
  ·
    refine ⟨331758375052351606953779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221172250034901071302519 331758375052351606953779)
    ·
      refine ⟨497637562578527410430669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331758375052351606953779 497637562578527410430669)
      ·
        refine ⟨186614085966947778911501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497637562578527410430669 186614085966947778911501)
        ·
          refine ⟨69980282237605417091813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186614085966947778911501 69980282237605417091813)
          ·
            refine ⟨13121302919551015704715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69980282237605417091813 13121302919551015704715)
            ·
              refine ⟨19681954379326523557073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13121302919551015704715 19681954379326523557073)
              ·
                refine ⟨14761465784494892667805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19681954379326523557073 14761465784494892667805)
                ·
                  refine ⟨5535549669185584750427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14761465784494892667805 5535549669185584750427)
                  ·
                    rfl

theorem cell20_12128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_12128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12128 prefixEnd_12128 := by exact prefixLift 12128
  have htrace : WordTrace (prefixWord ++ tailWord_12128) baseStart_12128 baseEnd_12128 := by
    simpa [prefixWord, tailWord_12128, baseEnd_12128] using wordTrace_append hprefix tailTrace_12128
  have hstable : (prefixWord ++ tailWord_12128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12128).length < 2 ^ (prefixWord ++ tailWord_12128).sum := by decide
  have hdescent : baseEnd_12128 < baseStart_12128 := by decide
  rcases family_descends (prefixWord ++ tailWord_12128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12135 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 2]
def baseStart_12135 : Nat := 118140960795 + 12135 * 2 ^ 59
def prefixEnd_12135 : Nat := 4983230072969 + 3 ^ 40 * 12135 * 2
def baseEnd_12135 : Nat := 5538744659924671517065

theorem tailTrace_12135 : CollatzResearch.WordTrace tailWord_12135 prefixEnd_12135 5538744659924671517065 := by
  unfold tailWord_12135
  simp only [CollatzResearch.WordTrace]
  refine ⟨442599811044442338109859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 295066540696294892073239 442599811044442338109859)
  ·
    refine ⟨663899716566663507164789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 442599811044442338109859 663899716566663507164789)
    ·
      refine ⟨62240598428124703796699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 663899716566663507164789 62240598428124703796699)
      ·
        refine ⟨93360897642187055695049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62240598428124703796699 93360897642187055695049)
        ·
          refine ⟨70020673231640291771287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93360897642187055695049 70020673231640291771287)
          ·
            refine ⟨105031009847460437656931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70020673231640291771287 105031009847460437656931)
            ·
              refine ⟨157546514771190656485397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105031009847460437656931 157546514771190656485397)
              ·
                refine ⟨7384992879899562022753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157546514771190656485397 7384992879899562022753)
                ·
                  refine ⟨5538744659924671517065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384992879899562022753 5538744659924671517065)
                  ·
                    rfl

theorem cell20_12135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2].length) (baseStart_12135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12135 prefixEnd_12135 := by exact prefixLift 12135
  have htrace : WordTrace (prefixWord ++ tailWord_12135) baseStart_12135 baseEnd_12135 := by
    simpa [prefixWord, tailWord_12135, baseEnd_12135] using wordTrace_append hprefix tailTrace_12135
  have hstable : (prefixWord ++ tailWord_12135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12135).length < 2 ^ (prefixWord ++ tailWord_12135).sum := by decide
  have hdescent : baseEnd_12135 < baseStart_12135 := by decide
  rcases family_descends (prefixWord ++ tailWord_12135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12163 : List Nat := [1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_12163 : Nat := 118140960795 + 12163 * 2 ^ 59
def prefixEnd_12163 : Nat := 4983230072969 + 3 ^ 40 * 12163 * 2
def baseEnd_12163 : Nat := 1850508207627006194539

theorem tailTrace_12163 : CollatzResearch.WordTrace tailWord_12163 prefixEnd_12163 1850508207627006194539 := by
  unfold tailWord_12163
  simp only [CollatzResearch.WordTrace]
  refine ⟨443621054943003120129143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 295747369962002080086095 443621054943003120129143)
  ·
    refine ⟨665431582414504680193715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 443621054943003120129143 665431582414504680193715)
    ·
      refine ⟨998147373621757020290573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665431582414504680193715 998147373621757020290573)
      ·
        refine ⟨374305265108158882608965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 998147373621757020290573 374305265108158882608965)
        ·
          refine ⟨70182237207779790489181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374305265108158882608965 70182237207779790489181)
          ·
            refine ⟨26318338952917421433443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70182237207779790489181 26318338952917421433443)
            ·
              refine ⟨39477508429376132150165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26318338952917421433443 39477508429376132150165)
              ·
                refine ⟨1850508207627006194539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39477508429376132150165 1850508207627006194539)
                ·
                  rfl

theorem cell20_12163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_12163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12163 prefixEnd_12163 := by exact prefixLift 12163
  have htrace : WordTrace (prefixWord ++ tailWord_12163) baseStart_12163 baseEnd_12163 := by
    simpa [prefixWord, tailWord_12163, baseEnd_12163] using wordTrace_append hprefix tailTrace_12163
  have hstable : (prefixWord ++ tailWord_12163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12163).length < 2 ^ (prefixWord ++ tailWord_12163).sum := by decide
  have hdescent : baseEnd_12163 < baseStart_12163 := by decide
  rcases family_descends (prefixWord ++ tailWord_12163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12177 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_12177 : Nat := 118140960795 + 12177 * 2 ^ 59
def prefixEnd_12177 : Nat := 4983230072969 + 3 ^ 40 * 12177 * 2
def baseEnd_12177 : Nat := 5557914604359192116893

theorem tailTrace_12177 : CollatzResearch.WordTrace tailWord_12177 prefixEnd_12177 5557914604359192116893 := by
  unfold tailWord_12177
  simp only [CollatzResearch.WordTrace]
  refine ⟨444131676892283511138785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 296087784594855674092523 444131676892283511138785)
  ·
    refine ⟨333098757669212633354089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 444131676892283511138785 333098757669212633354089)
    ·
      refine ⟨249824068251909475015567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333098757669212633354089 249824068251909475015567)
      ·
        refine ⟨374736102377864212523351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249824068251909475015567 374736102377864212523351)
        ·
          refine ⟨562104153566796318785027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374736102377864212523351 562104153566796318785027)
          ·
            refine ⟨843156230350194478177541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562104153566796318785027 843156230350194478177541)
            ·
              refine ⟨158091793190661464658289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 843156230350194478177541 158091793190661464658289)
              ·
                refine ⟨118568844892996098493717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158091793190661464658289 118568844892996098493717)
                ·
                  refine ⟨5557914604359192116893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118568844892996098493717 5557914604359192116893)
                  ·
                    rfl

theorem cell20_12177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_12177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12177 prefixEnd_12177 := by exact prefixLift 12177
  have htrace : WordTrace (prefixWord ++ tailWord_12177) baseStart_12177 baseEnd_12177 := by
    simpa [prefixWord, tailWord_12177, baseEnd_12177] using wordTrace_append hprefix tailTrace_12177
  have hstable : (prefixWord ++ tailWord_12177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12177).length < 2 ^ (prefixWord ++ tailWord_12177).sum := by decide
  have hdescent : baseEnd_12177 < baseStart_12177 := by decide
  rcases family_descends (prefixWord ++ tailWord_12177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12180 : List Nat := [2, 4, 2, 1, 1, 4, 6]
def baseStart_12180 : Nat := 118140960795 + 12180 * 2 ^ 59
def prefixEnd_12180 : Nat := 4983230072969 + 3 ^ 40 * 12180 * 2
def baseEnd_12180 : Nat := 617698209567168335209

theorem tailTrace_12180 : CollatzResearch.WordTrace tailWord_12180 prefixEnd_12180 617698209567168335209 := by
  unfold tailWord_12180
  simp only [CollatzResearch.WordTrace]
  refine ⟨222120547940707511748997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 296160730587610015665329 222120547940707511748997)
  ·
    refine ⟨41647602738882658452937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222120547940707511748997 41647602738882658452937)
    ·
      refine ⟨31235702054161993839703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41647602738882658452937 31235702054161993839703)
      ·
        refine ⟨46853553081242990759555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31235702054161993839703 46853553081242990759555)
        ·
          refine ⟨70280329621864486139333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46853553081242990759555 70280329621864486139333)
          ·
            refine ⟨13177561804099591151125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70280329621864486139333 13177561804099591151125)
            ·
              refine ⟨617698209567168335209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13177561804099591151125 617698209567168335209)
              ·
                rfl

theorem cell20_12180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_12180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12180 prefixEnd_12180 := by exact prefixLift 12180
  have htrace : WordTrace (prefixWord ++ tailWord_12180) baseStart_12180 baseEnd_12180 := by
    simpa [prefixWord, tailWord_12180, baseEnd_12180] using wordTrace_append hprefix tailTrace_12180
  have hstable : (prefixWord ++ tailWord_12180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12180).length < 2 ^ (prefixWord ++ tailWord_12180).sum := by decide
  have hdescent : baseEnd_12180 < baseStart_12180 := by decide
  rcases family_descends (prefixWord ++ tailWord_12180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12215 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_12215 : Nat := 118140960795 + 12215 * 2 ^ 59
def prefixEnd_12215 : Nat := 4983230072969 + 3 ^ 40 * 12215 * 2
def baseEnd_12215 : Nat := 5575258839799948850071

theorem tailTrace_12215 : CollatzResearch.WordTrace tailWord_12215 prefixEnd_12215 5575258839799948850071 := by
  unfold tailWord_12215
  simp only [CollatzResearch.WordTrace]
  refine ⟨445517650754616001022099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 297011767169744000681399 445517650754616001022099)
  ·
    refine ⟨668276476131924001533149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445517650754616001022099 668276476131924001533149)
    ·
      refine ⟨250603678549471500574931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 668276476131924001533149 250603678549471500574931)
      ·
        refine ⟨375905517824207250862397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250603678549471500574931 375905517824207250862397)
        ·
          refine ⟨140964569184077719073399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375905517824207250862397 140964569184077719073399)
          ·
            refine ⟨211446853776116578610099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140964569184077719073399 211446853776116578610099)
            ·
              refine ⟨317170280664174867915149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211446853776116578610099 317170280664174867915149)
              ·
                refine ⟨118938855249065575468181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317170280664174867915149 118938855249065575468181)
                ·
                  refine ⟨5575258839799948850071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118938855249065575468181 5575258839799948850071)
                  ·
                    rfl

theorem cell20_12215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_12215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12215 prefixEnd_12215 := by exact prefixLift 12215
  have htrace : WordTrace (prefixWord ++ tailWord_12215) baseStart_12215 baseEnd_12215 := by
    simpa [prefixWord, tailWord_12215, baseEnd_12215] using wordTrace_append hprefix tailTrace_12215
  have hstable : (prefixWord ++ tailWord_12215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12215).length < 2 ^ (prefixWord ++ tailWord_12215).sum := by decide
  have hdescent : baseEnd_12215 < baseStart_12215 := by decide
  rcases family_descends (prefixWord ++ tailWord_12215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12245 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 2]
def baseStart_12245 : Nat := 118140960795 + 12245 * 2 ^ 59
def prefixEnd_12245 : Nat := 4983230072969 + 3 ^ 40 * 12245 * 2
def baseEnd_12245 : Nat := 5588951657253177849949

theorem tailTrace_12245 : CollatzResearch.WordTrace tailWord_12245 prefixEnd_12245 5588951657253177849949 := by
  unfold tailWord_12245
  simp only [CollatzResearch.WordTrace]
  refine ⟨446611840645931124614189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 297741227097287416409459 446611840645931124614189)
  ·
    refine ⟨167479440242224171730321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 446611840645931124614189 167479440242224171730321)
    ·
      refine ⟨125609580181668128797741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167479440242224171730321 125609580181668128797741)
      ·
        refine ⟨47103592568125548299153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125609580181668128797741 47103592568125548299153)
        ·
          refine ⟨35327694426094161224365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47103592568125548299153 35327694426094161224365)
          ·
            refine ⟨13247885409785310459137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35327694426094161224365 13247885409785310459137)
            ·
              refine ⟨9935914057338982844353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13247885409785310459137 9935914057338982844353)
              ·
                refine ⟨7451935543004237133265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9935914057338982844353 7451935543004237133265)
                ·
                  refine ⟨5588951657253177849949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7451935543004237133265 5588951657253177849949)
                  ·
                    rfl

theorem cell20_12245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_12245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12245 prefixEnd_12245 := by exact prefixLift 12245
  have htrace : WordTrace (prefixWord ++ tailWord_12245) baseStart_12245 baseEnd_12245 := by
    simpa [prefixWord, tailWord_12245, baseEnd_12245] using wordTrace_append hprefix tailTrace_12245
  have hstable : (prefixWord ++ tailWord_12245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12245).length < 2 ^ (prefixWord ++ tailWord_12245).sum := by decide
  have hdescent : baseEnd_12245 < baseStart_12245 := by decide
  rcases family_descends (prefixWord ++ tailWord_12245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12270 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_12270 : Nat := 118140960795 + 12270 * 2 ^ 59
def prefixEnd_12270 : Nat := 4983230072969 + 3 ^ 40 * 12270 * 2
def baseEnd_12270 : Nat := 5600362338464202016513

theorem tailTrace_12270 : CollatzResearch.WordTrace tailWord_12270 prefixEnd_12270 5600362338464202016513 := by
  unfold tailWord_12270
  simp only [CollatzResearch.WordTrace]
  refine ⟨55940458194420049284283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 298349110370240262849509 55940458194420049284283)
  ·
    refine ⟨83910687291630073926425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55940458194420049284283 83910687291630073926425)
    ·
      refine ⟨62933015468722555444819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83910687291630073926425 62933015468722555444819)
      ·
        refine ⟨94399523203083833167229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62933015468722555444819 94399523203083833167229)
        ·
          refine ⟨35399821201156437437711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94399523203083833167229 35399821201156437437711)
          ·
            refine ⟨53099731801734656156567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35399821201156437437711 53099731801734656156567)
            ·
              refine ⟨79649597702601984234851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53099731801734656156567 79649597702601984234851)
              ·
                refine ⟨119474396553902976352277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79649597702601984234851 119474396553902976352277)
                ·
                  refine ⟨5600362338464202016513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119474396553902976352277 5600362338464202016513)
                  ·
                    rfl

theorem cell20_12270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_12270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12270 prefixEnd_12270 := by exact prefixLift 12270
  have htrace : WordTrace (prefixWord ++ tailWord_12270) baseStart_12270 baseEnd_12270 := by
    simpa [prefixWord, tailWord_12270, baseEnd_12270] using wordTrace_append hprefix tailTrace_12270
  have hstable : (prefixWord ++ tailWord_12270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12270).length < 2 ^ (prefixWord ++ tailWord_12270).sum := by decide
  have hdescent : baseEnd_12270 < baseStart_12270 := by decide
  rcases family_descends (prefixWord ++ tailWord_12270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12284 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_12284 : Nat := 118140960795 + 12284 * 2 ^ 59
def prefixEnd_12284 : Nat := 4983230072969 + 3 ^ 40 * 12284 * 2
def baseEnd_12284 : Nat := 5606752319942375549789

theorem tailTrace_12284 : CollatzResearch.WordTrace tailWord_12284 prefixEnd_12284 5606752319942375549789 := by
  unfold tailWord_12284
  simp only [CollatzResearch.WordTrace]
  refine ⟨224017143752320392641953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 298689525003093856855937 224017143752320392641953)
  ·
    refine ⟨168012857814240294481465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224017143752320392641953 168012857814240294481465)
    ·
      refine ⟨126009643360680220861099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168012857814240294481465 126009643360680220861099)
      ·
        refine ⟨189014465041020331291649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126009643360680220861099 189014465041020331291649)
        ·
          refine ⟨141760848780765248468737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189014465041020331291649 141760848780765248468737)
          ·
            refine ⟨106320636585573936351553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141760848780765248468737 106320636585573936351553)
            ·
              refine ⟨79740477439180452263665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106320636585573936351553 79740477439180452263665)
              ·
                refine ⟨59805358079385339197749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79740477439180452263665 59805358079385339197749)
                ·
                  refine ⟨5606752319942375549789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59805358079385339197749 5606752319942375549789)
                  ·
                    rfl

theorem cell20_12284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_12284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12284 prefixEnd_12284 := by exact prefixLift 12284
  have htrace : WordTrace (prefixWord ++ tailWord_12284) baseStart_12284 baseEnd_12284 := by
    simpa [prefixWord, tailWord_12284, baseEnd_12284] using wordTrace_append hprefix tailTrace_12284
  have hstable : (prefixWord ++ tailWord_12284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12284).length < 2 ^ (prefixWord ++ tailWord_12284).sum := by decide
  have hdescent : baseEnd_12284 < baseStart_12284 := by decide
  rcases family_descends (prefixWord ++ tailWord_12284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12328 : List Nat := [2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_12328 : Nat := 118140960795 + 12328 * 2 ^ 59
def prefixEnd_12328 : Nat := 4983230072969 + 3 ^ 40 * 12328 * 2
def baseEnd_12328 : Nat := 1875611706291259360981

theorem tailTrace_12328 : CollatzResearch.WordTrace tailWord_12328 prefixEnd_12328 1875611706291259360981 := by
  unfold tailWord_12328
  simp only [CollatzResearch.WordTrace]
  refine ⟨224819549672618149942819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 299759399563490866590425 224819549672618149942819)
  ·
    refine ⟨337229324508927224914229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224819549672618149942819 337229324508927224914229)
    ·
      refine ⟨31615249172711927335709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 337229324508927224914229 31615249172711927335709)
      ·
        refine ⟨11855718439766972750891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31615249172711927335709 11855718439766972750891)
        ·
          refine ⟨17783577659650459126337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11855718439766972750891 17783577659650459126337)
          ·
            refine ⟨13337683244737844344753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17783577659650459126337 13337683244737844344753)
            ·
              refine ⟨10003262433553383258565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13337683244737844344753 10003262433553383258565)
              ·
                refine ⟨1875611706291259360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10003262433553383258565 1875611706291259360981)
                ·
                  rfl

theorem cell20_12328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_12328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12328 prefixEnd_12328 := by exact prefixLift 12328
  have htrace : WordTrace (prefixWord ++ tailWord_12328) baseStart_12328 baseEnd_12328 := by
    simpa [prefixWord, tailWord_12328, baseEnd_12328] using wordTrace_append hprefix tailTrace_12328
  have hstable : (prefixWord ++ tailWord_12328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12328).length < 2 ^ (prefixWord ++ tailWord_12328).sum := by decide
  have hdescent : baseEnd_12328 < baseStart_12328 := by decide
  rcases family_descends (prefixWord ++ tailWord_12328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12353 : List Nat := [1, 2, 5, 1, 2, 1, 8]
def baseStart_12353 : Nat := 118140960795 + 12353 * 2 ^ 59
def prefixEnd_12353 : Nat := 4983230072969 + 3 ^ 40 * 12353 * 2
def baseEnd_12353 : Nat := 626471755564978027723

theorem tailTrace_12353 : CollatzResearch.WordTrace tailWord_12353 prefixEnd_12353 626471755564978027723 := by
  unfold tailWord_12353
  simp only [CollatzResearch.WordTrace]
  refine ⟨450550924254665569545713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 300367282836443713030475 450550924254665569545713)
  ·
    refine ⟨337913193190999177159285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 450550924254665569545713 337913193190999177159285)
    ·
      refine ⟨31679361861656172858683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 337913193190999177159285 31679361861656172858683)
      ·
        refine ⟨47519042792484259288025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31679361861656172858683 47519042792484259288025)
        ·
          refine ⟨35639282094363194466019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47519042792484259288025 35639282094363194466019)
          ·
            refine ⟨53458923141544791699029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35639282094363194466019 53458923141544791699029)
            ·
              refine ⟨626471755564978027723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 53458923141544791699029 626471755564978027723)
              ·
                rfl

theorem cell20_12353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_12353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12353 prefixEnd_12353 := by exact prefixLift 12353
  have htrace : WordTrace (prefixWord ++ tailWord_12353) baseStart_12353 baseEnd_12353 := by
    simpa [prefixWord, tailWord_12353, baseEnd_12353] using wordTrace_append hprefix tailTrace_12353
  have hstable : (prefixWord ++ tailWord_12353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12353).length < 2 ^ (prefixWord ++ tailWord_12353).sum := by decide
  have hdescent : baseEnd_12353 < baseStart_12353 := by decide
  rcases family_descends (prefixWord ++ tailWord_12353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12370 : List Nat := [3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_12370 : Nat := 118140960795 + 12370 * 2 ^ 59
def prefixEnd_12370 : Nat := 4983230072969 + 3 ^ 40 * 12370 * 2
def baseEnd_12370 : Nat := 1882001687769432894257

theorem tailTrace_12370 : CollatzResearch.WordTrace tailWord_12370 prefixEnd_12370 1882001687769432894257 := by
  unfold tailWord_12370
  simp only [CollatzResearch.WordTrace]
  refine ⟨112792741298269368228641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 300780643462051648609709 112792741298269368228641)
  ·
    refine ⟨84594555973702026171481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112792741298269368228641 84594555973702026171481)
    ·
      refine ⟨63445916980276519628611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84594555973702026171481 63445916980276519628611)
      ·
        refine ⟨95168875470414779442917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63445916980276519628611 95168875470414779442917)
        ·
          refine ⟨17844164150702771145547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95168875470414779442917 17844164150702771145547)
          ·
            refine ⟨26766246226054156718321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17844164150702771145547 26766246226054156718321)
            ·
              refine ⟨20074684669540617538741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26766246226054156718321 20074684669540617538741)
              ·
                refine ⟨1882001687769432894257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20074684669540617538741 1882001687769432894257)
                ·
                  rfl

theorem cell20_12370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_12370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12370 prefixEnd_12370 := by exact prefixLift 12370
  have htrace : WordTrace (prefixWord ++ tailWord_12370) baseStart_12370 baseEnd_12370 := by
    simpa [prefixWord, tailWord_12370, baseEnd_12370] using wordTrace_append hprefix tailTrace_12370
  have hstable : (prefixWord ++ tailWord_12370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12370).length < 2 ^ (prefixWord ++ tailWord_12370).sum := by decide
  have hdescent : baseEnd_12370 < baseStart_12370 := by decide
  rcases family_descends (prefixWord ++ tailWord_12370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12412 : List Nat := [2, 2, 2, 1, 1, 12]
def baseStart_12412 : Nat := 118140960795 + 12412 * 2 ^ 59
def prefixEnd_12412 : Nat := 4983230072969 + 3 ^ 40 * 12412 * 2
def baseEnd_12412 : Nat := 209821296583067380837

theorem tailTrace_12412 : CollatzResearch.WordTrace tailWord_12412 prefixEnd_12412 209821296583067380837 := by
  unfold tailWord_12412
  simp only [CollatzResearch.WordTrace]
  refine ⟨226351415520459322971745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 301801887360612430628993 226351415520459322971745)
  ·
    refine ⟨169763561640344492228809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226351415520459322971745 169763561640344492228809)
    ·
      refine ⟨127322671230258369171607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169763561640344492228809 127322671230258369171607)
      ·
        refine ⟨190984006845387553757411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127322671230258369171607 190984006845387553757411)
        ·
          refine ⟨286476010268081330636117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190984006845387553757411 286476010268081330636117)
          ·
            refine ⟨209821296583067380837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 286476010268081330636117 209821296583067380837)
            ·
              rfl

theorem cell20_12412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 12].length) (baseStart_12412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12412 prefixEnd_12412 := by exact prefixLift 12412
  have htrace : WordTrace (prefixWord ++ tailWord_12412) baseStart_12412 baseEnd_12412 := by
    simpa [prefixWord, tailWord_12412, baseEnd_12412] using wordTrace_append hprefix tailTrace_12412
  have hstable : (prefixWord ++ tailWord_12412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12412).length < 2 ^ (prefixWord ++ tailWord_12412).sum := by decide
  have hdescent : baseEnd_12412 < baseStart_12412 := by decide
  rcases family_descends (prefixWord ++ tailWord_12412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12438 : List Nat := [5, 3, 2, 1, 1, 1, 3, 4]
def baseStart_12438 : Nat := 118140960795 + 12438 * 2 ^ 59
def prefixEnd_12438 : Nat := 4983230072969 + 3 ^ 40 * 12438 * 2
def baseEnd_12438 : Nat := 1892347372067428138609

theorem tailTrace_12438 : CollatzResearch.WordTrace tailWord_12438 prefixEnd_12438 1892347372067428138609 := by
  unfold tailWord_12438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353195559170317899373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 302434085964483390926645 28353195559170317899373)
  ·
    refine ⟨10632448334688869212265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28353195559170317899373 10632448334688869212265)
    ·
      refine ⟨7974336251016651909199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10632448334688869212265 7974336251016651909199)
      ·
        refine ⟨11961504376524977863799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974336251016651909199 11961504376524977863799)
        ·
          refine ⟨17942256564787466795699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961504376524977863799 17942256564787466795699)
          ·
            refine ⟨26913384847181200193549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17942256564787466795699 26913384847181200193549)
            ·
              refine ⟨10092519317692950072581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26913384847181200193549 10092519317692950072581)
              ·
                refine ⟨1892347372067428138609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10092519317692950072581 1892347372067428138609)
                ·
                  rfl

theorem cell20_12438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_12438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12438 prefixEnd_12438 := by exact prefixLift 12438
  have htrace : WordTrace (prefixWord ++ tailWord_12438) baseStart_12438 baseEnd_12438 := by
    simpa [prefixWord, tailWord_12438, baseEnd_12438] using wordTrace_append hprefix tailTrace_12438
  have hstable : (prefixWord ++ tailWord_12438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12438).length < 2 ^ (prefixWord ++ tailWord_12438).sum := by decide
  have hdescent : baseEnd_12438 < baseStart_12438 := by decide
  rcases family_descends (prefixWord ++ tailWord_12438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12488 : List Nat := [2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_12488 : Nat := 118140960795 + 12488 * 2 ^ 59
def prefixEnd_12488 : Nat := 4983230072969 + 3 ^ 40 * 12488 * 2
def baseEnd_12488 : Nat := 1899954492874777582985

theorem tailTrace_12488 : CollatzResearch.WordTrace tailWord_12488 prefixEnd_12488 1899954492874777582985 := by
  unfold tailWord_12488
  simp only [CollatzResearch.WordTrace]
  refine ⟨227737389382791812855059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 303649852510389083806745 227737389382791812855059)
  ·
    refine ⟨341606084074187719282589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227737389382791812855059 341606084074187719282589)
    ·
      refine ⟨128102281527820394730971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341606084074187719282589 128102281527820394730971)
      ·
        refine ⟨192153422291730592096457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128102281527820394730971 192153422291730592096457)
        ·
          refine ⟨144115066718797944072343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192153422291730592096457 144115066718797944072343)
          ·
            refine ⟨216172600078196916108515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144115066718797944072343 216172600078196916108515)
            ·
              refine ⟨324258900117295374162773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216172600078196916108515 324258900117295374162773)
              ·
                refine ⟨1899954492874777582985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 324258900117295374162773 1899954492874777582985)
                ·
                  rfl

theorem cell20_12488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_12488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12488 prefixEnd_12488 := by exact prefixLift 12488
  have htrace : WordTrace (prefixWord ++ tailWord_12488) baseStart_12488 baseEnd_12488 := by
    simpa [prefixWord, tailWord_12488, baseEnd_12488] using wordTrace_append hprefix tailTrace_12488
  have hstable : (prefixWord ++ tailWord_12488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12488).length < 2 ^ (prefixWord ++ tailWord_12488).sum := by decide
  have hdescent : baseEnd_12488 < baseStart_12488 := by decide
  rcases family_descends (prefixWord ++ tailWord_12488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12491 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 3]
def baseStart_12491 : Nat := 118140960795 + 12491 * 2 ^ 59
def prefixEnd_12491 : Nat := 4983230072969 + 3 ^ 40 * 12491 * 2
def baseEnd_12491 : Nat := 5701232760369655648943

theorem tailTrace_12491 : CollatzResearch.WordTrace tailWord_12491 prefixEnd_12491 5701232760369655648943 := by
  unfold tailWord_12491
  simp only [CollatzResearch.WordTrace]
  refine ⟨455584197754715138069327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 303722798503143425379551 455584197754715138069327)
  ·
    refine ⟨683376296632072707103991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455584197754715138069327 683376296632072707103991)
    ·
      refine ⟨1025064444948109060655987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683376296632072707103991 1025064444948109060655987)
      ·
        refine ⟨1537596667422163590983981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025064444948109060655987 1537596667422163590983981)
        ·
          refine ⟨576598750283311346618993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1537596667422163590983981 576598750283311346618993)
          ·
            refine ⟨432449062712483509964245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576598750283311346618993 432449062712483509964245)
            ·
              refine ⟨10135524907323832264787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 432449062712483509964245 10135524907323832264787)
              ·
                refine ⟨15203287360985748397181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135524907323832264787 15203287360985748397181)
                ·
                  refine ⟨5701232760369655648943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15203287360985748397181 5701232760369655648943)
                  ·
                    rfl

theorem cell20_12491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_12491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12491 prefixEnd_12491 := by exact prefixLift 12491
  have htrace : WordTrace (prefixWord ++ tailWord_12491) baseStart_12491 baseEnd_12491 := by
    simpa [prefixWord, tailWord_12491, baseEnd_12491] using wordTrace_append hprefix tailTrace_12491
  have hstable : (prefixWord ++ tailWord_12491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12491).length < 2 ^ (prefixWord ++ tailWord_12491).sum := by decide
  have hdescent : baseEnd_12491 < baseStart_12491 := by decide
  rcases family_descends (prefixWord ++ tailWord_12491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12498 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_12498 : Nat := 118140960795 + 12498 * 2 ^ 59
def prefixEnd_12498 : Nat := 4983230072969 + 3 ^ 40 * 12498 * 2
def baseEnd_12498 : Nat := 5704427751108742415581

theorem tailTrace_12498 : CollatzResearch.WordTrace tailWord_12498 prefixEnd_12498 5704427751108742415581 := by
  unfold tailWord_12498
  simp only [CollatzResearch.WordTrace]
  refine ⟨113959877182338833393537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 303893005819570222382765 113959877182338833393537)
  ·
    refine ⟨85469907886754125045153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113959877182338833393537 85469907886754125045153)
    ·
      refine ⟨64102430915065593783865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85469907886754125045153 64102430915065593783865)
      ·
        refine ⟨48076823186299195337899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64102430915065593783865 48076823186299195337899)
        ·
          refine ⟨72115234779448793006849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48076823186299195337899 72115234779448793006849)
          ·
            refine ⟨54086426084586594755137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72115234779448793006849 54086426084586594755137)
            ·
              refine ⟨40564819563439946066353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54086426084586594755137 40564819563439946066353)
              ·
                refine ⟨30423614672579959549765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40564819563439946066353 30423614672579959549765)
                ·
                  refine ⟨5704427751108742415581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30423614672579959549765 5704427751108742415581)
                  ·
                    rfl

theorem cell20_12498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_12498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12498 prefixEnd_12498 := by exact prefixLift 12498
  have htrace : WordTrace (prefixWord ++ tailWord_12498) baseStart_12498 baseEnd_12498 := by
    simpa [prefixWord, tailWord_12498, baseEnd_12498] using wordTrace_append hprefix tailTrace_12498
  have hstable : (prefixWord ++ tailWord_12498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12498).length < 2 ^ (prefixWord ++ tailWord_12498).sum := by decide
  have hdescent : baseEnd_12498 < baseStart_12498 := by decide
  rcases family_descends (prefixWord ++ tailWord_12498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12501 : List Nat := [1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_12501 : Nat := 118140960795 + 12501 * 2 ^ 59
def prefixEnd_12501 : Nat := 4983230072969 + 3 ^ 40 * 12501 * 2
def baseEnd_12501 : Nat := 1901932344284688438523

theorem tailTrace_12501 : CollatzResearch.WordTrace tailWord_12501 prefixEnd_12501 1901932344284688438523 := by
  unfold tailWord_12501
  simp only [CollatzResearch.WordTrace]
  refine ⟨455948927718486845933357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 303965951812324563955571 455948927718486845933357)
  ·
    refine ⟨170980847894432567225009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 455948927718486845933357 170980847894432567225009)
    ·
      refine ⟨128235635920824425418757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170980847894432567225009 128235635920824425418757)
      ·
        refine ⟨24044181735154579766017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128235635920824425418757 24044181735154579766017)
        ·
          refine ⟨18033136301365934824513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24044181735154579766017 18033136301365934824513)
          ·
            refine ⟨13524852226024451118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18033136301365934824513 13524852226024451118385)
            ·
              refine ⟨10143639169518338338789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13524852226024451118385 10143639169518338338789)
              ·
                refine ⟨1901932344284688438523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10143639169518338338789 1901932344284688438523)
                ·
                  rfl

theorem cell20_12501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_12501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12501 prefixEnd_12501 := by exact prefixLift 12501
  have htrace : WordTrace (prefixWord ++ tailWord_12501) baseStart_12501 baseEnd_12501 := by
    simpa [prefixWord, tailWord_12501, baseEnd_12501] using wordTrace_append hprefix tailTrace_12501
  have hstable : (prefixWord ++ tailWord_12501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12501).length < 2 ^ (prefixWord ++ tailWord_12501).sum := by decide
  have hdescent : baseEnd_12501 < baseStart_12501 := by decide
  rcases family_descends (prefixWord ++ tailWord_12501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12505 : List Nat := [1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_12505 : Nat := 118140960795 + 12505 * 2 ^ 59
def prefixEnd_12505 : Nat := 4983230072969 + 3 ^ 40 * 12505 * 2
def baseEnd_12505 : Nat := 1902540913949276394073

theorem tailTrace_12505 : CollatzResearch.WordTrace tailWord_12505 prefixEnd_12505 1902540913949276394073 := by
  unfold tailWord_12505
  simp only [CollatzResearch.WordTrace]
  refine ⟨456094819703995529078969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 304063213135997019385979 456094819703995529078969)
  ·
    refine ⟨342071114777996646809227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 456094819703995529078969 342071114777996646809227)
    ·
      refine ⟨513106672166994970213841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342071114777996646809227 513106672166994970213841)
      ·
        refine ⟨384830004125246227660381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513106672166994970213841 384830004125246227660381)
        ·
          refine ⟨144311251546967335372643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384830004125246227660381 144311251546967335372643)
          ·
            refine ⟨216466877320451003058965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144311251546967335372643 216466877320451003058965)
            ·
              refine ⟨10146884874396140768389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216466877320451003058965 10146884874396140768389)
              ·
                refine ⟨1902540913949276394073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10146884874396140768389 1902540913949276394073)
                ·
                  rfl

theorem cell20_12505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_12505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12505 prefixEnd_12505 := by exact prefixLift 12505
  have htrace : WordTrace (prefixWord ++ tailWord_12505) baseStart_12505 baseEnd_12505 := by
    simpa [prefixWord, tailWord_12505, baseEnd_12505] using wordTrace_append hprefix tailTrace_12505
  have hstable : (prefixWord ++ tailWord_12505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12505).length < 2 ^ (prefixWord ++ tailWord_12505).sum := by decide
  have hdescent : baseEnd_12505 < baseStart_12505 := by decide
  rcases family_descends (prefixWord ++ tailWord_12505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12536 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_12536 : Nat := 118140960795 + 12536 * 2 ^ 59
def prefixEnd_12536 : Nat := 4983230072969 + 3 ^ 40 * 12536 * 2
def baseEnd_12536 : Nat := 5721771986549499148759

theorem tailTrace_12536 : CollatzResearch.WordTrace tailWord_12536 prefixEnd_12536 5721771986549499148759 := by
  unfold tailWord_12536
  simp only [CollatzResearch.WordTrace]
  refine ⟨228612741295843911728731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 304816988394458548971641 228612741295843911728731)
  ·
    refine ⟨342919111943765867593097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228612741295843911728731 342919111943765867593097)
    ·
      refine ⟨257189333957824400694823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342919111943765867593097 257189333957824400694823)
      ·
        refine ⟨385784000936736601042235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257189333957824400694823 385784000936736601042235)
        ·
          refine ⟨578676001405104901563353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385784000936736601042235 578676001405104901563353)
          ·
            refine ⟨434007001053828676172515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578676001405104901563353 434007001053828676172515)
            ·
              refine ⟨651010501580743014258773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434007001053828676172515 651010501580743014258773)
              ·
                refine ⟨7629029315399332198345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 651010501580743014258773 7629029315399332198345)
                ·
                  refine ⟨5721771986549499148759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629029315399332198345 5721771986549499148759)
                  ·
                    rfl

theorem cell20_12536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_12536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12536 prefixEnd_12536 := by exact prefixLift 12536
  have htrace : WordTrace (prefixWord ++ tailWord_12536) baseStart_12536 baseEnd_12536 := by
    simpa [prefixWord, tailWord_12536, baseEnd_12536] using wordTrace_append hprefix tailTrace_12536
  have hstable : (prefixWord ++ tailWord_12536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12536).length < 2 ^ (prefixWord ++ tailWord_12536).sum := by decide
  have hdescent : baseEnd_12536 < baseStart_12536 := by decide
  rcases family_descends (prefixWord ++ tailWord_12536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12546 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_12546 : Nat := 118140960795 + 12546 * 2 ^ 59
def prefixEnd_12546 : Nat := 4983230072969 + 3 ^ 40 * 12546 * 2
def baseEnd_12546 : Nat := 5726336259033908815385

theorem tailTrace_12546 : CollatzResearch.WordTrace tailWord_12546 prefixEnd_12546 5726336259033908815385 := by
  unfold tailWord_12546
  simp only [CollatzResearch.WordTrace]
  refine ⟨114397553138864882830373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 305060141703639687547661 114397553138864882830373)
  ·
    refine ⟨21449541213537165530695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114397553138864882830373 21449541213537165530695)
    ·
      refine ⟨32174311820305748296043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21449541213537165530695 32174311820305748296043)
      ·
        refine ⟨48261467730458622444065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32174311820305748296043 48261467730458622444065)
        ·
          refine ⟨36196100797843966833049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48261467730458622444065 36196100797843966833049)
          ·
            refine ⟨27147075598382975124787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36196100797843966833049 27147075598382975124787)
            ·
              refine ⟨40720613397574462687181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27147075598382975124787 40720613397574462687181)
              ·
                refine ⟨15270230024090423507693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40720613397574462687181 15270230024090423507693)
                ·
                  refine ⟨5726336259033908815385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15270230024090423507693 5726336259033908815385)
                  ·
                    rfl

theorem cell20_12546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_12546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12546 prefixEnd_12546 := by exact prefixLift 12546
  have htrace : WordTrace (prefixWord ++ tailWord_12546) baseStart_12546 baseEnd_12546 := by
    simpa [prefixWord, tailWord_12546, baseEnd_12546] using wordTrace_append hprefix tailTrace_12546
  have hstable : (prefixWord ++ tailWord_12546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12546).length < 2 ^ (prefixWord ++ tailWord_12546).sum := by decide
  have hdescent : baseEnd_12546 < baseStart_12546 := by decide
  rcases family_descends (prefixWord ++ tailWord_12546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12571 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_12571 : Nat := 118140960795 + 12571 * 2 ^ 59
def prefixEnd_12571 : Nat := 4983230072969 + 3 ^ 40 * 12571 * 2
def baseEnd_12571 : Nat := 5737746940244932981949

theorem tailTrace_12571 : CollatzResearch.WordTrace tailWord_12571 prefixEnd_12571 5737746940244932981949 := by
  unfold tailWord_12571
  simp only [CollatzResearch.WordTrace]
  refine ⟨458502037464888800981567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 305668024976592533987711 458502037464888800981567)
  ·
    refine ⟨687753056197333201472351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458502037464888800981567 687753056197333201472351)
    ·
      refine ⟨1031629584295999802208527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687753056197333201472351 1031629584295999802208527)
      ·
        refine ⟨1547444376443999703312791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031629584295999802208527 1547444376443999703312791)
        ·
          refine ⟨2321166564665999554969187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547444376443999703312791 2321166564665999554969187)
          ·
            refine ⟨3481749846998999332453781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321166564665999554969187 3481749846998999332453781)
            ·
              refine ⟨163207024078078093708771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3481749846998999332453781 163207024078078093708771)
              ·
                refine ⟨244810536117117140563157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163207024078078093708771 244810536117117140563157)
                ·
                  refine ⟨5737746940244932981949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244810536117117140563157 5737746940244932981949)
                  ·
                    rfl

theorem cell20_12571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_12571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12571 prefixEnd_12571 := by exact prefixLift 12571
  have htrace : WordTrace (prefixWord ++ tailWord_12571) baseStart_12571 baseEnd_12571 := by
    simpa [prefixWord, tailWord_12571, baseEnd_12571] using wordTrace_append hprefix tailTrace_12571
  have hstable : (prefixWord ++ tailWord_12571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12571).length < 2 ^ (prefixWord ++ tailWord_12571).sum := by decide
  have hdescent : baseEnd_12571 < baseStart_12571 := by decide
  rcases family_descends (prefixWord ++ tailWord_12571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12581 : List Nat := [1, 3, 1, 2, 6, 7]
def baseStart_12581 : Nat := 118140960795 + 12581 * 2 ^ 59
def prefixEnd_12581 : Nat := 4983230072969 + 3 ^ 40 * 12581 * 2
def baseEnd_12581 : Nat := 212678193064049727725

theorem tailTrace_12581 : CollatzResearch.WordTrace tailWord_12581 prefixEnd_12581 212678193064049727725 := by
  unfold tailWord_12581
  simp only [CollatzResearch.WordTrace]
  refine ⟨458866767428660508845597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 305911178285773672563731 458866767428660508845597)
  ·
    refine ⟨172075037785747690817099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 458866767428660508845597 172075037785747690817099)
    ·
      refine ⟨258112556678621536225649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172075037785747690817099 258112556678621536225649)
      ·
        refine ⟨193584417508966152169237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258112556678621536225649 193584417508966152169237)
        ·
          refine ⟨9074269570732788382933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193584417508966152169237 9074269570732788382933)
          ·
            refine ⟨212678193064049727725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9074269570732788382933 212678193064049727725)
            ·
              rfl

theorem cell20_12581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 7].length) (baseStart_12581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12581 prefixEnd_12581 := by exact prefixLift 12581
  have htrace : WordTrace (prefixWord ++ tailWord_12581) baseStart_12581 baseEnd_12581 := by
    simpa [prefixWord, tailWord_12581, baseEnd_12581] using wordTrace_append hprefix tailTrace_12581
  have hstable : (prefixWord ++ tailWord_12581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12581).length < 2 ^ (prefixWord ++ tailWord_12581).sum := by decide
  have hdescent : baseEnd_12581 < baseStart_12581 := by decide
  rcases family_descends (prefixWord ++ tailWord_12581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12583 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 2]
def baseStart_12583 : Nat := 118140960795 + 12583 * 2 ^ 59
def prefixEnd_12583 : Nat := 4983230072969 + 3 ^ 40 * 12583 * 2
def baseEnd_12583 : Nat := 5743224067226224581901

theorem tailTrace_12583 : CollatzResearch.WordTrace tailWord_12583 prefixEnd_12583 5743224067226224581901 := by
  unfold tailWord_12583
  simp only [CollatzResearch.WordTrace]
  refine ⟨458939713421414850418403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 305959808947609900278935 458939713421414850418403)
  ·
    refine ⟨688409570132122275627605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458939713421414850418403 688409570132122275627605)
    ·
      refine ⟨8067299649985807917511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 688409570132122275627605 8067299649985807917511)
      ·
        refine ⟨12100949474978711876267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8067299649985807917511 12100949474978711876267)
        ·
          refine ⟨18151424212468067814401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100949474978711876267 18151424212468067814401)
          ·
            refine ⟨13613568159351050860801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18151424212468067814401 13613568159351050860801)
            ·
              refine ⟨10210176119513288145601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13613568159351050860801 10210176119513288145601)
              ·
                refine ⟨7657632089634966109201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10210176119513288145601 7657632089634966109201)
                ·
                  refine ⟨5743224067226224581901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657632089634966109201 5743224067226224581901)
                  ·
                    rfl

theorem cell20_12583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2].length) (baseStart_12583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12583 prefixEnd_12583 := by exact prefixLift 12583
  have htrace : WordTrace (prefixWord ++ tailWord_12583) baseStart_12583 baseEnd_12583 := by
    simpa [prefixWord, tailWord_12583, baseEnd_12583] using wordTrace_append hprefix tailTrace_12583
  have hstable : (prefixWord ++ tailWord_12583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12583).length < 2 ^ (prefixWord ++ tailWord_12583).sum := by decide
  have hdescent : baseEnd_12583 < baseStart_12583 := by decide
  rcases family_descends (prefixWord ++ tailWord_12583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12584 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_12584 : Nat := 118140960795 + 12584 * 2 ^ 59
def prefixEnd_12584 : Nat := 4983230072969 + 3 ^ 40 * 12584 * 2
def baseEnd_12584 : Nat := 5743680494474665548563

theorem tailTrace_12584 : CollatzResearch.WordTrace tailWord_12584 prefixEnd_12584 5743680494474665548563 := by
  unfold tailWord_12584
  simp only [CollatzResearch.WordTrace]
  refine ⟨229488093208896010602403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 305984124278528014136537 229488093208896010602403)
  ·
    refine ⟨344232139813344015903605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229488093208896010602403 344232139813344015903605)
    ·
      refine ⟨32271763107501001490963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 344232139813344015903605 32271763107501001490963)
      ·
        refine ⟨48407644661251502236445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32271763107501001490963 48407644661251502236445)
        ·
          refine ⟨18152866747969313338667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48407644661251502236445 18152866747969313338667)
          ·
            refine ⟨27229300121953970008001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152866747969313338667 27229300121953970008001)
            ·
              refine ⟨20421975091465477506001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27229300121953970008001 20421975091465477506001)
              ·
                refine ⟨15316481318599108129501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20421975091465477506001 15316481318599108129501)
                ·
                  refine ⟨5743680494474665548563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15316481318599108129501 5743680494474665548563)
                  ·
                    rfl

theorem cell20_12584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_12584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12584 prefixEnd_12584 := by exact prefixLift 12584
  have htrace : WordTrace (prefixWord ++ tailWord_12584) baseStart_12584 baseEnd_12584 := by
    simpa [prefixWord, tailWord_12584, baseEnd_12584] using wordTrace_append hprefix tailTrace_12584
  have hstable : (prefixWord ++ tailWord_12584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12584).length < 2 ^ (prefixWord ++ tailWord_12584).sum := by decide
  have hdescent : baseEnd_12584 < baseStart_12584 := by decide
  rcases family_descends (prefixWord ++ tailWord_12584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12588 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_12588 : Nat := 118140960795 + 12588 * 2 ^ 59
def prefixEnd_12588 : Nat := 4983230072969 + 3 ^ 40 * 12588 * 2
def baseEnd_12588 : Nat := 5745506203468429415213

theorem tailTrace_12588 : CollatzResearch.WordTrace tailWord_12588 prefixEnd_12588 5745506203468429415213 := by
  unfold tailWord_12588
  simp only [CollatzResearch.WordTrace]
  refine ⟨229561039201650352175209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 306081385602200469566945 229561039201650352175209)
  ·
    refine ⟨172170779401237764131407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229561039201650352175209 172170779401237764131407)
    ·
      refine ⟨258256169101856646197111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172170779401237764131407 258256169101856646197111)
      ·
        refine ⟨387384253652784969295667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258256169101856646197111 387384253652784969295667)
        ·
          refine ⟨581076380479177453943501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387384253652784969295667 581076380479177453943501)
          ·
            refine ⟨217903642679691545228813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581076380479177453943501 217903642679691545228813)
            ·
              refine ⟨81713866004884329460805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217903642679691545228813 81713866004884329460805)
              ·
                refine ⟨15321349875915811773901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81713866004884329460805 15321349875915811773901)
                ·
                  refine ⟨5745506203468429415213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15321349875915811773901 5745506203468429415213)
                  ·
                    rfl

theorem cell20_12588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_12588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12588 prefixEnd_12588 := by exact prefixLift 12588
  have htrace : WordTrace (prefixWord ++ tailWord_12588) baseStart_12588 baseEnd_12588 := by
    simpa [prefixWord, tailWord_12588, baseEnd_12588] using wordTrace_append hprefix tailTrace_12588
  have hstable : (prefixWord ++ tailWord_12588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12588).length < 2 ^ (prefixWord ++ tailWord_12588).sum := by decide
  have hdescent : baseEnd_12588 < baseStart_12588 := by decide
  rcases family_descends (prefixWord ++ tailWord_12588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12591 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 2]
def baseStart_12591 : Nat := 118140960795 + 12591 * 2 ^ 59
def prefixEnd_12591 : Nat := 4983230072969 + 3 ^ 40 * 12591 * 2
def baseEnd_12591 : Nat := 5746875485213752315201

theorem tailTrace_12591 : CollatzResearch.WordTrace tailWord_12591 prefixEnd_12591 5746875485213752315201 := by
  unfold tailWord_12591
  simp only [CollatzResearch.WordTrace]
  refine ⟨459231497392432216709627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 306154331594954811139751 459231497392432216709627)
  ·
    refine ⟨688847246088648325064441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459231497392432216709627 688847246088648325064441)
    ·
      refine ⟨516635434566486243798331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 688847246088648325064441 516635434566486243798331)
      ·
        refine ⟨774953151849729365697497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516635434566486243798331 774953151849729365697497)
        ·
          refine ⟨581214863887297024273123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774953151849729365697497 581214863887297024273123)
          ·
            refine ⟨871822295830945536409685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581214863887297024273123 871822295830945536409685)
            ·
              refine ⟨10216667529268893004801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 871822295830945536409685 10216667529268893004801)
              ·
                refine ⟨7662500646951669753601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10216667529268893004801 7662500646951669753601)
                ·
                  refine ⟨5746875485213752315201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7662500646951669753601 5746875485213752315201)
                  ·
                    rfl

theorem cell20_12591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2].length) (baseStart_12591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12591 prefixEnd_12591 := by exact prefixLift 12591
  have htrace : WordTrace (prefixWord ++ tailWord_12591) baseStart_12591 baseEnd_12591 := by
    simpa [prefixWord, tailWord_12591, baseEnd_12591] using wordTrace_append hprefix tailTrace_12591
  have hstable : (prefixWord ++ tailWord_12591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12591).length < 2 ^ (prefixWord ++ tailWord_12591).sum := by decide
  have hdescent : baseEnd_12591 < baseStart_12591 := by decide
  rcases family_descends (prefixWord ++ tailWord_12591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12595 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_12595 : Nat := 118140960795 + 12595 * 2 ^ 59
def prefixEnd_12595 : Nat := 4983230072969 + 3 ^ 40 * 12595 * 2
def baseEnd_12595 : Nat := 5748701194207516181851

theorem tailTrace_12595 : CollatzResearch.WordTrace tailWord_12595 prefixEnd_12595 5748701194207516181851 := by
  unfold tailWord_12595
  simp only [CollatzResearch.WordTrace]
  refine ⟨459377389377940899855239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 306251592918627266570159 459377389377940899855239)
  ·
    refine ⟨689066084066911349782859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459377389377940899855239 689066084066911349782859)
    ·
      refine ⟨1033599126100367024674289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689066084066911349782859 1033599126100367024674289)
      ·
        refine ⟨775199344575275268505717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033599126100367024674289 775199344575275268505717)
        ·
          refine ⟨72674938553932056422411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 775199344575275268505717 72674938553932056422411)
          ·
            refine ⟨109012407830898084633617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72674938553932056422411 109012407830898084633617)
            ·
              refine ⟨81759305873173563475213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109012407830898084633617 81759305873173563475213)
              ·
                refine ⟨30659739702440086303205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81759305873173563475213 30659739702440086303205)
                ·
                  refine ⟨5748701194207516181851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30659739702440086303205 5748701194207516181851)
                  ·
                    rfl

theorem cell20_12595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_12595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12595 prefixEnd_12595 := by exact prefixLift 12595
  have htrace : WordTrace (prefixWord ++ tailWord_12595) baseStart_12595 baseEnd_12595 := by
    simpa [prefixWord, tailWord_12595, baseEnd_12595] using wordTrace_append hprefix tailTrace_12595
  have hstable : (prefixWord ++ tailWord_12595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12595).length < 2 ^ (prefixWord ++ tailWord_12595).sum := by decide
  have hdescent : baseEnd_12595 < baseStart_12595 := by decide
  rcases family_descends (prefixWord ++ tailWord_12595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12636 : List Nat := [2, 2, 4, 3, 1, 1, 7]
def baseStart_12636 : Nat := 118140960795 + 12636 * 2 ^ 59
def prefixEnd_12636 : Nat := 4983230072969 + 3 ^ 40 * 12636 * 2
def baseEnd_12636 : Nat := 640823856821510646113

theorem tailTrace_12636 : CollatzResearch.WordTrace tailWord_12636 prefixEnd_12636 640823856821510646113 := by
  unfold tailWord_12636
  simp only [CollatzResearch.WordTrace]
  refine ⟨230436391114702451048881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 307248521486269934731841 230436391114702451048881)
  ·
    refine ⟨172827293336026838286661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230436391114702451048881 172827293336026838286661)
    ·
      refine ⟨32405117500505032178749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172827293336026838286661 32405117500505032178749)
      ·
        refine ⟨12151919062689387067031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32405117500505032178749 12151919062689387067031)
        ·
          refine ⟨18227878594034080600547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12151919062689387067031 18227878594034080600547)
          ·
            refine ⟨27341817891051120900821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18227878594034080600547 27341817891051120900821)
            ·
              refine ⟨640823856821510646113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27341817891051120900821 640823856821510646113)
              ·
                rfl

theorem cell20_12636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_12636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12636 prefixEnd_12636 := by exact prefixLift 12636
  have htrace : WordTrace (prefixWord ++ tailWord_12636) baseStart_12636 baseEnd_12636 := by
    simpa [prefixWord, tailWord_12636, baseEnd_12636] using wordTrace_append hprefix tailTrace_12636
  have hstable : (prefixWord ++ tailWord_12636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12636).length < 2 ^ (prefixWord ++ tailWord_12636).sum := by decide
  have hdescent : baseEnd_12636 < baseStart_12636 := by decide
  rcases family_descends (prefixWord ++ tailWord_12636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12650 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_12650 : Nat := 118140960795 + 12650 * 2 ^ 59
def prefixEnd_12650 : Nat := 4983230072969 + 3 ^ 40 * 12650 * 2
def baseEnd_12650 : Nat := 5773804692871769348293

theorem tailTrace_12650 : CollatzResearch.WordTrace tailWord_12650 prefixEnd_12650 5773804692871769348293 := by
  unfold tailWord_12650
  simp only [CollatzResearch.WordTrace]
  refine ⟨115345851044671323276851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 307588936119123528738269 115345851044671323276851)
  ·
    refine ⟨173018776567006984915277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115345851044671323276851 173018776567006984915277)
    ·
      refine ⟨64882041212627619343229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173018776567006984915277 64882041212627619343229)
      ·
        refine ⟨24330765454735357253711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64882041212627619343229 24330765454735357253711)
        ·
          refine ⟨36496148182103035880567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24330765454735357253711 36496148182103035880567)
          ·
            refine ⟨54744222273154553820851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36496148182103035880567 54744222273154553820851)
            ·
              refine ⟨82116333409731830731277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54744222273154553820851 82116333409731830731277)
              ·
                refine ⟨30793625028649436524229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82116333409731830731277 30793625028649436524229)
                ·
                  refine ⟨5773804692871769348293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30793625028649436524229 5773804692871769348293)
                  ·
                    rfl

theorem cell20_12650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_12650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12650 prefixEnd_12650 := by exact prefixLift 12650
  have htrace : WordTrace (prefixWord ++ tailWord_12650) baseStart_12650 baseEnd_12650 := by
    simpa [prefixWord, tailWord_12650, baseEnd_12650] using wordTrace_append hprefix tailTrace_12650
  have hstable : (prefixWord ++ tailWord_12650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12650).length < 2 ^ (prefixWord ++ tailWord_12650).sum := by decide
  have hdescent : baseEnd_12650 < baseStart_12650 := by decide
  rcases family_descends (prefixWord ++ tailWord_12650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12712 : List Nat := [2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_12712 : Nat := 118140960795 + 12712 * 2 ^ 59
def prefixEnd_12712 : Nat := 4983230072969 + 3 ^ 40 * 12712 * 2
def baseEnd_12712 : Nat := 1934034394091703093791

theorem tailTrace_12712 : CollatzResearch.WordTrace tailWord_12712 prefixEnd_12712 1934034394091703093791 := by
  unfold tailWord_12712
  simp only [CollatzResearch.WordTrace]
  refine ⟨231822364977034940932195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 309096486636046587909593 231822364977034940932195)
  ·
    refine ⟨347733547465552411398293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231822364977034940932195 347733547465552411398293)
    ·
      refine ⟨16300010037447769284295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 347733547465552411398293 16300010037447769284295)
      ·
        refine ⟨24450015056171653926443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16300010037447769284295 24450015056171653926443)
        ·
          refine ⟨36675022584257480889665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24450015056171653926443 36675022584257480889665)
          ·
            refine ⟨27506266938193110667249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36675022584257480889665 27506266938193110667249)
            ·
              refine ⟨20629700203644833000437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27506266938193110667249 20629700203644833000437)
              ·
                refine ⟨1934034394091703093791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20629700203644833000437 1934034394091703093791)
                ·
                  rfl

theorem cell20_12712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_12712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12712 prefixEnd_12712 := by exact prefixLift 12712
  have htrace : WordTrace (prefixWord ++ tailWord_12712) baseStart_12712 baseEnd_12712 := by
    simpa [prefixWord, tailWord_12712, baseEnd_12712] using wordTrace_append hprefix tailTrace_12712
  have hstable : (prefixWord ++ tailWord_12712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12712).length < 2 ^ (prefixWord ++ tailWord_12712).sum := by decide
  have hdescent : baseEnd_12712 < baseStart_12712 := by decide
  rcases family_descends (prefixWord ++ tailWord_12712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12757 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_12757 : Nat := 118140960795 + 12757 * 2 ^ 59
def prefixEnd_12757 : Nat := 4983230072969 + 3 ^ 40 * 12757 * 2
def baseEnd_12757 : Nat := 5822642408454952781189

theorem tailTrace_12757 : CollatzResearch.WordTrace tailWord_12757 prefixEnd_12757 5822642408454952781189 := by
  unfold tailWord_12757
  simp only [CollatzResearch.WordTrace]
  refine ⟨465286014791042567252525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 310190676527361711501683 465286014791042567252525)
  ·
    refine ⟨174482255546640962719697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 465286014791042567252525 174482255546640962719697)
    ·
      refine ⟨130861691659980722039773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174482255546640962719697 130861691659980722039773)
      ·
        refine ⟨49073134372492770764915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130861691659980722039773 49073134372492770764915)
        ·
          refine ⟨73609701558739156147373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49073134372492770764915 73609701558739156147373)
          ·
            refine ⟨27603638084527183555265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73609701558739156147373 27603638084527183555265)
            ·
              refine ⟨20702728563395387666449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27603638084527183555265 20702728563395387666449)
              ·
                refine ⟨15527046422546540749837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20702728563395387666449 15527046422546540749837)
                ·
                  refine ⟨5822642408454952781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15527046422546540749837 5822642408454952781189)
                  ·
                    rfl

theorem cell20_12757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_12757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12757 prefixEnd_12757 := by exact prefixLift 12757
  have htrace : WordTrace (prefixWord ++ tailWord_12757) baseStart_12757 baseEnd_12757 := by
    simpa [prefixWord, tailWord_12757, baseEnd_12757] using wordTrace_append hprefix tailTrace_12757
  have hstable : (prefixWord ++ tailWord_12757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12757).length < 2 ^ (prefixWord ++ tailWord_12757).sum := by decide
  have hdescent : baseEnd_12757 < baseStart_12757 := by decide
  rcases family_descends (prefixWord ++ tailWord_12757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12785 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_12785 : Nat := 118140960795 + 12785 * 2 ^ 59
def prefixEnd_12785 : Nat := 4983230072969 + 3 ^ 40 * 12785 * 2
def baseEnd_12785 : Nat := 5835422371411299847741

theorem tailTrace_12785 : CollatzResearch.WordTrace tailWord_12785 prefixEnd_12785 5835422371411299847741 := by
  unfold tailWord_12785
  simp only [CollatzResearch.WordTrace]
  refine ⟨466307258689603349271809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 310871505793068899514539 466307258689603349271809)
  ·
    refine ⟨349730444017202511953857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 466307258689603349271809 349730444017202511953857)
    ·
      refine ⟨262297833012901883965393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349730444017202511953857 262297833012901883965393)
      ·
        refine ⟨196723374759676412974045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262297833012901883965393 196723374759676412974045)
        ·
          refine ⟨73771265534878654865267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196723374759676412974045 73771265534878654865267)
          ·
            refine ⟨110656898302317982297901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73771265534878654865267 110656898302317982297901)
            ·
              refine ⟨41496336863369243361713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110656898302317982297901 41496336863369243361713)
              ·
                refine ⟨31122252647526932521285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41496336863369243361713 31122252647526932521285)
                ·
                  refine ⟨5835422371411299847741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31122252647526932521285 5835422371411299847741)
                  ·
                    rfl

theorem cell20_12785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_12785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12785 prefixEnd_12785 := by exact prefixLift 12785
  have htrace : WordTrace (prefixWord ++ tailWord_12785) baseStart_12785 baseEnd_12785 := by
    simpa [prefixWord, tailWord_12785, baseEnd_12785] using wordTrace_append hprefix tailTrace_12785
  have hstable : (prefixWord ++ tailWord_12785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12785).length < 2 ^ (prefixWord ++ tailWord_12785).sum := by decide
  have hdescent : baseEnd_12785 < baseStart_12785 := by decide
  rcases family_descends (prefixWord ++ tailWord_12785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12799 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_12799 : Nat := 118140960795 + 12799 * 2 ^ 59
def prefixEnd_12799 : Nat := 4983230072969 + 3 ^ 40 * 12799 * 2
def baseEnd_12799 : Nat := 5841812352889473381017

theorem tailTrace_12799 : CollatzResearch.WordTrace tailWord_12799 prefixEnd_12799 5841812352889473381017 := by
  unfold tailWord_12799
  simp only [CollatzResearch.WordTrace]
  refine ⟨466817880638883740281451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311211920425922493520967 466817880638883740281451)
  ·
    refine ⟨700226820958325610422177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466817880638883740281451 700226820958325610422177)
    ·
      refine ⟨525170115718744207816633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 700226820958325610422177 525170115718744207816633)
      ·
        refine ⟨393877586789058155862475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525170115718744207816633 393877586789058155862475)
        ·
          refine ⟨590816380183587233793713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393877586789058155862475 590816380183587233793713)
          ·
            refine ⟨443112285137690425345285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590816380183587233793713 443112285137690425345285)
            ·
              refine ⟨83083553463316954752241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443112285137690425345285 83083553463316954752241)
              ·
                refine ⟨62312665097487716064181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83083553463316954752241 62312665097487716064181)
                ·
                  refine ⟨5841812352889473381017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62312665097487716064181 5841812352889473381017)
                  ·
                    rfl

theorem cell20_12799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_12799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12799 prefixEnd_12799 := by exact prefixLift 12799
  have htrace : WordTrace (prefixWord ++ tailWord_12799) baseStart_12799 baseEnd_12799 := by
    simpa [prefixWord, tailWord_12799, baseEnd_12799] using wordTrace_append hprefix tailTrace_12799
  have hstable : (prefixWord ++ tailWord_12799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12799).length < 2 ^ (prefixWord ++ tailWord_12799).sum := by decide
  have hdescent : baseEnd_12799 < baseStart_12799 := by decide
  rcases family_descends (prefixWord ++ tailWord_12799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12833 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 3]
def baseStart_12833 : Nat := 118140960795 + 12833 * 2 ^ 59
def prefixEnd_12833 : Nat := 4983230072969 + 3 ^ 40 * 12833 * 2
def baseEnd_12833 : Nat := 5857330879336466247545

theorem tailTrace_12833 : CollatzResearch.WordTrace tailWord_12833 prefixEnd_12833 5857330879336466247545 := by
  unfold tailWord_12833
  simp only [CollatzResearch.WordTrace]
  refine ⟨468057962515707547019153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 312038641677138364679435 468057962515707547019153)
  ·
    refine ⟨351043471886780660264365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 468057962515707547019153 351043471886780660264365)
    ·
      refine ⟨131641301957542747599137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351043471886780660264365 131641301957542747599137)
      ·
        refine ⟨98730976468157060699353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131641301957542747599137 98730976468157060699353)
        ·
          refine ⟨74048232351117795524515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98730976468157060699353 74048232351117795524515)
          ·
            refine ⟨111072348526676693286773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74048232351117795524515 111072348526676693286773)
            ·
              refine ⟨10413032674375939995635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111072348526676693286773 10413032674375939995635)
              ·
                refine ⟨15619549011563909993453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10413032674375939995635 15619549011563909993453)
                ·
                  refine ⟨5857330879336466247545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15619549011563909993453 5857330879336466247545)
                  ·
                    rfl

theorem cell20_12833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_12833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12833 prefixEnd_12833 := by exact prefixLift 12833
  have htrace : WordTrace (prefixWord ++ tailWord_12833) baseStart_12833 baseEnd_12833 := by
    simpa [prefixWord, tailWord_12833, baseEnd_12833] using wordTrace_append hprefix tailTrace_12833
  have hstable : (prefixWord ++ tailWord_12833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12833).length < 2 ^ (prefixWord ++ tailWord_12833).sum := by decide
  have hdescent : baseEnd_12833 < baseStart_12833 := by decide
  rcases family_descends (prefixWord ++ tailWord_12833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12840 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_12840 : Nat := 118140960795 + 12840 * 2 ^ 59
def prefixEnd_12840 : Nat := 4983230072969 + 3 ^ 40 * 12840 * 2
def baseEnd_12840 : Nat := 5860525870075553014183

theorem tailTrace_12840 : CollatzResearch.WordTrace tailWord_12840 prefixEnd_12840 5860525870075553014183 := by
  unfold tailWord_12840
  simp only [CollatzResearch.WordTrace]
  refine ⟨234156636745173871261987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 312208848993565161682649 234156636745173871261987)
  ·
    refine ⟨351234955117760806892981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234156636745173871261987 351234955117760806892981)
    ·
      refine ⟨32928277042290075646217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351234955117760806892981 32928277042290075646217)
      ·
        refine ⟨24696207781717556734663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32928277042290075646217 24696207781717556734663)
        ·
          refine ⟨37044311672576335101995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24696207781717556734663 37044311672576335101995)
          ·
            refine ⟨55566467508864502652993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37044311672576335101995 55566467508864502652993)
            ·
              refine ⟨41674850631648376989745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55566467508864502652993 41674850631648376989745)
              ·
                refine ⟨31256137973736282742309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41674850631648376989745 31256137973736282742309)
                ·
                  refine ⟨5860525870075553014183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31256137973736282742309 5860525870075553014183)
                  ·
                    rfl

theorem cell20_12840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_12840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12840 prefixEnd_12840 := by exact prefixLift 12840
  have htrace : WordTrace (prefixWord ++ tailWord_12840) baseStart_12840 baseEnd_12840 := by
    simpa [prefixWord, tailWord_12840, baseEnd_12840] using wordTrace_append hprefix tailTrace_12840
  have hstable : (prefixWord ++ tailWord_12840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12840).length < 2 ^ (prefixWord ++ tailWord_12840).sum := by decide
  have hdescent : baseEnd_12840 < baseStart_12840 := by decide
  rcases family_descends (prefixWord ++ tailWord_12840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12875 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_12875 : Nat := 118140960795 + 12875 * 2 ^ 59
def prefixEnd_12875 : Nat := 4983230072969 + 3 ^ 40 * 12875 * 2
def baseEnd_12875 : Nat := 5876500823770986847373

theorem tailTrace_12875 : CollatzResearch.WordTrace tailWord_12875 prefixEnd_12875 5876500823770986847373 := by
  unfold tailWord_12875
  simp only [CollatzResearch.WordTrace]
  refine ⟨469589828363548720048079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 313059885575699146698719 469589828363548720048079)
  ·
    refine ⟨704384742545323080072119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469589828363548720048079 704384742545323080072119)
    ·
      refine ⟨1056577113817984620108179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704384742545323080072119 1056577113817984620108179)
      ·
        refine ⟨1584865670726976930162269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056577113817984620108179 1584865670726976930162269)
        ·
          refine ⟨594324626522616348810851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1584865670726976930162269 594324626522616348810851)
          ·
            refine ⟨891486939783924523216277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594324626522616348810851 891486939783924523216277)
            ·
              refine ⟨41788450302371462025763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 891486939783924523216277 41788450302371462025763)
              ·
                refine ⟨62682675453557193038645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41788450302371462025763 62682675453557193038645)
                ·
                  refine ⟨5876500823770986847373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62682675453557193038645 5876500823770986847373)
                  ·
                    rfl

theorem cell20_12875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_12875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12875 prefixEnd_12875 := by exact prefixLift 12875
  have htrace : WordTrace (prefixWord ++ tailWord_12875) baseStart_12875 baseEnd_12875 := by
    simpa [prefixWord, tailWord_12875, baseEnd_12875] using wordTrace_append hprefix tailTrace_12875
  have hstable : (prefixWord ++ tailWord_12875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12875).length < 2 ^ (prefixWord ++ tailWord_12875).sum := by decide
  have hdescent : baseEnd_12875 < baseStart_12875 := by decide
  rcases family_descends (prefixWord ++ tailWord_12875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12878 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_12878 : Nat := 118140960795 + 12878 * 2 ^ 59
def prefixEnd_12878 : Nat := 4983230072969 + 3 ^ 40 * 12878 * 2
def baseEnd_12878 : Nat := 5877870105516309747361

theorem tailTrace_12878 : CollatzResearch.WordTrace tailWord_12878 prefixEnd_12878 5877870105516309747361 := by
  unfold tailWord_12878
  simp only [CollatzResearch.WordTrace]
  refine ⟨58712405919085029050911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 313132831568453488271525 58712405919085029050911)
  ·
    refine ⟨88068608878627543576367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58712405919085029050911 88068608878627543576367)
    ·
      refine ⟨132102913317941315364551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88068608878627543576367 132102913317941315364551)
      ·
        refine ⟨198154369976911973046827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132102913317941315364551 198154369976911973046827)
        ·
          refine ⟨297231554965367959570241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198154369976911973046827 297231554965367959570241)
          ·
            refine ⟨222923666224025969677681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297231554965367959570241 222923666224025969677681)
            ·
              refine ⟨167192749668019477258261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222923666224025969677681 167192749668019477258261)
              ·
                refine ⟨7837160140688412996481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167192749668019477258261 7837160140688412996481)
                ·
                  refine ⟨5877870105516309747361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837160140688412996481 5877870105516309747361)
                  ·
                    rfl

theorem cell20_12878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_12878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12878 prefixEnd_12878 := by exact prefixLift 12878
  have htrace : WordTrace (prefixWord ++ tailWord_12878) baseStart_12878 baseEnd_12878 := by
    simpa [prefixWord, tailWord_12878, baseEnd_12878] using wordTrace_append hprefix tailTrace_12878
  have hstable : (prefixWord ++ tailWord_12878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12878).length < 2 ^ (prefixWord ++ tailWord_12878).sum := by decide
  have hdescent : baseEnd_12878 < baseStart_12878 := by decide
  rcases family_descends (prefixWord ++ tailWord_12878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12906 : List Nat := [3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_12906 : Nat := 118140960795 + 12906 * 2 ^ 59
def prefixEnd_12906 : Nat := 4983230072969 + 3 ^ 40 * 12906 * 2
def baseEnd_12906 : Nat := 1963550022824218937971

theorem tailTrace_12906 : CollatzResearch.WordTrace tailWord_12906 prefixEnd_12906 1963550022824218937971 := by
  unfold tailWord_12906
  simp only [CollatzResearch.WordTrace]
  refine ⟨117680122812810253606643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 313813660834160676284381 117680122812810253606643)
  ·
    refine ⟨176520184219215380409965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117680122812810253606643 176520184219215380409965)
    ·
      refine ⟨66195069082205767653737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176520184219215380409965 66195069082205767653737)
      ·
        refine ⟨49646301811654325740303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66195069082205767653737 49646301811654325740303)
        ·
          refine ⟨74469452717481488610455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49646301811654325740303 74469452717481488610455)
          ·
            refine ⟨111704179076222232915683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74469452717481488610455 111704179076222232915683)
            ·
              refine ⟨167556268614333349373525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111704179076222232915683 167556268614333349373525)
              ·
                refine ⟨1963550022824218937971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 167556268614333349373525 1963550022824218937971)
                ·
                  rfl

theorem cell20_12906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_12906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12906 prefixEnd_12906 := by exact prefixLift 12906
  have htrace : WordTrace (prefixWord ++ tailWord_12906) baseStart_12906 baseEnd_12906 := by
    simpa [prefixWord, tailWord_12906, baseEnd_12906] using wordTrace_append hprefix tailTrace_12906
  have hstable : (prefixWord ++ tailWord_12906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12906).length < 2 ^ (prefixWord ++ tailWord_12906).sum := by decide
  have hdescent : baseEnd_12906 < baseStart_12906 := by decide
  rcases family_descends (prefixWord ++ tailWord_12906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12920 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_12920 : Nat := 118140960795 + 12920 * 2 ^ 59
def prefixEnd_12920 : Nat := 4983230072969 + 3 ^ 40 * 12920 * 2
def baseEnd_12920 : Nat := 5897040049950830347189

theorem tailTrace_12920 : CollatzResearch.WordTrace tailWord_12920 prefixEnd_12920 5897040049950830347189 := by
  unfold tailWord_12920
  simp only [CollatzResearch.WordTrace]
  refine ⟨235615556600260702718107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 314154075467014270290809 235615556600260702718107)
  ·
    refine ⟨353423334900391054077161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235615556600260702718107 353423334900391054077161)
    ·
      refine ⟨265067501175293290557871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353423334900391054077161 265067501175293290557871)
      ·
        refine ⟨397601251762939935836807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265067501175293290557871 397601251762939935836807)
        ·
          refine ⟨596401877644409903755211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397601251762939935836807 596401877644409903755211)
          ·
            refine ⟨894602816466614855632817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596401877644409903755211 894602816466614855632817)
            ·
              refine ⟨670952112349961141724613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894602816466614855632817 670952112349961141724613)
              ·
                refine ⟨125803521065617714073365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 670952112349961141724613 125803521065617714073365)
                ·
                  refine ⟨5897040049950830347189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125803521065617714073365 5897040049950830347189)
                  ·
                    rfl

theorem cell20_12920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_12920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12920 prefixEnd_12920 := by exact prefixLift 12920
  have htrace : WordTrace (prefixWord ++ tailWord_12920) baseStart_12920 baseEnd_12920 := by
    simpa [prefixWord, tailWord_12920, baseEnd_12920] using wordTrace_append hprefix tailTrace_12920
  have hstable : (prefixWord ++ tailWord_12920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12920).length < 2 ^ (prefixWord ++ tailWord_12920).sum := by decide
  have hdescent : baseEnd_12920 < baseStart_12920 := by decide
  rcases family_descends (prefixWord ++ tailWord_12920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12933 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 2]
def baseStart_12933 : Nat := 118140960795 + 12933 * 2 ^ 59
def prefixEnd_12933 : Nat := 4983230072969 + 3 ^ 40 * 12933 * 2
def baseEnd_12933 : Nat := 5902973604180562913803

theorem tailTrace_12933 : CollatzResearch.WordTrace tailWord_12933 prefixEnd_12933 5902973604180562913803 := by
  unfold tailWord_12933
  simp only [CollatzResearch.WordTrace]
  refine ⟨471705262153424625659453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 314470174768949750439635 471705262153424625659453)
  ·
    refine ⟨176889473307534234622295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 471705262153424625659453 176889473307534234622295)
    ·
      refine ⟨265334209961301351933443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176889473307534234622295 265334209961301351933443)
      ·
        refine ⟨398001314941952027900165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265334209961301351933443 398001314941952027900165)
        ·
          refine ⟨74625246551616005231281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398001314941952027900165 74625246551616005231281)
          ·
            refine ⟨55968934913712003923461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74625246551616005231281 55968934913712003923461)
            ·
              refine ⟨10494175296321000735649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55968934913712003923461 10494175296321000735649)
              ·
                refine ⟨7870631472240750551737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10494175296321000735649 7870631472240750551737)
                ·
                  refine ⟨5902973604180562913803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870631472240750551737 5902973604180562913803)
                  ·
                    rfl

theorem cell20_12933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_12933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12933 prefixEnd_12933 := by exact prefixLift 12933
  have htrace : WordTrace (prefixWord ++ tailWord_12933) baseStart_12933 baseEnd_12933 := by
    simpa [prefixWord, tailWord_12933, baseEnd_12933] using wordTrace_append hprefix tailTrace_12933
  have hstable : (prefixWord ++ tailWord_12933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12933).length < 2 ^ (prefixWord ++ tailWord_12933).sum := by decide
  have hdescent : baseEnd_12933 < baseStart_12933 := by decide
  rcases family_descends (prefixWord ++ tailWord_12933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12992 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_12992 : Nat := 118140960795 + 12992 * 2 ^ 59
def prefixEnd_12992 : Nat := 4983230072969 + 3 ^ 40 * 12992 * 2
def baseEnd_12992 : Nat := 5929902811838579946895

theorem tailTrace_12992 : CollatzResearch.WordTrace tailWord_12992 prefixEnd_12992 5929902811838579946895 := by
  unfold tailWord_12992
  simp only [CollatzResearch.WordTrace]
  refine ⟨236928584469838851028615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 315904779293118468038153 236928584469838851028615)
  ·
    refine ⟨355392876704758276542923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236928584469838851028615 355392876704758276542923)
    ·
      refine ⟨533089315057137414814385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355392876704758276542923 533089315057137414814385)
      ·
        refine ⟨399816986292853061110789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533089315057137414814385 399816986292853061110789)
        ·
          refine ⟨74965684929909948958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399816986292853061110789 74965684929909948958273)
          ·
            refine ⟨56224263697432461718705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74965684929909948958273 56224263697432461718705)
            ·
              refine ⟨42168197773074346289029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56224263697432461718705 42168197773074346289029)
              ·
                refine ⟨7906537082451439929193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42168197773074346289029 7906537082451439929193)
                ·
                  refine ⟨5929902811838579946895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7906537082451439929193 5929902811838579946895)
                  ·
                    rfl

theorem cell20_12992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_12992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12992 prefixEnd_12992 := by exact prefixLift 12992
  have htrace : WordTrace (prefixWord ++ tailWord_12992) baseStart_12992 baseEnd_12992 := by
    simpa [prefixWord, tailWord_12992, baseEnd_12992] using wordTrace_append hprefix tailTrace_12992
  have hstable : (prefixWord ++ tailWord_12992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12992).length < 2 ^ (prefixWord ++ tailWord_12992).sum := by decide
  have hdescent : baseEnd_12992 < baseStart_12992 := by decide
  rcases family_descends (prefixWord ++ tailWord_12992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12998 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_12998 : Nat := 118140960795 + 12998 * 2 ^ 59
def prefixEnd_12998 : Nat := 4983230072969 + 3 ^ 40 * 12998 * 2
def baseEnd_12998 : Nat := 5932641375329225746871

theorem tailTrace_12998 : CollatzResearch.WordTrace tailWord_12998 prefixEnd_12998 5932641375329225746871 := by
  unfold tailWord_12998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14814875216185647711739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 316050671278627151183765 14814875216185647711739)
  ·
    refine ⟨22222312824278471567609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14814875216185647711739 22222312824278471567609)
    ·
      refine ⟨16666734618208853675707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22222312824278471567609 16666734618208853675707)
      ·
        refine ⟨25000101927313280513561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16666734618208853675707 25000101927313280513561)
        ·
          refine ⟨18750076445484960385171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25000101927313280513561 18750076445484960385171)
          ·
            refine ⟨28125114668227440577757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18750076445484960385171 28125114668227440577757)
            ·
              refine ⟨10546918000585290216659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28125114668227440577757 10546918000585290216659)
              ·
                refine ⟨15820377000877935324989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10546918000585290216659 15820377000877935324989)
                ·
                  refine ⟨5932641375329225746871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15820377000877935324989 5932641375329225746871)
                  ·
                    rfl

theorem cell20_12998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_12998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_12998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_12998 prefixEnd_12998 := by exact prefixLift 12998
  have htrace : WordTrace (prefixWord ++ tailWord_12998) baseStart_12998 baseEnd_12998 := by
    simpa [prefixWord, tailWord_12998, baseEnd_12998] using wordTrace_append hprefix tailTrace_12998
  have hstable : (prefixWord ++ tailWord_12998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12998).length < 2 ^ (prefixWord ++ tailWord_12998).sum := by decide
  have hdescent : baseEnd_12998 < baseStart_12998 := by decide
  rcases family_descends (prefixWord ++ tailWord_12998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13098 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_13098 : Nat := 118140960795 + 13098 * 2 ^ 59
def prefixEnd_13098 : Nat := 4983230072969 + 3 ^ 40 * 13098 * 2
def baseEnd_13098 : Nat := 5978284100173322413129

theorem tailTrace_13098 : CollatzResearch.WordTrace tailWord_13098 prefixEnd_13098 5978284100173322413129 := by
  unfold tailWord_13098
  simp only [CollatzResearch.WordTrace]
  refine ⟨119430826638914451353987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 318482204370438536943965 119430826638914451353987)
  ·
    refine ⟨179146239958371677030981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119430826638914451353987 179146239958371677030981)
    ·
      refine ⟨33589919992194689443309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179146239958371677030981 33589919992194689443309)
      ·
        refine ⟨12596219997073008541241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33589919992194689443309 12596219997073008541241)
        ·
          refine ⟨9447164997804756405931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12596219997073008541241 9447164997804756405931)
          ·
            refine ⟨14170747496707134608897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447164997804756405931 14170747496707134608897)
            ·
              refine ⟨10628060622530350956673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14170747496707134608897 10628060622530350956673)
              ·
                refine ⟨7971045466897763217505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10628060622530350956673 7971045466897763217505)
                ·
                  refine ⟨5978284100173322413129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7971045466897763217505 5978284100173322413129)
                  ·
                    rfl

theorem cell20_13098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_13098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13098 prefixEnd_13098 := by exact prefixLift 13098
  have htrace : WordTrace (prefixWord ++ tailWord_13098) baseStart_13098 baseEnd_13098 := by
    simpa [prefixWord, tailWord_13098, baseEnd_13098] using wordTrace_append hprefix tailTrace_13098
  have hstable : (prefixWord ++ tailWord_13098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13098).length < 2 ^ (prefixWord ++ tailWord_13098).sum := by decide
  have hdescent : baseEnd_13098 < baseStart_13098 := by decide
  rcases family_descends (prefixWord ++ tailWord_13098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13102 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_13102 : Nat := 118140960795 + 13102 * 2 ^ 59
def prefixEnd_13102 : Nat := 4983230072969 + 3 ^ 40 * 13102 * 2
def baseEnd_13102 : Nat := 5980109809167086279779

theorem tailTrace_13102 : CollatzResearch.WordTrace tailWord_13102 prefixEnd_13102 5980109809167086279779 := by
  unfold tailWord_13102
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733649817645811070195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 318579465694110992374373 59733649817645811070195)
  ·
    refine ⟨89600474726468716605293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59733649817645811070195 89600474726468716605293)
    ·
      refine ⟨33600178022425768726985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89600474726468716605293 33600178022425768726985)
      ·
        refine ⟨25200133516819326545239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33600178022425768726985 25200133516819326545239)
        ·
          refine ⟨37800200275228989817859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25200133516819326545239 37800200275228989817859)
          ·
            refine ⟨56700300412843484726789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37800200275228989817859 56700300412843484726789)
            ·
              refine ⟨10631306327408153386273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56700300412843484726789 10631306327408153386273)
              ·
                refine ⟨7973479745556115039705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10631306327408153386273 7973479745556115039705)
                ·
                  refine ⟨5980109809167086279779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7973479745556115039705 5980109809167086279779)
                  ·
                    rfl

theorem cell20_13102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_13102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13102 prefixEnd_13102 := by exact prefixLift 13102
  have htrace : WordTrace (prefixWord ++ tailWord_13102) baseStart_13102 baseEnd_13102 := by
    simpa [prefixWord, tailWord_13102, baseEnd_13102] using wordTrace_append hprefix tailTrace_13102
  have hstable : (prefixWord ++ tailWord_13102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13102).length < 2 ^ (prefixWord ++ tailWord_13102).sum := by decide
  have hdescent : baseEnd_13102 < baseStart_13102 := by decide
  rcases family_descends (prefixWord ++ tailWord_13102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13106 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_13106 : Nat := 118140960795 + 13106 * 2 ^ 59
def prefixEnd_13106 : Nat := 4983230072969 + 3 ^ 40 * 13106 * 2
def baseEnd_13106 : Nat := 5981935518160850146429

theorem tailTrace_13106 : CollatzResearch.WordTrace tailWord_13106 prefixEnd_13106 5981935518160850146429 := by
  unfold tailWord_13106
  simp only [CollatzResearch.WordTrace]
  refine ⟨119503772631668792926793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 318676727017783447804781 119503772631668792926793)
  ·
    refine ⟨89627829473751594695095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119503772631668792926793 89627829473751594695095)
    ·
      refine ⟨134441744210627392042643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89627829473751594695095 134441744210627392042643)
      ·
        refine ⟨201662616315941088063965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134441744210627392042643 201662616315941088063965)
        ·
          refine ⟨75623481118477908023987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201662616315941088063965 75623481118477908023987)
          ·
            refine ⟨113435221677716862035981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75623481118477908023987 113435221677716862035981)
            ·
              refine ⟨42538208129143823263493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113435221677716862035981 42538208129143823263493)
              ·
                refine ⟨7975914024214466861905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42538208129143823263493 7975914024214466861905)
                ·
                  refine ⟨5981935518160850146429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7975914024214466861905 5981935518160850146429)
                  ·
                    rfl

theorem cell20_13106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_13106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13106 prefixEnd_13106 := by exact prefixLift 13106
  have htrace : WordTrace (prefixWord ++ tailWord_13106) baseStart_13106 baseEnd_13106 := by
    simpa [prefixWord, tailWord_13106, baseEnd_13106] using wordTrace_append hprefix tailTrace_13106
  have hstable : (prefixWord ++ tailWord_13106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13106).length < 2 ^ (prefixWord ++ tailWord_13106).sum := by decide
  have hdescent : baseEnd_13106 < baseStart_13106 := by decide
  rcases family_descends (prefixWord ++ tailWord_13106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13141 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_13141 : Nat := 118140960795 + 13141 * 2 ^ 59
def prefixEnd_13141 : Nat := 4983230072969 + 3 ^ 40 * 13141 * 2
def baseEnd_13141 : Nat := 5997910471856283979619

theorem tailTrace_13141 : CollatzResearch.WordTrace tailWord_13141 prefixEnd_13141 5997910471856283979619 := by
  unfold tailWord_13141
  simp only [CollatzResearch.WordTrace]
  refine ⟨479291645399876149231277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 319527763599917432820851 479291645399876149231277)
  ·
    refine ⟨179734367024953555961729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 479291645399876149231277 179734367024953555961729)
    ·
      refine ⟨134800775268715166971297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179734367024953555961729 134800775268715166971297)
      ·
        refine ⟨101100581451536375228473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134800775268715166971297 101100581451536375228473)
        ·
          refine ⟨75825436088652281421355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101100581451536375228473 75825436088652281421355)
          ·
            refine ⟨113738154132978422132033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75825436088652281421355 113738154132978422132033)
            ·
              refine ⟨85303615599733816599025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113738154132978422132033 85303615599733816599025)
              ·
                refine ⟨63977711699800362449269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85303615599733816599025 63977711699800362449269)
                ·
                  refine ⟨5997910471856283979619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63977711699800362449269 5997910471856283979619)
                  ·
                    rfl

theorem cell20_13141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_13141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13141 prefixEnd_13141 := by exact prefixLift 13141
  have htrace : WordTrace (prefixWord ++ tailWord_13141) baseStart_13141 baseEnd_13141 := by
    simpa [prefixWord, tailWord_13141, baseEnd_13141] using wordTrace_append hprefix tailTrace_13141
  have hstable : (prefixWord ++ tailWord_13141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13141).length < 2 ^ (prefixWord ++ tailWord_13141).sum := by decide
  have hdescent : baseEnd_13141 < baseStart_13141 := by decide
  rcases family_descends (prefixWord ++ tailWord_13141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13154 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_13154 : Nat := 118140960795 + 13154 * 2 ^ 59
def prefixEnd_13154 : Nat := 4983230072969 + 3 ^ 40 * 13154 * 2
def baseEnd_13154 : Nat := 6003844026086016546233

theorem tailTrace_13154 : CollatzResearch.WordTrace tailWord_13154 prefixEnd_13154 6003844026086016546233 := by
  unfold tailWord_13154
  simp only [CollatzResearch.WordTrace]
  refine ⟨119941448588194842363629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 319843862901852912969677 119941448588194842363629)
  ·
    refine ⟨44978043220573065886361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119941448588194842363629 44978043220573065886361)
    ·
      refine ⟨33733532415429799414771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44978043220573065886361 33733532415429799414771)
      ·
        refine ⟨50600298623144699122157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33733532415429799414771 50600298623144699122157)
        ·
          refine ⟨18975111983679262170809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50600298623144699122157 18975111983679262170809)
          ·
            refine ⟨14231333987759446628107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18975111983679262170809 14231333987759446628107)
            ·
              refine ⟨21347000981639169942161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14231333987759446628107 21347000981639169942161)
              ·
                refine ⟨16010250736229377456621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21347000981639169942161 16010250736229377456621)
                ·
                  refine ⟨6003844026086016546233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16010250736229377456621 6003844026086016546233)
                  ·
                    rfl

theorem cell20_13154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_13154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13154 prefixEnd_13154 := by exact prefixLift 13154
  have htrace : WordTrace (prefixWord ++ tailWord_13154) baseStart_13154 baseEnd_13154 := by
    simpa [prefixWord, tailWord_13154, baseEnd_13154] using wordTrace_append hprefix tailTrace_13154
  have hstable : (prefixWord ++ tailWord_13154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13154).length < 2 ^ (prefixWord ++ tailWord_13154).sum := by decide
  have hdescent : baseEnd_13154 < baseStart_13154 := by decide
  rcases family_descends (prefixWord ++ tailWord_13154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13179 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_13179 : Nat := 118140960795 + 13179 * 2 ^ 59
def prefixEnd_13179 : Nat := 4983230072969 + 3 ^ 40 * 13179 * 2
def baseEnd_13179 : Nat := 6015254707297040712797

theorem tailTrace_13179 : CollatzResearch.WordTrace tailWord_13179 prefixEnd_13179 6015254707297040712797 := by
  unfold tailWord_13179
  simp only [CollatzResearch.WordTrace]
  refine ⟨480677619262208639114591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 320451746174805759409727 480677619262208639114591)
  ·
    refine ⟨721016428893312958671887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 480677619262208639114591 721016428893312958671887)
    ·
      refine ⟨1081524643339969438007831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721016428893312958671887 1081524643339969438007831)
      ·
        refine ⟨1622286965009954157011747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081524643339969438007831 1622286965009954157011747)
        ·
          refine ⟨2433430447514931235517621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622286965009954157011747 2433430447514931235517621)
          ·
            refine ⟨228134104454524803329777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2433430447514931235517621 228134104454524803329777)
            ·
              refine ⟨171100578340893602497333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228134104454524803329777 171100578340893602497333)
              ·
                refine ⟨16040679219458775234125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171100578340893602497333 16040679219458775234125)
                ·
                  refine ⟨6015254707297040712797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16040679219458775234125 6015254707297040712797)
                  ·
                    rfl

theorem cell20_13179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_13179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13179 prefixEnd_13179 := by exact prefixLift 13179
  have htrace : WordTrace (prefixWord ++ tailWord_13179) baseStart_13179 baseEnd_13179 := by
    simpa [prefixWord, tailWord_13179, baseEnd_13179] using wordTrace_append hprefix tailTrace_13179
  have hstable : (prefixWord ++ tailWord_13179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13179).length < 2 ^ (prefixWord ++ tailWord_13179).sum := by decide
  have hdescent : baseEnd_13179 < baseStart_13179 := by decide
  rcases family_descends (prefixWord ++ tailWord_13179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13189 : List Nat := [1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_13189 : Nat := 118140960795 + 13189 * 2 ^ 59
def prefixEnd_13189 : Nat := 4983230072969 + 3 ^ 40 * 13189 * 2
def baseEnd_13189 : Nat := 2006606326593816793141

theorem tailTrace_13189 : CollatzResearch.WordTrace tailWord_13189 prefixEnd_13189 2006606326593816793141 := by
  unfold tailWord_13189
  simp only [CollatzResearch.WordTrace]
  refine ⟨481042349225980346978621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 320694899483986897985747 481042349225980346978621)
  ·
    refine ⟨180390880959742630116983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 481042349225980346978621 180390880959742630116983)
    ·
      refine ⟨270586321439613945175475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180390880959742630116983 270586321439613945175475)
      ·
        refine ⟨405879482159420917763213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270586321439613945175475 405879482159420917763213)
        ·
          refine ⟨152204805809782844161205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405879482159420917763213 152204805809782844161205)
          ·
            refine ⟨14269200544667141640113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152204805809782844161205 14269200544667141640113)
            ·
              refine ⟨10701900408500356230085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14269200544667141640113 10701900408500356230085)
              ·
                refine ⟨2006606326593816793141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10701900408500356230085 2006606326593816793141)
                ·
                  rfl

theorem cell20_13189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_13189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13189 prefixEnd_13189 := by exact prefixLift 13189
  have htrace : WordTrace (prefixWord ++ tailWord_13189) baseStart_13189 baseEnd_13189 := by
    simpa [prefixWord, tailWord_13189, baseEnd_13189] using wordTrace_append hprefix tailTrace_13189
  have hstable : (prefixWord ++ tailWord_13189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13189).length < 2 ^ (prefixWord ++ tailWord_13189).sum := by decide
  have hdescent : baseEnd_13189 < baseStart_13189 := by decide
  rcases family_descends (prefixWord ++ tailWord_13189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13203 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 2]
def baseStart_13203 : Nat := 118140960795 + 13203 * 2 ^ 59
def prefixEnd_13203 : Nat := 4983230072969 + 3 ^ 40 * 13203 * 2
def baseEnd_13203 : Nat := 6026208961259623912699

theorem tailTrace_13203 : CollatzResearch.WordTrace tailWord_13203 prefixEnd_13203 6026208961259623912699 := by
  unfold tailWord_13203
  simp only [CollatzResearch.WordTrace]
  refine ⟨481552971175260737988263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 321035314116840491992175 481552971175260737988263)
  ·
    refine ⟨722329456762891106982395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481552971175260737988263 722329456762891106982395)
    ·
      refine ⟨1083494185144336660473593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722329456762891106982395 1083494185144336660473593)
      ·
        refine ⟨812620638858252495355195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083494185144336660473593 812620638858252495355195)
        ·
          refine ⟨1218930958287378743032793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812620638858252495355195 1218930958287378743032793)
          ·
            refine ⟨914198218715534057274595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218930958287378743032793 914198218715534057274595)
            ·
              refine ⟨1371297328073301085911893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914198218715534057274595 1371297328073301085911893)
              ·
                refine ⟨8034945281679498550265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1371297328073301085911893 8034945281679498550265)
                ·
                  refine ⟨6026208961259623912699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034945281679498550265 6026208961259623912699)
                  ·
                    rfl

theorem cell20_13203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2].length) (baseStart_13203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13203 prefixEnd_13203 := by exact prefixLift 13203
  have htrace : WordTrace (prefixWord ++ tailWord_13203) baseStart_13203 baseEnd_13203 := by
    simpa [prefixWord, tailWord_13203, baseEnd_13203] using wordTrace_append hprefix tailTrace_13203
  have hstable : (prefixWord ++ tailWord_13203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13203).length < 2 ^ (prefixWord ++ tailWord_13203).sum := by decide
  have hdescent : baseEnd_13203 < baseStart_13203 := by decide
  rcases family_descends (prefixWord ++ tailWord_13203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13206 : List Nat := [5, 3, 1, 1, 1, 1, 8]
def baseStart_13206 : Nat := 118140960795 + 13206 * 2 ^ 59
def prefixEnd_13206 : Nat := 4983230072969 + 3 ^ 40 * 13206 * 2
def baseEnd_13206 : Nat := 669730915889438534743

theorem tailTrace_13206 : CollatzResearch.WordTrace tailWord_13206 prefixEnd_13206 669730915889438534743 := by
  unfold tailWord_13206
  simp only [CollatzResearch.WordTrace]
  refine ⟨30103899385274515646717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 321108260109594833564981 30103899385274515646717)
  ·
    refine ⟨11288962269477943367519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30103899385274515646717 11288962269477943367519)
    ·
      refine ⟨16933443404216915051279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11288962269477943367519 16933443404216915051279)
      ·
        refine ⟨25400165106325372576919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16933443404216915051279 25400165106325372576919)
        ·
          refine ⟨38100247659488058865379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25400165106325372576919 38100247659488058865379)
          ·
            refine ⟨57150371489232088298069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38100247659488058865379 57150371489232088298069)
            ·
              refine ⟨669730915889438534743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57150371489232088298069 669730915889438534743)
              ·
                rfl

theorem cell20_13206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_13206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13206 prefixEnd_13206 := by exact prefixLift 13206
  have htrace : WordTrace (prefixWord ++ tailWord_13206) baseStart_13206 baseEnd_13206 := by
    simpa [prefixWord, tailWord_13206, baseEnd_13206] using wordTrace_append hprefix tailTrace_13206
  have hstable : (prefixWord ++ tailWord_13206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13206).length < 2 ^ (prefixWord ++ tailWord_13206).sum := by decide
  have hdescent : baseEnd_13206 < baseStart_13206 := by decide
  rcases family_descends (prefixWord ++ tailWord_13206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13261 : List Nat := [1, 6, 3, 1, 2, 7]
def baseStart_13261 : Nat := 118140960795 + 13261 * 2 ^ 59
def prefixEnd_13261 : Nat := 4983230072969 + 3 ^ 40 * 13261 * 2
def baseEnd_13261 : Nat := 224173397839599999227

theorem tailTrace_13261 : CollatzResearch.WordTrace tailWord_13261 prefixEnd_13261 224173397839599999227 := by
  unfold tailWord_13261
  simp only [CollatzResearch.WordTrace]
  refine ⟨483668404965136643599637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 322445603310091095733091 483668404965136643599637)
  ·
    refine ⟨22671956482740780168733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 483668404965136643599637 22671956482740780168733)
    ·
      refine ⟨8501983681027792563275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22671956482740780168733 8501983681027792563275)
      ·
        refine ⟨12752975521541688844913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501983681027792563275 12752975521541688844913)
        ·
          refine ⟨9564731641156266633685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12752975521541688844913 9564731641156266633685)
          ·
            refine ⟨224173397839599999227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9564731641156266633685 224173397839599999227)
            ·
              rfl

theorem cell20_13261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 7].length) (baseStart_13261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13261 prefixEnd_13261 := by exact prefixLift 13261
  have htrace : WordTrace (prefixWord ++ tailWord_13261) baseStart_13261 baseEnd_13261 := by
    simpa [prefixWord, tailWord_13261, baseEnd_13261] using wordTrace_append hprefix tailTrace_13261
  have hstable : (prefixWord ++ tailWord_13261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13261).length < 2 ^ (prefixWord ++ tailWord_13261).sum := by decide
  have hdescent : baseEnd_13261 < baseStart_13261 := by decide
  rcases family_descends (prefixWord ++ tailWord_13261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13269 : List Nat := [1, 3, 2, 3, 11]
def baseStart_13269 : Nat := 118140960795 + 13269 * 2 ^ 59
def prefixEnd_13269 : Nat := 4983230072969 + 3 ^ 40 * 13269 * 2
def baseEnd_13269 : Nat := 74769545180947255709

theorem tailTrace_13269 : CollatzResearch.WordTrace tailWord_13269 prefixEnd_13269 74769545180947255709 := by
  unfold tailWord_13269
  simp only [CollatzResearch.WordTrace]
  refine ⟨483960188936154009890861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 322640125957436006593907 483960188936154009890861)
  ·
    refine ⟨181485070851057753709073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 483960188936154009890861 181485070851057753709073)
    ·
      refine ⟨136113803138293315281805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181485070851057753709073 136113803138293315281805)
      ·
        refine ⟨51042676176859993230677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136113803138293315281805 51042676176859993230677)
        ·
          refine ⟨74769545180947255709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 51042676176859993230677 74769545180947255709)
          ·
            rfl

theorem cell20_13269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 11].length) (baseStart_13269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13269 prefixEnd_13269 := by exact prefixLift 13269
  have htrace : WordTrace (prefixWord ++ tailWord_13269) baseStart_13269 baseEnd_13269 := by
    simpa [prefixWord, tailWord_13269, baseEnd_13269] using wordTrace_append hprefix tailTrace_13269
  have hstable : (prefixWord ++ tailWord_13269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13269).length < 2 ^ (prefixWord ++ tailWord_13269).sum := by decide
  have hdescent : baseEnd_13269 < baseStart_13269 := by decide
  rcases family_descends (prefixWord ++ tailWord_13269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13272 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_13272 : Nat := 118140960795 + 13272 * 2 ^ 59
def prefixEnd_13272 : Nat := 4983230072969 + 3 ^ 40 * 13272 * 2
def baseEnd_13272 : Nat := 6057702441402050612417

theorem tailTrace_13272 : CollatzResearch.WordTrace tailWord_13272 prefixEnd_13272 6057702441402050612417 := by
  unfold tailWord_13272
  simp only [CollatzResearch.WordTrace]
  refine ⟨242034803962642761125035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 322713071950190348166713 242034803962642761125035)
  ·
    refine ⟨363052205943964141687553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242034803962642761125035 363052205943964141687553)
    ·
      refine ⟨272289154457973106265665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363052205943964141687553 272289154457973106265665)
      ·
        refine ⟨204216865843479829699249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272289154457973106265665 204216865843479829699249)
        ·
          refine ⟨153162649382609872274437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204216865843479829699249 153162649382609872274437)
          ·
            refine ⟨28717996759239351051457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153162649382609872274437 28717996759239351051457)
            ·
              refine ⟨21538497569429513288593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28717996759239351051457 21538497569429513288593)
              ·
                refine ⟨16153873177072134966445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21538497569429513288593 16153873177072134966445)
                ·
                  refine ⟨6057702441402050612417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16153873177072134966445 6057702441402050612417)
                  ·
                    rfl

theorem cell20_13272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_13272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13272 prefixEnd_13272 := by exact prefixLift 13272
  have htrace : WordTrace (prefixWord ++ tailWord_13272) baseStart_13272 baseEnd_13272 := by
    simpa [prefixWord, tailWord_13272, baseEnd_13272] using wordTrace_append hprefix tailTrace_13272
  have hstable : (prefixWord ++ tailWord_13272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13272).length < 2 ^ (prefixWord ++ tailWord_13272).sum := by decide
  have hdescent : baseEnd_13272 < baseStart_13272 := by decide
  rcases family_descends (prefixWord ++ tailWord_13272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13282 : List Nat := [3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_13282 : Nat := 118140960795 + 13282 * 2 ^ 59
def prefixEnd_13282 : Nat := 4983230072969 + 3 ^ 40 * 13282 * 2
def baseEnd_13282 : Nat := 2020755571295486759681

theorem tailTrace_13282 : CollatzResearch.WordTrace tailWord_13282 prefixEnd_13282 2020755571295486759681 := by
  unfold tailWord_13282
  simp only [CollatzResearch.WordTrace]
  refine ⟨121108584472264307528525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 322956225259371486742733 121108584472264307528525)
  ·
    refine ⟨45415719177099115323197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121108584472264307528525 45415719177099115323197)
    ·
      refine ⟨17030894691412168246199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45415719177099115323197 17030894691412168246199)
      ·
        refine ⟨25546342037118252369299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17030894691412168246199 25546342037118252369299)
        ·
          refine ⟨38319513055677378553949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25546342037118252369299 38319513055677378553949)
          ·
            refine ⟨14369817395879016957731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38319513055677378553949 14369817395879016957731)
            ·
              refine ⟨21554726093818525436597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14369817395879016957731 21554726093818525436597)
              ·
                refine ⟨2020755571295486759681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21554726093818525436597 2020755571295486759681)
                ·
                  rfl

theorem cell20_13282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_13282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13282 prefixEnd_13282 := by exact prefixLift 13282
  have htrace : WordTrace (prefixWord ++ tailWord_13282) baseStart_13282 baseEnd_13282 := by
    simpa [prefixWord, tailWord_13282, baseEnd_13282] using wordTrace_append hprefix tailTrace_13282
  have hstable : (prefixWord ++ tailWord_13282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13282).length < 2 ^ (prefixWord ++ tailWord_13282).sum := by decide
  have hdescent : baseEnd_13282 < baseStart_13282 := by decide
  rcases family_descends (prefixWord ++ tailWord_13282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13330 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_13330 : Nat := 118140960795 + 13330 * 2 ^ 59
def prefixEnd_13330 : Nat := 4983230072969 + 3 ^ 40 * 13330 * 2
def baseEnd_13330 : Nat := 6084175221811626678847

theorem tailTrace_13330 : CollatzResearch.WordTrace tailWord_13330 prefixEnd_13330 6084175221811626678847 := by
  unfold tailWord_13330
  simp only [CollatzResearch.WordTrace]
  refine ⟨121546260428790356965361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 324123361143440951907629 121546260428790356965361)
  ·
    refine ⟨91159695321592767724021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121546260428790356965361 91159695321592767724021)
    ·
      refine ⟨8546221436399321974127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91159695321592767724021 8546221436399321974127)
      ·
        refine ⟨12819332154598982961191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8546221436399321974127 12819332154598982961191)
        ·
          refine ⟨19228998231898474441787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12819332154598982961191 19228998231898474441787)
          ·
            refine ⟨28843497347847711662681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19228998231898474441787 28843497347847711662681)
            ·
              refine ⟨21632623010885783747011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28843497347847711662681 21632623010885783747011)
              ·
                refine ⟨32448934516328675620517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21632623010885783747011 32448934516328675620517)
                ·
                  refine ⟨6084175221811626678847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32448934516328675620517 6084175221811626678847)
                  ·
                    rfl

theorem cell20_13330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_13330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13330 prefixEnd_13330 := by exact prefixLift 13330
  have htrace : WordTrace (prefixWord ++ tailWord_13330) baseStart_13330 baseEnd_13330 := by
    simpa [prefixWord, tailWord_13330, baseEnd_13330] using wordTrace_append hprefix tailTrace_13330
  have hstable : (prefixWord ++ tailWord_13330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13330).length < 2 ^ (prefixWord ++ tailWord_13330).sum := by decide
  have hdescent : baseEnd_13330 < baseStart_13330 := by decide
  rcases family_descends (prefixWord ++ tailWord_13330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13344 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_13344 : Nat := 118140960795 + 13344 * 2 ^ 59
def prefixEnd_13344 : Nat := 4983230072969 + 3 ^ 40 * 13344 * 2
def baseEnd_13344 : Nat := 6090565203289800212123

theorem tailTrace_13344 : CollatzResearch.WordTrace tailWord_13344 prefixEnd_13344 6090565203289800212123 := by
  unfold tailWord_13344
  simp only [CollatzResearch.WordTrace]
  refine ⟨243347831832220909435543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 324463775776294545914057 243347831832220909435543)
  ·
    refine ⟨365021747748331364153315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243347831832220909435543 365021747748331364153315)
    ·
      refine ⟨547532621622497046229973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365021747748331364153315 547532621622497046229973)
      ·
        refine ⟨12832795819277274521015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 547532621622497046229973 12832795819277274521015)
        ·
          refine ⟨19249193728915911781523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832795819277274521015 19249193728915911781523)
          ·
            refine ⟨28873790593373867672285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19249193728915911781523 28873790593373867672285)
            ·
              refine ⟨10827671472515200377107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28873790593373867672285 10827671472515200377107)
              ·
                refine ⟨16241507208772800565661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10827671472515200377107 16241507208772800565661)
                ·
                  refine ⟨6090565203289800212123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16241507208772800565661 6090565203289800212123)
                  ·
                    rfl

theorem cell20_13344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_13344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13344 prefixEnd_13344 := by exact prefixLift 13344
  have htrace : WordTrace (prefixWord ++ tailWord_13344) baseStart_13344 baseEnd_13344 := by
    simpa [prefixWord, tailWord_13344, baseEnd_13344] using wordTrace_append hprefix tailTrace_13344
  have hstable : (prefixWord ++ tailWord_13344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13344).length < 2 ^ (prefixWord ++ tailWord_13344).sum := by decide
  have hdescent : baseEnd_13344 < baseStart_13344 := by decide
  rcases family_descends (prefixWord ++ tailWord_13344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13369 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_13369 : Nat := 118140960795 + 13369 * 2 ^ 59
def prefixEnd_13369 : Nat := 4983230072969 + 3 ^ 40 * 13369 * 2
def baseEnd_13369 : Nat := 6101975884500824378687

theorem tailTrace_13369 : CollatzResearch.WordTrace tailWord_13369 prefixEnd_13369 6101975884500824378687 := by
  unfold tailWord_13369
  simp only [CollatzResearch.WordTrace]
  refine ⟨487607488573871088531161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 325071659049247392354107 487607488573871088531161)
  ·
    refine ⟨365705616430403316398371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 487607488573871088531161 365705616430403316398371)
    ·
      refine ⟨548558424645604974597557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365705616430403316398371 548558424645604974597557)
      ·
        refine ⟨51427352310525466368521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 548558424645604974597557 51427352310525466368521)
        ·
          refine ⟨38570514232894099776391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51427352310525466368521 38570514232894099776391)
          ·
            refine ⟨57855771349341149664587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38570514232894099776391 57855771349341149664587)
            ·
              refine ⟨86783657024011724496881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57855771349341149664587 86783657024011724496881)
              ·
                refine ⟨65087742768008793372661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86783657024011724496881 65087742768008793372661)
                ·
                  refine ⟨6101975884500824378687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65087742768008793372661 6101975884500824378687)
                  ·
                    rfl

theorem cell20_13369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_13369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13369 prefixEnd_13369 := by exact prefixLift 13369
  have htrace : WordTrace (prefixWord ++ tailWord_13369) baseStart_13369 baseEnd_13369 := by
    simpa [prefixWord, tailWord_13369, baseEnd_13369] using wordTrace_append hprefix tailTrace_13369
  have hstable : (prefixWord ++ tailWord_13369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13369).length < 2 ^ (prefixWord ++ tailWord_13369).sum := by decide
  have hdescent : baseEnd_13369 < baseStart_13369 := by decide
  rcases family_descends (prefixWord ++ tailWord_13369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13372 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_13372 : Nat := 118140960795 + 13372 * 2 ^ 59
def prefixEnd_13372 : Nat := 4983230072969 + 3 ^ 40 * 13372 * 2
def baseEnd_13372 : Nat := 6103345166246147278675

theorem tailTrace_13372 : CollatzResearch.WordTrace tailWord_13372 prefixEnd_13372 6103345166246147278675 := by
  unfold tailWord_13372
  simp only [CollatzResearch.WordTrace]
  refine ⟨243858453781501300445185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 325144605042001733926913 243858453781501300445185)
  ·
    refine ⟨182893840336125975333889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243858453781501300445185 182893840336125975333889)
    ·
      refine ⟨137170380252094481500417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182893840336125975333889 137170380252094481500417)
      ·
        refine ⟨102877785189070861125313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137170380252094481500417 102877785189070861125313)
        ·
          refine ⟨77158338891803145843985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102877785189070861125313 77158338891803145843985)
          ·
            refine ⟨57868754168852359382989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77158338891803145843985 57868754168852359382989)
            ·
              refine ⟨21700782813319634768621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57868754168852359382989 21700782813319634768621)
              ·
                refine ⟨8137793554994863038233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21700782813319634768621 8137793554994863038233)
                ·
                  refine ⟨6103345166246147278675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137793554994863038233 6103345166246147278675)
                  ·
                    rfl

theorem cell20_13372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_13372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13372 prefixEnd_13372 := by exact prefixLift 13372
  have htrace : WordTrace (prefixWord ++ tailWord_13372) baseStart_13372 baseEnd_13372 := by
    simpa [prefixWord, tailWord_13372, baseEnd_13372] using wordTrace_append hprefix tailTrace_13372
  have hstable : (prefixWord ++ tailWord_13372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13372).length < 2 ^ (prefixWord ++ tailWord_13372).sum := by decide
  have hdescent : baseEnd_13372 < baseStart_13372 := by decide
  rcases family_descends (prefixWord ++ tailWord_13372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13383 : List Nat := [1, 1, 4, 1, 3, 2, 8]
def baseStart_13383 : Nat := 118140960795 + 13383 * 2 ^ 59
def prefixEnd_13383 : Nat := 4983230072969 + 3 ^ 40 * 13383 * 2
def baseEnd_13383 : Nat := 678707318442110879107

theorem tailTrace_13383 : CollatzResearch.WordTrace tailWord_13383 prefixEnd_13383 678707318442110879107 := by
  unfold tailWord_13383
  simp only [CollatzResearch.WordTrace]
  refine ⟨488118110523151479540803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 325412073682100986360535 488118110523151479540803)
  ·
    refine ⟨732177165784727219311205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488118110523151479540803 732177165784727219311205)
    ·
      refine ⟨137283218584636353620851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 732177165784727219311205 137283218584636353620851)
      ·
        refine ⟨205924827876954530431277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137283218584636353620851 205924827876954530431277)
        ·
          refine ⟨77221810453857948911729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205924827876954530431277 77221810453857948911729)
          ·
            refine ⟨57916357840393461683797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77221810453857948911729 57916357840393461683797)
            ·
              refine ⟨678707318442110879107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57916357840393461683797 678707318442110879107)
              ·
                rfl

theorem cell20_13383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_13383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13383 prefixEnd_13383 := by exact prefixLift 13383
  have htrace : WordTrace (prefixWord ++ tailWord_13383) baseStart_13383 baseEnd_13383 := by
    simpa [prefixWord, tailWord_13383, baseEnd_13383] using wordTrace_append hprefix tailTrace_13383
  have hstable : (prefixWord ++ tailWord_13383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13383).length < 2 ^ (prefixWord ++ tailWord_13383).sum := by decide
  have hdescent : baseEnd_13383 < baseStart_13383 := by decide
  rcases family_descends (prefixWord ++ tailWord_13383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13393 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 2]
def baseStart_13393 : Nat := 118140960795 + 13393 * 2 ^ 59
def prefixEnd_13393 : Nat := 4983230072969 + 3 ^ 40 * 13393 * 2
def baseEnd_13393 : Nat := 6112930138463407578589

theorem tailTrace_13393 : CollatzResearch.WordTrace tailWord_13393 prefixEnd_13393 6112930138463407578589 := by
  unfold tailWord_13393
  simp only [CollatzResearch.WordTrace]
  refine ⟨488482840486923187404833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 325655226991282124936555 488482840486923187404833)
  ·
    refine ⟨366362130365192390553625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 488482840486923187404833 366362130365192390553625)
    ·
      refine ⟨274771597773894292915219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366362130365192390553625 274771597773894292915219)
      ·
        refine ⟨412157396660841439372829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274771597773894292915219 412157396660841439372829)
        ·
          refine ⟨154559023747815539764811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412157396660841439372829 154559023747815539764811)
          ·
            refine ⟨231838535621723309647217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154559023747815539764811 231838535621723309647217)
            ·
              refine ⟨173878901716292482235413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231838535621723309647217 173878901716292482235413)
              ·
                refine ⟨8150573517951210104785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173878901716292482235413 8150573517951210104785)
                ·
                  refine ⟨6112930138463407578589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8150573517951210104785 6112930138463407578589)
                  ·
                    rfl

theorem cell20_13393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_13393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13393 prefixEnd_13393 := by exact prefixLift 13393
  have htrace : WordTrace (prefixWord ++ tailWord_13393) baseStart_13393 baseEnd_13393 := by
    simpa [prefixWord, tailWord_13393, baseEnd_13393] using wordTrace_append hprefix tailTrace_13393
  have hstable : (prefixWord ++ tailWord_13393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13393).length < 2 ^ (prefixWord ++ tailWord_13393).sum := by decide
  have hdescent : baseEnd_13393 < baseStart_13393 := by decide
  rcases family_descends (prefixWord ++ tailWord_13393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13407 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_13407 : Nat := 118140960795 + 13407 * 2 ^ 59
def prefixEnd_13407 : Nat := 4983230072969 + 3 ^ 40 * 13407 * 2
def baseEnd_13407 : Nat := 6119320119941581111865

theorem tailTrace_13407 : CollatzResearch.WordTrace tailWord_13407 prefixEnd_13407 6119320119941581111865 := by
  unfold tailWord_13407
  simp only [CollatzResearch.WordTrace]
  refine ⟨488993462436203578414475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 325995641624135718942983 488993462436203578414475)
  ·
    refine ⟨733490193654305367621713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488993462436203578414475 733490193654305367621713)
    ·
      refine ⟨550117645240729025716285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 733490193654305367621713 550117645240729025716285)
      ·
        refine ⟨206294116965273384643607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550117645240729025716285 206294116965273384643607)
        ·
          refine ⟨309441175447910076965411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206294116965273384643607 309441175447910076965411)
          ·
            refine ⟨464161763171865115448117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309441175447910076965411 464161763171865115448117)
            ·
              refine ⟨43515165297362354573261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 464161763171865115448117 43515165297362354573261)
              ·
                refine ⟨16318186986510882964973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43515165297362354573261 16318186986510882964973)
                ·
                  refine ⟨6119320119941581111865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16318186986510882964973 6119320119941581111865)
                  ·
                    rfl

theorem cell20_13407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_13407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13407 prefixEnd_13407 := by exact prefixLift 13407
  have htrace : WordTrace (prefixWord ++ tailWord_13407) baseStart_13407 baseEnd_13407 := by
    simpa [prefixWord, tailWord_13407, baseEnd_13407] using wordTrace_append hprefix tailTrace_13407
  have hstable : (prefixWord ++ tailWord_13407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13407).length < 2 ^ (prefixWord ++ tailWord_13407).sum := by decide
  have hdescent : baseEnd_13407 < baseStart_13407 := by decide
  rcases family_descends (prefixWord ++ tailWord_13407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13431 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 2]
def baseStart_13431 : Nat := 118140960795 + 13431 * 2 ^ 59
def prefixEnd_13431 : Nat := 4983230072969 + 3 ^ 40 * 13431 * 2
def baseEnd_13431 : Nat := 6130274373904164311767

theorem tailTrace_13431 : CollatzResearch.WordTrace tailWord_13431 prefixEnd_13431 6130274373904164311767 := by
  unfold tailWord_13431
  simp only [CollatzResearch.WordTrace]
  refine ⟨489868814349255677288147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 326579209566170451525431 489868814349255677288147)
  ·
    refine ⟨734803221523883515932221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 489868814349255677288147 734803221523883515932221)
    ·
      refine ⟨275551208071456318474583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 734803221523883515932221 275551208071456318474583)
      ·
        refine ⟨413326812107184477711875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275551208071456318474583 413326812107184477711875)
        ·
          refine ⟨619990218160776716567813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413326812107184477711875 619990218160776716567813)
          ·
            refine ⟨116248165905145634356465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 619990218160776716567813 116248165905145634356465)
            ·
              refine ⟨87186124428859225767349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116248165905145634356465 87186124428859225767349)
              ·
                refine ⟨8173699165205552415689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87186124428859225767349 8173699165205552415689)
                ·
                  refine ⟨6130274373904164311767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173699165205552415689 6130274373904164311767)
                  ·
                    rfl

theorem cell20_13431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2].length) (baseStart_13431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13431 prefixEnd_13431 := by exact prefixLift 13431
  have htrace : WordTrace (prefixWord ++ tailWord_13431) baseStart_13431 baseEnd_13431 := by
    simpa [prefixWord, tailWord_13431, baseEnd_13431] using wordTrace_append hprefix tailTrace_13431
  have hstable : (prefixWord ++ tailWord_13431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13431).length < 2 ^ (prefixWord ++ tailWord_13431).sum := by decide
  have hdescent : baseEnd_13431 < baseStart_13431 := by decide
  rcases family_descends (prefixWord ++ tailWord_13431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13459 : List Nat := [1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_13459 : Nat := 118140960795 + 13459 * 2 ^ 59
def prefixEnd_13459 : Nat := 4983230072969 + 3 ^ 40 * 13459 * 2
def baseEnd_13459 : Nat := 2047684778953503792773

theorem tailTrace_13459 : CollatzResearch.WordTrace tailWord_13459 prefixEnd_13459 2047684778953503792773 := by
  unfold tailWord_13459
  simp only [CollatzResearch.WordTrace]
  refine ⟨490890058247816459307431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 327260038831877639538287 490890058247816459307431)
  ·
    refine ⟨736335087371724688961147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 490890058247816459307431 736335087371724688961147)
    ·
      refine ⟨1104502631057587033441721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736335087371724688961147 1104502631057587033441721)
      ·
        refine ⟨828376973293190275081291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104502631057587033441721 828376973293190275081291)
        ·
          refine ⟨1242565459939785412621937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828376973293190275081291 1242565459939785412621937)
          ·
            refine ⟨931924094954839059466453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242565459939785412621937 931924094954839059466453)
            ·
              refine ⟨21841970975504040456245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 931924094954839059466453 21841970975504040456245)
              ·
                refine ⟨2047684778953503792773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21841970975504040456245 2047684778953503792773)
                ·
                  rfl

theorem cell20_13459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_13459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13459 prefixEnd_13459 := by exact prefixLift 13459
  have htrace : WordTrace (prefixWord ++ tailWord_13459) baseStart_13459 baseEnd_13459 := by
    simpa [prefixWord, tailWord_13459, baseEnd_13459] using wordTrace_append hprefix tailTrace_13459
  have hstable : (prefixWord ++ tailWord_13459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13459).length < 2 ^ (prefixWord ++ tailWord_13459).sum := by decide
  have hdescent : baseEnd_13459 < baseStart_13459 := by decide
  rcases family_descends (prefixWord ++ tailWord_13459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13497 : List Nat := [1, 2, 1, 4, 1, 4, 7]
def baseStart_13497 : Nat := 118140960795 + 13497 * 2 ^ 59
def prefixEnd_13497 : Nat := 4983230072969 + 3 ^ 40 * 13497 * 2
def baseEnd_13497 : Nat := 684488730255696456833

theorem tailTrace_13497 : CollatzResearch.WordTrace tailWord_13497 prefixEnd_13497 684488730255696456833 := by
  unfold tailWord_13497
  simp only [CollatzResearch.WordTrace]
  refine ⟨492276032110148949190745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 328184021406765966127163 492276032110148949190745)
  ·
    refine ⟨369207024082611711893059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 492276032110148949190745 369207024082611711893059)
    ·
      refine ⟨553810536123917567839589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369207024082611711893059 553810536123917567839589)
      ·
        refine ⟨103839475523234543969923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 553810536123917567839589 103839475523234543969923)
        ·
          refine ⟨155759213284851815954885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103839475523234543969923 155759213284851815954885)
          ·
            refine ⟨29204852490909715491541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155759213284851815954885 29204852490909715491541)
            ·
              refine ⟨684488730255696456833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29204852490909715491541 684488730255696456833)
              ·
                rfl

theorem cell20_13497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_13497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13497 prefixEnd_13497 := by exact prefixLift 13497
  have htrace : WordTrace (prefixWord ++ tailWord_13497) baseStart_13497 baseEnd_13497 := by
    simpa [prefixWord, tailWord_13497, baseEnd_13497] using wordTrace_append hprefix tailTrace_13497
  have hstable : (prefixWord ++ tailWord_13497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13497).length < 2 ^ (prefixWord ++ tailWord_13497).sum := by decide
  have hdescent : baseEnd_13497 < baseStart_13497 := by decide
  rcases family_descends (prefixWord ++ tailWord_13497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13500 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_13500 : Nat := 118140960795 + 13500 * 2 ^ 59
def prefixEnd_13500 : Nat := 4983230072969 + 3 ^ 40 * 13500 * 2
def baseEnd_13500 : Nat := 6161767854046591011485

theorem tailTrace_13500 : CollatzResearch.WordTrace tailWord_13500 prefixEnd_13500 6161767854046591011485 := by
  unfold tailWord_13500
  simp only [CollatzResearch.WordTrace]
  refine ⟨246192725549640230774977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 328256967399520307699969 246192725549640230774977)
  ·
    refine ⟨184644544162230173081233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246192725549640230774977 184644544162230173081233)
    ·
      refine ⟨138483408121672629810925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184644544162230173081233 138483408121672629810925)
      ·
        refine ⟨51931278045627236179097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138483408121672629810925 51931278045627236179097)
        ·
          refine ⟨38948458534220427134323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51931278045627236179097 38948458534220427134323)
          ·
            refine ⟨58422687801330640701485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38948458534220427134323 58422687801330640701485)
            ·
              refine ⟨21908507925498990263057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58422687801330640701485 21908507925498990263057)
              ·
                refine ⟨16431380944124242697293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21908507925498990263057 16431380944124242697293)
                ·
                  refine ⟨6161767854046591011485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16431380944124242697293 6161767854046591011485)
                  ·
                    rfl

theorem cell20_13500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_13500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13500 prefixEnd_13500 := by exact prefixLift 13500
  have htrace : WordTrace (prefixWord ++ tailWord_13500) baseStart_13500 baseEnd_13500 := by
    simpa [prefixWord, tailWord_13500, baseEnd_13500] using wordTrace_append hprefix tailTrace_13500
  have hstable : (prefixWord ++ tailWord_13500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13500).length < 2 ^ (prefixWord ++ tailWord_13500).sum := by decide
  have hdescent : baseEnd_13500 < baseStart_13500 := by decide
  rcases family_descends (prefixWord ++ tailWord_13500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13541 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 2]
def baseStart_13541 : Nat := 118140960795 + 13541 * 2 ^ 59
def prefixEnd_13541 : Nat := 4983230072969 + 3 ^ 40 * 13541 * 2
def baseEnd_13541 : Nat := 6180481371232670644651

theorem tailTrace_13541 : CollatzResearch.WordTrace tailWord_13541 prefixEnd_13541 6180481371232670644651 := by
  unfold tailWord_13541
  simp only [CollatzResearch.WordTrace]
  refine ⟨493880843950744463792477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 329253895967162975861651 493880843950744463792477)
  ·
    refine ⟨185205316481529173922179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 493880843950744463792477 185205316481529173922179)
    ·
      refine ⟨277807974722293760883269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185205316481529173922179 277807974722293760883269)
      ·
        refine ⟨52088995260430080165613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277807974722293760883269 52088995260430080165613)
        ·
          refine ⟨19533373222661280062105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52088995260430080165613 19533373222661280062105)
          ·
            refine ⟨14650029916995960046579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19533373222661280062105 14650029916995960046579)
            ·
              refine ⟨21975044875493940069869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14650029916995960046579 21975044875493940069869)
              ·
                refine ⟨8240641828310227526201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21975044875493940069869 8240641828310227526201)
                ·
                  refine ⟨6180481371232670644651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240641828310227526201 6180481371232670644651)
                  ·
                    rfl

theorem cell20_13541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_13541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13541 prefixEnd_13541 := by exact prefixLift 13541
  have htrace : WordTrace (prefixWord ++ tailWord_13541) baseStart_13541 baseEnd_13541 := by
    simpa [prefixWord, tailWord_13541, baseEnd_13541] using wordTrace_append hprefix tailTrace_13541
  have hstable : (prefixWord ++ tailWord_13541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13541).length < 2 ^ (prefixWord ++ tailWord_13541).sum := by decide
  have hdescent : baseEnd_13541 < baseStart_13541 := by decide
  rcases family_descends (prefixWord ++ tailWord_13541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13562 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_13562 : Nat := 118140960795 + 13562 * 2 ^ 59
def prefixEnd_13562 : Nat := 4983230072969 + 3 ^ 40 * 13562 * 2
def baseEnd_13562 : Nat := 6190066343449930944565

theorem tailTrace_13562 : CollatzResearch.WordTrace tailWord_13562 prefixEnd_13562 6190066343449930944565 := by
  unfold tailWord_13562
  simp only [CollatzResearch.WordTrace]
  refine ⟨123661694218666262576735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 329764517916443366871293 123661694218666262576735)
  ·
    refine ⟨185492541327999393865103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123661694218666262576735 185492541327999393865103)
    ·
      refine ⟨278238811991999090797655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185492541327999393865103 278238811991999090797655)
      ·
        refine ⟨417358217987998636196483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278238811991999090797655 417358217987998636196483)
        ·
          refine ⟨626037326981997954294725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417358217987998636196483 626037326981997954294725)
          ·
            refine ⟨117381998809124616430261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 626037326981997954294725 117381998809124616430261)
            ·
              refine ⟨11004562388355432790337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117381998809124616430261 11004562388355432790337)
              ·
                refine ⟨8253421791266574592753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11004562388355432790337 8253421791266574592753)
                ·
                  refine ⟨6190066343449930944565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8253421791266574592753 6190066343449930944565)
                  ·
                    rfl

theorem cell20_13562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_13562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13562 prefixEnd_13562 := by exact prefixLift 13562
  have htrace : WordTrace (prefixWord ++ tailWord_13562) baseStart_13562 baseEnd_13562 := by
    simpa [prefixWord, tailWord_13562, baseEnd_13562] using wordTrace_append hprefix tailTrace_13562
  have hstable : (prefixWord ++ tailWord_13562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13562).length < 2 ^ (prefixWord ++ tailWord_13562).sum := by decide
  have hdescent : baseEnd_13562 < baseStart_13562 := by decide
  rcases family_descends (prefixWord ++ tailWord_13562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13573 : List Nat := [1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_13573 : Nat := 118140960795 + 13573 * 2 ^ 59
def prefixEnd_13573 : Nat := 4983230072969 + 3 ^ 40 * 13573 * 2
def baseEnd_13573 : Nat := 2065029014394260525951

theorem tailTrace_13573 : CollatzResearch.WordTrace tailWord_13573 prefixEnd_13573 2065029014394260525951 := by
  unfold tailWord_13573
  simp only [CollatzResearch.WordTrace]
  refine ⟨495047979834813928957373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 330031986556542619304915 495047979834813928957373)
  ·
    refine ⟨185642992438055223359015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 495047979834813928957373 185642992438055223359015)
    ·
      refine ⟨278464488657082835038523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185642992438055223359015 278464488657082835038523)
      ·
        refine ⟨417696732985624252557785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278464488657082835038523 417696732985624252557785)
        ·
          refine ⟨313272549739218189418339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417696732985624252557785 313272549739218189418339)
          ·
            refine ⟨469908824608827284127509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313272549739218189418339 469908824608827284127509)
            ·
              refine ⟨22026976153538778943477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 469908824608827284127509 22026976153538778943477)
              ·
                refine ⟨2065029014394260525951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22026976153538778943477 2065029014394260525951)
                ·
                  rfl

theorem cell20_13573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_13573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13573 prefixEnd_13573 := by exact prefixLift 13573
  have htrace : WordTrace (prefixWord ++ tailWord_13573) baseStart_13573 baseEnd_13573 := by
    simpa [prefixWord, tailWord_13573, baseEnd_13573] using wordTrace_append hprefix tailTrace_13573
  have hstable : (prefixWord ++ tailWord_13573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13573).length < 2 ^ (prefixWord ++ tailWord_13573).sum := by decide
  have hdescent : baseEnd_13573 < baseStart_13573 := by decide
  rcases family_descends (prefixWord ++ tailWord_13573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13576 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_13576 : Nat := 118140960795 + 13576 * 2 ^ 59
def prefixEnd_13576 : Nat := 4983230072969 + 3 ^ 40 * 13576 * 2
def baseEnd_13576 : Nat := 6196456324928104477841

theorem tailTrace_13576 : CollatzResearch.WordTrace tailWord_13576 prefixEnd_13576 6196456324928104477841 := by
  unfold tailWord_13576
  simp only [CollatzResearch.WordTrace]
  refine ⟨247578699411972720658291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 330104932549296960877721 247578699411972720658291)
  ·
    refine ⟨371368049117959080987437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247578699411972720658291 371368049117959080987437)
    ·
      refine ⟨139263018419234655370289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371368049117959080987437 139263018419234655370289)
      ·
        refine ⟨104447263814425991527717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139263018419234655370289 104447263814425991527717)
        ·
          refine ⟨19583861965204873411447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104447263814425991527717 19583861965204873411447)
          ·
            refine ⟨29375792947807310117171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19583861965204873411447 29375792947807310117171)
            ·
              refine ⟨44063689421710965175757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29375792947807310117171 44063689421710965175757)
              ·
                refine ⟨16523883533141611940909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44063689421710965175757 16523883533141611940909)
                ·
                  refine ⟨6196456324928104477841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16523883533141611940909 6196456324928104477841)
                  ·
                    rfl

theorem cell20_13576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_13576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13576 prefixEnd_13576 := by exact prefixLift 13576
  have htrace : WordTrace (prefixWord ++ tailWord_13576) baseStart_13576 baseEnd_13576 := by
    simpa [prefixWord, tailWord_13576, baseEnd_13576] using wordTrace_append hprefix tailTrace_13576
  have hstable : (prefixWord ++ tailWord_13576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13576).length < 2 ^ (prefixWord ++ tailWord_13576).sum := by decide
  have hdescent : baseEnd_13576 < baseStart_13576 := by decide
  rcases family_descends (prefixWord ++ tailWord_13576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13617 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 2]
def baseStart_13617 : Nat := 118140960795 + 13617 * 2 ^ 59
def prefixEnd_13617 : Nat := 4983230072969 + 3 ^ 40 * 13617 * 2
def baseEnd_13617 : Nat := 6215169842114184111007

theorem tailTrace_13617 : CollatzResearch.WordTrace tailWord_13617 prefixEnd_13617 6215169842114184111007 := by
  unfold tailWord_13617
  simp only [CollatzResearch.WordTrace]
  refine ⟨496652791675409443559105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 331101861116939629039403 496652791675409443559105)
  ·
    refine ⟨372489593756557082669329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 496652791675409443559105 372489593756557082669329)
    ·
      refine ⟨279367195317417812001997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372489593756557082669329 279367195317417812001997)
      ·
        refine ⟨104762698244031679500749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279367195317417812001997 104762698244031679500749)
        ·
          refine ⟨39286011841511879812781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104762698244031679500749 39286011841511879812781)
          ·
            refine ⟨14732254440566954929793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39286011841511879812781 14732254440566954929793)
            ·
              refine ⟨11049190830425216197345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14732254440566954929793 11049190830425216197345)
              ·
                refine ⟨8286893122818912148009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11049190830425216197345 8286893122818912148009)
                ·
                  refine ⟨6215169842114184111007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8286893122818912148009 6215169842114184111007)
                  ·
                    rfl

theorem cell20_13617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_13617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13617 prefixEnd_13617 := by exact prefixLift 13617
  have htrace : WordTrace (prefixWord ++ tailWord_13617) baseStart_13617 baseEnd_13617 := by
    simpa [prefixWord, tailWord_13617, baseEnd_13617] using wordTrace_append hprefix tailTrace_13617
  have hstable : (prefixWord ++ tailWord_13617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13617).length < 2 ^ (prefixWord ++ tailWord_13617).sum := by decide
  have hdescent : baseEnd_13617 < baseStart_13617 := by decide
  rcases family_descends (prefixWord ++ tailWord_13617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13628 : List Nat := [2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_13628 : Nat := 118140960795 + 13628 * 2 ^ 59
def prefixEnd_13628 : Nat := 4983230072969 + 3 ^ 40 * 13628 * 2
def baseEnd_13628 : Nat := 2073396847282344914765

theorem tailTrace_13628 : CollatzResearch.WordTrace tailWord_13628 prefixEnd_13628 2073396847282344914765 := by
  unfold tailWord_13628
  simp only [CollatzResearch.WordTrace]
  refine ⟨248526997317779161104769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 331369329757038881473025 248526997317779161104769)
  ·
    refine ⟨186395247988334370828577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248526997317779161104769 186395247988334370828577)
    ·
      refine ⟨139796435991250778121433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186395247988334370828577 139796435991250778121433)
      ·
        refine ⟨104847326993438083591075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139796435991250778121433 104847326993438083591075)
        ·
          refine ⟨157270990490157125386613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104847326993438083591075 157270990490157125386613)
          ·
            refine ⟨14744155358452230504995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157270990490157125386613 14744155358452230504995)
            ·
              refine ⟨22116233037678345757493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14744155358452230504995 22116233037678345757493)
              ·
                refine ⟨2073396847282344914765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22116233037678345757493 2073396847282344914765)
                ·
                  rfl

theorem cell20_13628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_13628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13628 prefixEnd_13628 := by exact prefixLift 13628
  have htrace : WordTrace (prefixWord ++ tailWord_13628) baseStart_13628 baseEnd_13628 := by
    simpa [prefixWord, tailWord_13628, baseEnd_13628] using wordTrace_append hprefix tailTrace_13628
  have hstable : (prefixWord ++ tailWord_13628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13628).length < 2 ^ (prefixWord ++ tailWord_13628).sum := by decide
  have hdescent : baseEnd_13628 < baseStart_13628 := by decide
  rcases family_descends (prefixWord ++ tailWord_13628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13656 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_13656 : Nat := 118140960795 + 13656 * 2 ^ 59
def prefixEnd_13656 : Nat := 4983230072969 + 3 ^ 40 * 13656 * 2
def baseEnd_13656 : Nat := 6232970504803381810847

theorem tailTrace_13656 : CollatzResearch.WordTrace tailWord_13656 prefixEnd_13656 6232970504803381810847 := by
  unfold tailWord_13656
  simp only [CollatzResearch.WordTrace]
  refine ⟨249037619267059552114411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 332050159022746069485881 249037619267059552114411)
  ·
    refine ⟨373556428900589328171617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249037619267059552114411 373556428900589328171617)
    ·
      refine ⟨280167321675441996128713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373556428900589328171617 280167321675441996128713)
      ·
        refine ⟨210125491256581497096535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280167321675441996128713 210125491256581497096535)
        ·
          refine ⟨315188236884872245644803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210125491256581497096535 315188236884872245644803)
          ·
            refine ⟨472782355327308368467205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315188236884872245644803 472782355327308368467205)
            ·
              refine ⟨88646691623870319087601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 472782355327308368467205 88646691623870319087601)
              ·
                refine ⟨66485018717902739315701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88646691623870319087601 66485018717902739315701)
                ·
                  refine ⟨6232970504803381810847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66485018717902739315701 6232970504803381810847)
                  ·
                    rfl

theorem cell20_13656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_13656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13656 prefixEnd_13656 := by exact prefixLift 13656
  have htrace : WordTrace (prefixWord ++ tailWord_13656) baseStart_13656 baseEnd_13656 := by
    simpa [prefixWord, tailWord_13656, baseEnd_13656] using wordTrace_append hprefix tailTrace_13656
  have hstable : (prefixWord ++ tailWord_13656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13656).length < 2 ^ (prefixWord ++ tailWord_13656).sum := by decide
  have hdescent : baseEnd_13656 < baseStart_13656 := by decide
  rcases family_descends (prefixWord ++ tailWord_13656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13663 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_13663 : Nat := 118140960795 + 13663 * 2 ^ 59
def prefixEnd_13663 : Nat := 4983230072969 + 3 ^ 40 * 13663 * 2
def baseEnd_13663 : Nat := 6236165495542468577485

theorem tailTrace_13663 : CollatzResearch.WordTrace tailWord_13663 prefixEnd_13663 6236165495542468577485 := by
  unfold tailWord_13663
  simp only [CollatzResearch.WordTrace]
  refine ⟨498330549508759299733643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 332220366339172866489095 498330549508759299733643)
  ·
    refine ⟨747495824263138949600465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 498330549508759299733643 747495824263138949600465)
    ·
      refine ⟨560621868197354212200349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 747495824263138949600465 560621868197354212200349)
      ·
        refine ⟨210233200574007829575131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560621868197354212200349 210233200574007829575131)
        ·
          refine ⟨315349800861011744362697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210233200574007829575131 315349800861011744362697)
          ·
            refine ⟨236512350645758808272023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315349800861011744362697 236512350645758808272023)
            ·
              refine ⟨354768525968638212408035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236512350645758808272023 354768525968638212408035)
              ·
                refine ⟨532152788952957318612053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354768525968638212408035 532152788952957318612053)
                ·
                  refine ⟨6236165495542468577485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 532152788952957318612053 6236165495542468577485)
                  ·
                    rfl

theorem cell20_13663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_13663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13663 prefixEnd_13663 := by exact prefixLift 13663
  have htrace : WordTrace (prefixWord ++ tailWord_13663) baseStart_13663 baseEnd_13663 := by
    simpa [prefixWord, tailWord_13663, baseEnd_13663] using wordTrace_append hprefix tailTrace_13663
  have hstable : (prefixWord ++ tailWord_13663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13663).length < 2 ^ (prefixWord ++ tailWord_13663).sum := by decide
  have hdescent : baseEnd_13663 < baseStart_13663 := by decide
  rcases family_descends (prefixWord ++ tailWord_13663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13680 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_13680 : Nat := 118140960795 + 13680 * 2 ^ 59
def prefixEnd_13680 : Nat := 4983230072969 + 3 ^ 40 * 13680 * 2
def baseEnd_13680 : Nat := 6243924758765965010749

theorem tailTrace_13680 : CollatzResearch.WordTrace tailWord_13680 prefixEnd_13680 6243924758765965010749 := by
  unfold tailWord_13680
  simp only [CollatzResearch.WordTrace]
  refine ⟨249475295223585601551247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 332633726964780802068329 249475295223585601551247)
  ·
    refine ⟨374212942835378402326871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249475295223585601551247 374212942835378402326871)
    ·
      refine ⟨561319414253067603490307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374212942835378402326871 561319414253067603490307)
      ·
        refine ⟨841979121379601405235461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561319414253067603490307 841979121379601405235461)
        ·
          refine ⟨157871085258675263481649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 841979121379601405235461 157871085258675263481649)
          ·
            refine ⟨118403313944006447611237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157871085258675263481649 118403313944006447611237)
            ·
              refine ⟨22200621364501208927107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118403313944006447611237 22200621364501208927107)
              ·
                refine ⟨33300932046751813390661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22200621364501208927107 33300932046751813390661)
                ·
                  refine ⟨6243924758765965010749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33300932046751813390661 6243924758765965010749)
                  ·
                    rfl

theorem cell20_13680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_13680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13680 prefixEnd_13680 := by exact prefixLift 13680
  have htrace : WordTrace (prefixWord ++ tailWord_13680) baseStart_13680 baseEnd_13680 := by
    simpa [prefixWord, tailWord_13680, baseEnd_13680] using wordTrace_append hprefix tailTrace_13680
  have hstable : (prefixWord ++ tailWord_13680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13680).length < 2 ^ (prefixWord ++ tailWord_13680).sum := by decide
  have hdescent : baseEnd_13680 < baseStart_13680 := by decide
  rcases family_descends (prefixWord ++ tailWord_13680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13704 : List Nat := [2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_13704 : Nat := 118140960795 + 13704 * 2 ^ 59
def prefixEnd_13704 : Nat := 4983230072969 + 3 ^ 40 * 13704 * 2
def baseEnd_13704 : Nat := 2084959670909516070217

theorem tailTrace_13704 : CollatzResearch.WordTrace tailWord_13704 prefixEnd_13704 2084959670909516070217 := by
  unfold tailWord_13704
  simp only [CollatzResearch.WordTrace]
  refine ⟨249912971180111650988083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 333217294906815534650777 249912971180111650988083)
  ·
    refine ⟨374869456770167476482125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249912971180111650988083 374869456770167476482125)
    ·
      refine ⟨140576046288812803680797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374869456770167476482125 140576046288812803680797)
      ·
        refine ⟨52716017358304801380299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140576046288812803680797 52716017358304801380299)
        ·
          refine ⟨79074026037457202070449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52716017358304801380299 79074026037457202070449)
          ·
            refine ⟨59305519528092901552837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79074026037457202070449 59305519528092901552837)
            ·
              refine ⟨11119784911517419041157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59305519528092901552837 11119784911517419041157)
              ·
                refine ⟨2084959670909516070217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11119784911517419041157 2084959670909516070217)
                ·
                  rfl

theorem cell20_13704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_13704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13704 prefixEnd_13704 := by exact prefixLift 13704
  have htrace : WordTrace (prefixWord ++ tailWord_13704) baseStart_13704 baseEnd_13704 := by
    simpa [prefixWord, tailWord_13704, baseEnd_13704] using wordTrace_append hprefix tailTrace_13704
  have hstable : (prefixWord ++ tailWord_13704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13704).length < 2 ^ (prefixWord ++ tailWord_13704).sum := by decide
  have hdescent : baseEnd_13704 < baseStart_13704 := by decide
  rcases family_descends (prefixWord ++ tailWord_13704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13710 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_13710 : Nat := 118140960795 + 13710 * 2 ^ 59
def prefixEnd_13710 : Nat := 4983230072969 + 3 ^ 40 * 13710 * 2
def baseEnd_13710 : Nat := 6257617576219194010627

theorem tailTrace_13710 : CollatzResearch.WordTrace tailWord_13710 prefixEnd_13710 6257617576219194010627 := by
  unfold tailWord_13710
  simp only [CollatzResearch.WordTrace]
  refine ⟨62505597542310790836823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 333363186892324217796389 62505597542310790836823)
  ·
    refine ⟨93758396313466186255235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62505597542310790836823 93758396313466186255235)
    ·
      refine ⟨140637594470199279382853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93758396313466186255235 140637594470199279382853)
      ·
        refine ⟨26369548963162364884285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140637594470199279382853 26369548963162364884285)
        ·
          refine ⟨9888580861185886831607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26369548963162364884285 9888580861185886831607)
          ·
            refine ⟨14832871291778830247411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9888580861185886831607 14832871291778830247411)
            ·
              refine ⟨22249306937668245371117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14832871291778830247411 22249306937668245371117)
              ·
                refine ⟨8343490101625592014169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22249306937668245371117 8343490101625592014169)
                ·
                  refine ⟨6257617576219194010627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343490101625592014169 6257617576219194010627)
                  ·
                    rfl

theorem cell20_13710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_13710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13710 prefixEnd_13710 := by exact prefixLift 13710
  have htrace : WordTrace (prefixWord ++ tailWord_13710) baseStart_13710 baseEnd_13710 := by
    simpa [prefixWord, tailWord_13710, baseEnd_13710] using wordTrace_append hprefix tailTrace_13710
  have hstable : (prefixWord ++ tailWord_13710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13710).length < 2 ^ (prefixWord ++ tailWord_13710).sum := by decide
  have hdescent : baseEnd_13710 < baseStart_13710 := by decide
  rcases family_descends (prefixWord ++ tailWord_13710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13725 : List Nat := [1, 4, 2, 1, 3, 1, 8]
def baseStart_13725 : Nat := 118140960795 + 13725 * 2 ^ 59
def prefixEnd_13725 : Nat := 4983230072969 + 3 ^ 40 * 13725 * 2
def baseEnd_13725 : Nat := 696051553882867612285

theorem tailTrace_13725 : CollatzResearch.WordTrace tailWord_13725 prefixEnd_13725 696051553882867612285 := by
  unfold tailWord_13725
  simp only [CollatzResearch.WordTrace]
  refine ⟨500591875284143888490629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 333727916856095925660419 500591875284143888490629)
  ·
    refine ⟨93860976615776979091993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 500591875284143888490629 93860976615776979091993)
    ·
      refine ⟨70395732461832734318995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93860976615776979091993 70395732461832734318995)
      ·
        refine ⟨105593598692749101478493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70395732461832734318995 105593598692749101478493)
        ·
          refine ⟨39597599509780913054435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105593598692749101478493 39597599509780913054435)
          ·
            refine ⟨59396399264671369581653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39597599509780913054435 59396399264671369581653)
            ·
              refine ⟨696051553882867612285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 59396399264671369581653 696051553882867612285)
              ·
                rfl

theorem cell20_13725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_13725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13725 prefixEnd_13725 := by exact prefixLift 13725
  have htrace : WordTrace (prefixWord ++ tailWord_13725) baseStart_13725 baseEnd_13725 := by
    simpa [prefixWord, tailWord_13725, baseEnd_13725] using wordTrace_append hprefix tailTrace_13725
  have hstable : (prefixWord ++ tailWord_13725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13725).length < 2 ^ (prefixWord ++ tailWord_13725).sum := by decide
  have hdescent : baseEnd_13725 < baseStart_13725 := by decide
  rcases family_descends (prefixWord ++ tailWord_13725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13780 : List Nat := [2, 4, 1, 2, 4, 7]
def baseStart_13780 : Nat := 118140960795 + 13780 * 2 ^ 59
def prefixEnd_13780 : Nat := 4983230072969 + 3 ^ 40 * 13780 * 2
def baseEnd_13780 : Nat := 232946943837409691741

theorem tailTrace_13780 : CollatzResearch.WordTrace tailWord_13780 prefixEnd_13780 232946943837409691741 := by
  unfold tailWord_13780
  simp only [CollatzResearch.WordTrace]
  refine ⟨251298945042444140871397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 335065260056592187828529 251298945042444140871397)
  ·
    refine ⟨47118552195458276413387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251298945042444140871397 47118552195458276413387)
    ·
      refine ⟨70677828293187414620081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47118552195458276413387 70677828293187414620081)
      ·
        refine ⟨53008371219890560965061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70677828293187414620081 53008371219890560965061)
        ·
          refine ⟨9939069603729480180949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53008371219890560965061 9939069603729480180949)
          ·
            refine ⟨232946943837409691741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9939069603729480180949 232946943837409691741)
            ·
              rfl

theorem cell20_13780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 7].length) (baseStart_13780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13780 prefixEnd_13780 := by exact prefixLift 13780
  have htrace : WordTrace (prefixWord ++ tailWord_13780) baseStart_13780 baseEnd_13780 := by
    simpa [prefixWord, tailWord_13780, baseEnd_13780] using wordTrace_append hprefix tailTrace_13780
  have hstable : (prefixWord ++ tailWord_13780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13780).length < 2 ^ (prefixWord ++ tailWord_13780).sum := by decide
  have hdescent : baseEnd_13780 < baseStart_13780 := by decide
  rcases family_descends (prefixWord ++ tailWord_13780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13877 : List Nat := [1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_13877 : Nat := 118140960795 + 13877 * 2 ^ 59
def prefixEnd_13877 : Nat := 4983230072969 + 3 ^ 40 * 13877 * 2
def baseEnd_13877 : Nat := 2111280308902945147759

theorem tailTrace_13877 : CollatzResearch.WordTrace tailWord_13877 prefixEnd_13877 2111280308902945147759 := by
  unfold tailWord_13877
  simp only [CollatzResearch.WordTrace]
  refine ⟨506135770733473848023885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 337423847155649232015923 506135770733473848023885)
  ·
    refine ⟨189800914025052693008957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 506135770733473848023885 189800914025052693008957)
    ·
      refine ⟨71175342759394759878359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189800914025052693008957 71175342759394759878359)
      ·
        refine ⟨106763014139092139817539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71175342759394759878359 106763014139092139817539)
        ·
          refine ⟨160144521208638209726309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106763014139092139817539 160144521208638209726309)
          ·
            refine ⟨30027097726619664323683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160144521208638209726309 30027097726619664323683)
            ·
              refine ⟨45040646589929496485525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30027097726619664323683 45040646589929496485525)
              ·
                refine ⟨2111280308902945147759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45040646589929496485525 2111280308902945147759)
                ·
                  rfl

theorem cell20_13877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_13877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13877 prefixEnd_13877 := by exact prefixLift 13877
  have htrace : WordTrace (prefixWord ++ tailWord_13877) baseStart_13877 baseEnd_13877 := by
    simpa [prefixWord, tailWord_13877, baseEnd_13877] using wordTrace_append hprefix tailTrace_13877
  have hstable : (prefixWord ++ tailWord_13877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13877).length < 2 ^ (prefixWord ++ tailWord_13877).sum := by decide
  have hdescent : baseEnd_13877 < baseStart_13877 := by decide
  rcases family_descends (prefixWord ++ tailWord_13877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13887 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 2]
def baseStart_13887 : Nat := 118140960795 + 13887 * 2 ^ 59
def prefixEnd_13887 : Nat := 4983230072969 + 3 ^ 40 * 13887 * 2
def baseEnd_13887 : Nat := 6338405199193245109903

theorem tailTrace_13887 : CollatzResearch.WordTrace tailWord_13887 prefixEnd_13887 6338405199193245109903 := by
  unfold tailWord_13887
  simp only [CollatzResearch.WordTrace]
  refine ⟨506500500697245555887915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 337667000464830370591943 506500500697245555887915)
  ·
    refine ⟨759750751045868333831873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506500500697245555887915 759750751045868333831873)
    ·
      refine ⟨569813063284401250373905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759750751045868333831873 569813063284401250373905)
      ·
        refine ⟨427359797463300937780429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569813063284401250373905 427359797463300937780429)
        ·
          refine ⟨160259924048737851667661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427359797463300937780429 160259924048737851667661)
          ·
            refine ⟨60097471518276694375373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160259924048737851667661 60097471518276694375373)
            ·
              refine ⟨22536551819353760390765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60097471518276694375373 22536551819353760390765)
              ·
                refine ⟨8451206932257660146537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22536551819353760390765 8451206932257660146537)
                ·
                  refine ⟨6338405199193245109903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451206932257660146537 6338405199193245109903)
                  ·
                    rfl

theorem cell20_13887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2].length) (baseStart_13887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13887 prefixEnd_13887 := by exact prefixLift 13887
  have htrace : WordTrace (prefixWord ++ tailWord_13887) baseStart_13887 baseEnd_13887 := by
    simpa [prefixWord, tailWord_13887, baseEnd_13887] using wordTrace_append hprefix tailTrace_13887
  have hstable : (prefixWord ++ tailWord_13887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13887).length < 2 ^ (prefixWord ++ tailWord_13887).sum := by decide
  have hdescent : baseEnd_13887 < baseStart_13887 := by decide
  rcases family_descends (prefixWord ++ tailWord_13887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13910 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_13910 : Nat := 118140960795 + 13910 * 2 ^ 59
def prefixEnd_13910 : Nat := 4983230072969 + 3 ^ 40 * 13910 * 2
def baseEnd_13910 : Nat := 6348903025907387343143

theorem tailTrace_13910 : CollatzResearch.WordTrace tailWord_13910 prefixEnd_13910 6348903025907387343143 := by
  unfold tailWord_13910
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708711225870030248449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 338226253075946989316789 31708711225870030248449)
  ·
    refine ⟨23781533419402522686337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31708711225870030248449 23781533419402522686337)
    ·
      refine ⟨17836150064551892014753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23781533419402522686337 17836150064551892014753)
      ·
        refine ⟨13377112548413919011065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17836150064551892014753 13377112548413919011065)
        ·
          refine ⟨10032834411310439258299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13377112548413919011065 10032834411310439258299)
          ·
            refine ⟨15049251616965658887449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10032834411310439258299 15049251616965658887449)
            ·
              refine ⟨11286938712724244165587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15049251616965658887449 11286938712724244165587)
              ·
                refine ⟨16930408069086366248381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286938712724244165587 16930408069086366248381)
                ·
                  refine ⟨6348903025907387343143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16930408069086366248381 6348903025907387343143)
                  ·
                    rfl

theorem cell20_13910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_13910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13910 prefixEnd_13910 := by exact prefixLift 13910
  have htrace : WordTrace (prefixWord ++ tailWord_13910) baseStart_13910 baseEnd_13910 := by
    simpa [prefixWord, tailWord_13910, baseEnd_13910] using wordTrace_append hprefix tailTrace_13910
  have hstable : (prefixWord ++ tailWord_13910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13910).length < 2 ^ (prefixWord ++ tailWord_13910).sum := by decide
  have hdescent : baseEnd_13910 < baseStart_13910 := by decide
  rcases family_descends (prefixWord ++ tailWord_13910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13929 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_13929 : Nat := 118140960795 + 13929 * 2 ^ 59
def prefixEnd_13929 : Nat := 4983230072969 + 3 ^ 40 * 13929 * 2
def baseEnd_13929 : Nat := 6357575143627765709731

theorem tailTrace_13929 : CollatzResearch.WordTrace tailWord_13929 prefixEnd_13929 6357575143627765709731 := by
  unfold tailWord_13929
  simp only [CollatzResearch.WordTrace]
  refine ⟨508032366545086728916841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 338688244363391152611227 508032366545086728916841)
  ·
    refine ⟨381024274908815046687631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 508032366545086728916841 381024274908815046687631)
    ·
      refine ⟨571536412363222570031447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381024274908815046687631 571536412363222570031447)
      ·
        refine ⟨857304618544833855047171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571536412363222570031447 857304618544833855047171)
        ·
          refine ⟨1285956927817250782570757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857304618544833855047171 1285956927817250782570757)
          ·
            refine ⟨241116923965734521732017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1285956927817250782570757 241116923965734521732017)
            ·
              refine ⟨180837692974300891299013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241116923965734521732017 180837692974300891299013)
              ·
                refine ⟨33907067432681417118565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180837692974300891299013 33907067432681417118565)
                ·
                  refine ⟨6357575143627765709731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33907067432681417118565 6357575143627765709731)
                  ·
                    rfl

theorem cell20_13929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_13929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13929 prefixEnd_13929 := by exact prefixLift 13929
  have htrace : WordTrace (prefixWord ++ tailWord_13929) baseStart_13929 baseEnd_13929 := by
    simpa [prefixWord, tailWord_13929, baseEnd_13929] using wordTrace_append hprefix tailTrace_13929
  have hstable : (prefixWord ++ tailWord_13929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13929).length < 2 ^ (prefixWord ++ tailWord_13929).sum := by decide
  have hdescent : baseEnd_13929 < baseStart_13929 := by decide
  rcases family_descends (prefixWord ++ tailWord_13929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13956 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_13956 : Nat := 118140960795 + 13956 * 2 ^ 59
def prefixEnd_13956 : Nat := 4983230072969 + 3 ^ 40 * 13956 * 2
def baseEnd_13956 : Nat := 6369898679335671809621

theorem tailTrace_13956 : CollatzResearch.WordTrace tailWord_13956 prefixEnd_13956 6369898679335671809621 := by
  unfold tailWord_13956
  simp only [CollatzResearch.WordTrace]
  refine ⟨254508568723635170074861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 339344758298180226766481 254508568723635170074861)
  ·
    refine ⟨95440713271363188778073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254508568723635170074861 95440713271363188778073)
    ·
      refine ⟨71580534953522391583555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95440713271363188778073 71580534953522391583555)
      ·
        refine ⟨107370802430283587375333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71580534953522391583555 107370802430283587375333)
        ·
          refine ⟨20132025455678172632875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107370802430283587375333 20132025455678172632875)
          ·
            refine ⟨30198038183517258949313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20132025455678172632875 30198038183517258949313)
            ·
              refine ⟨22648528637637944211985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30198038183517258949313 22648528637637944211985)
              ·
                refine ⟨16986396478228458158989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22648528637637944211985 16986396478228458158989)
                ·
                  refine ⟨6369898679335671809621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16986396478228458158989 6369898679335671809621)
                  ·
                    rfl

theorem cell20_13956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_13956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13956 prefixEnd_13956 := by exact prefixLift 13956
  have htrace : WordTrace (prefixWord ++ tailWord_13956) baseStart_13956 baseEnd_13956 := by
    simpa [prefixWord, tailWord_13956, baseEnd_13956] using wordTrace_append hprefix tailTrace_13956
  have hstable : (prefixWord ++ tailWord_13956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13956).length < 2 ^ (prefixWord ++ tailWord_13956).sum := by decide
  have hdescent : baseEnd_13956 < baseStart_13956 := by decide
  rcases family_descends (prefixWord ++ tailWord_13956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13984 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_13984 : Nat := 118140960795 + 13984 * 2 ^ 59
def prefixEnd_13984 : Nat := 4983230072969 + 3 ^ 40 * 13984 * 2
def baseEnd_13984 : Nat := 6382678642292018876173

theorem tailTrace_13984 : CollatzResearch.WordTrace tailWord_13984 prefixEnd_13984 6382678642292018876173 := by
  unfold tailWord_13984
  simp only [CollatzResearch.WordTrace]
  refine ⟨255019190672915561084503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 340025587563887414779337 255019190672915561084503)
  ·
    refine ⟨382528786009373341626755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255019190672915561084503 382528786009373341626755)
    ·
      refine ⟨573793179014060012440133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382528786009373341626755 573793179014060012440133)
      ·
        refine ⟨107586221065136252332525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 573793179014060012440133 107586221065136252332525)
        ·
          refine ⟨40344832899426094624697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107586221065136252332525 40344832899426094624697)
          ·
            refine ⟨30258624674569570968523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40344832899426094624697 30258624674569570968523)
            ·
              refine ⟨45387937011854356452785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30258624674569570968523 45387937011854356452785)
              ·
                refine ⟨34040952758890767339589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45387937011854356452785 34040952758890767339589)
                ·
                  refine ⟨6382678642292018876173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34040952758890767339589 6382678642292018876173)
                  ·
                    rfl

theorem cell20_13984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_13984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_13984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_13984 prefixEnd_13984 := by exact prefixLift 13984
  have htrace : WordTrace (prefixWord ++ tailWord_13984) baseStart_13984 baseEnd_13984 := by
    simpa [prefixWord, tailWord_13984, baseEnd_13984] using wordTrace_append hprefix tailTrace_13984
  have hstable : (prefixWord ++ tailWord_13984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13984).length < 2 ^ (prefixWord ++ tailWord_13984).sum := by decide
  have hdescent : baseEnd_13984 < baseStart_13984 := by decide
  rcases family_descends (prefixWord ++ tailWord_13984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14056 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_14056 : Nat := 118140960795 + 14056 * 2 ^ 59
def prefixEnd_14056 : Nat := 4983230072969 + 3 ^ 40 * 14056 * 2
def baseEnd_14056 : Nat := 6415541404179768475879

theorem tailTrace_14056 : CollatzResearch.WordTrace tailWord_14056 prefixEnd_14056 6415541404179768475879 := by
  unfold tailWord_14056
  simp only [CollatzResearch.WordTrace]
  refine ⟨256332218542493709395011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 341776291389991612526681 256332218542493709395011)
  ·
    refine ⟨384498327813740564092517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256332218542493709395011 384498327813740564092517)
    ·
      refine ⟨72093436465076355767347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384498327813740564092517 72093436465076355767347)
      ·
        refine ⟨108140154697614533651021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72093436465076355767347 108140154697614533651021)
        ·
          refine ⟨40552558011605450119133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108140154697614533651021 40552558011605450119133)
          ·
            refine ⟨15207209254352043794675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40552558011605450119133 15207209254352043794675)
            ·
              refine ⟨22810813881528065692013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15207209254352043794675 22810813881528065692013)
              ·
                refine ⟨8554055205573024634505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22810813881528065692013 8554055205573024634505)
                ·
                  refine ⟨6415541404179768475879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554055205573024634505 6415541404179768475879)
                  ·
                    rfl

theorem cell20_14056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_14056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14056 prefixEnd_14056 := by exact prefixLift 14056
  have htrace : WordTrace (prefixWord ++ tailWord_14056) baseStart_14056 baseEnd_14056 := by
    simpa [prefixWord, tailWord_14056, baseEnd_14056] using wordTrace_append hprefix tailTrace_14056
  have hstable : (prefixWord ++ tailWord_14056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14056).length < 2 ^ (prefixWord ++ tailWord_14056).sum := by decide
  have hdescent : baseEnd_14056 < baseStart_14056 := by decide
  rcases family_descends (prefixWord ++ tailWord_14056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14074 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_14074 : Nat := 118140960795 + 14074 * 2 ^ 59
def prefixEnd_14074 : Nat := 4983230072969 + 3 ^ 40 * 14074 * 2
def baseEnd_14074 : Nat := 6423757094651705875805

theorem tailTrace_14074 : CollatzResearch.WordTrace tailWord_14074 prefixEnd_14074 6423757094651705875805 := by
  unfold tailWord_14074
  simp only [CollatzResearch.WordTrace]
  refine ⟨128330237754944123236319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 342213967346517661963517 128330237754944123236319)
  ·
    refine ⟨192495356632416184854479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128330237754944123236319 192495356632416184854479)
    ·
      refine ⟨288743034948624277281719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192495356632416184854479 288743034948624277281719)
      ·
        refine ⟨433114552422936415922579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288743034948624277281719 433114552422936415922579)
        ·
          refine ⟨649671828634404623883869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433114552422936415922579 649671828634404623883869)
          ·
            refine ⟨243626935737901733956451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649671828634404623883869 243626935737901733956451)
            ·
              refine ⟨365440403606852600934677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243626935737901733956451 365440403606852600934677)
              ·
                refine ⟨17130018919071215668813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365440403606852600934677 17130018919071215668813)
                ·
                  refine ⟨6423757094651705875805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17130018919071215668813 6423757094651705875805)
                  ·
                    rfl

theorem cell20_14074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_14074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14074 prefixEnd_14074 := by exact prefixLift 14074
  have htrace : WordTrace (prefixWord ++ tailWord_14074) baseStart_14074 baseEnd_14074 := by
    simpa [prefixWord, tailWord_14074, baseEnd_14074] using wordTrace_append hprefix tailTrace_14074
  have hstable : (prefixWord ++ tailWord_14074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14074).length < 2 ^ (prefixWord ++ tailWord_14074).sum := by decide
  have hdescent : baseEnd_14074 < baseStart_14074 := by decide
  rcases family_descends (prefixWord ++ tailWord_14074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14087 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 3]
def baseStart_14087 : Nat := 118140960795 + 14087 * 2 ^ 59
def prefixEnd_14087 : Nat := 4983230072969 + 3 ^ 40 * 14087 * 2
def baseEnd_14087 : Nat := 6429690648881438442419

theorem tailTrace_14087 : CollatzResearch.WordTrace tailWord_14087 prefixEnd_14087 6429690648881438442419 := by
  unfold tailWord_14087
  simp only [CollatzResearch.WordTrace]
  refine ⟨513795099972679713168515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 342530066648453142112343 513795099972679713168515)
  ·
    refine ⟨770692649959019569752773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513795099972679713168515 770692649959019569752773)
    ·
      refine ⟨144504871867316169328645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 770692649959019569752773 144504871867316169328645)
      ·
        refine ⟨27094663475121781749121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144504871867316169328645 27094663475121781749121)
        ·
          refine ⟨20320997606341336311841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27094663475121781749121 20320997606341336311841)
          ·
            refine ⟨15240748204756002233881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20320997606341336311841 15240748204756002233881)
            ·
              refine ⟨11430561153567001675411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15240748204756002233881 11430561153567001675411)
              ·
                refine ⟨17145841730350502513117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11430561153567001675411 17145841730350502513117)
                ·
                  refine ⟨6429690648881438442419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17145841730350502513117 6429690648881438442419)
                  ·
                    rfl

theorem cell20_14087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_14087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14087 prefixEnd_14087 := by exact prefixLift 14087
  have htrace : WordTrace (prefixWord ++ tailWord_14087) baseStart_14087 baseEnd_14087 := by
    simpa [prefixWord, tailWord_14087, baseEnd_14087] using wordTrace_append hprefix tailTrace_14087
  have hstable : (prefixWord ++ tailWord_14087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14087).length < 2 ^ (prefixWord ++ tailWord_14087).sum := by decide
  have hdescent : baseEnd_14087 < baseStart_14087 := by decide
  rcases family_descends (prefixWord ++ tailWord_14087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14091 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 3]
def baseStart_14091 : Nat := 118140960795 + 14091 * 2 ^ 59
def prefixEnd_14091 : Nat := 4983230072969 + 3 ^ 40 * 14091 * 2
def baseEnd_14091 : Nat := 6431516357875202309069

theorem tailTrace_14091 : CollatzResearch.WordTrace tailWord_14091 prefixEnd_14091 6431516357875202309069 := by
  unfold tailWord_14091
  simp only [CollatzResearch.WordTrace]
  refine ⟨513940991958188396314127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 342627327972125597542751 513940991958188396314127)
  ·
    refine ⟨770911487937282594471191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513940991958188396314127 770911487937282594471191)
    ·
      refine ⟨1156367231905923891706787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770911487937282594471191 1156367231905923891706787)
      ·
        refine ⟨1734550847858885837560181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156367231905923891706787 1734550847858885837560181)
        ·
          refine ⟨162614141986770547271267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1734550847858885837560181 162614141986770547271267)
          ·
            refine ⟨243921212980155820906901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162614141986770547271267 243921212980155820906901)
            ·
              refine ⟨11433806858444804105011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243921212980155820906901 11433806858444804105011)
              ·
                refine ⟨17150710287667206157517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11433806858444804105011 17150710287667206157517)
                ·
                  refine ⟨6431516357875202309069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17150710287667206157517 6431516357875202309069)
                  ·
                    rfl

theorem cell20_14091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_14091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14091 prefixEnd_14091 := by exact prefixLift 14091
  have htrace : WordTrace (prefixWord ++ tailWord_14091) baseStart_14091 baseEnd_14091 := by
    simpa [prefixWord, tailWord_14091, baseEnd_14091] using wordTrace_append hprefix tailTrace_14091
  have hstable : (prefixWord ++ tailWord_14091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14091).length < 2 ^ (prefixWord ++ tailWord_14091).sum := by decide
  have hdescent : baseEnd_14091 < baseStart_14091 := by decide
  rcases family_descends (prefixWord ++ tailWord_14091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14095 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_14095 : Nat := 118140960795 + 14095 * 2 ^ 59
def prefixEnd_14095 : Nat := 4983230072969 + 3 ^ 40 * 14095 * 2
def baseEnd_14095 : Nat := 6433342066868966175719

theorem tailTrace_14095 : CollatzResearch.WordTrace tailWord_14095 prefixEnd_14095 6433342066868966175719 := by
  unfold tailWord_14095
  simp only [CollatzResearch.WordTrace]
  refine ⟨514086883943697079459739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 342724589295798052973159 514086883943697079459739)
  ·
    refine ⟨771130325915545619189609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514086883943697079459739 771130325915545619189609)
    ·
      refine ⟨578347744436659214392207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 771130325915545619189609 578347744436659214392207)
      ·
        refine ⟨867521616654988821588311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578347744436659214392207 867521616654988821588311)
        ·
          refine ⟨1301282424982483232382467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867521616654988821588311 1301282424982483232382467)
          ·
            refine ⟨1951923637473724848573701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301282424982483232382467 1951923637473724848573701)
            ·
              refine ⟨365985682026323409107569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1951923637473724848573701 365985682026323409107569)
              ·
                refine ⟨274489261519742556830677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365985682026323409107569 274489261519742556830677)
                ·
                  refine ⟨6433342066868966175719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 274489261519742556830677 6433342066868966175719)
                  ·
                    rfl

theorem cell20_14095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_14095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14095 prefixEnd_14095 := by exact prefixLift 14095
  have htrace : WordTrace (prefixWord ++ tailWord_14095) baseStart_14095 baseEnd_14095 := by
    simpa [prefixWord, tailWord_14095, baseEnd_14095] using wordTrace_append hprefix tailTrace_14095
  have hstable : (prefixWord ++ tailWord_14095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14095).length < 2 ^ (prefixWord ++ tailWord_14095).sum := by decide
  have hdescent : baseEnd_14095 < baseStart_14095 := by decide
  rcases family_descends (prefixWord ++ tailWord_14095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14129 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_14129 : Nat := 118140960795 + 14129 * 2 ^ 59
def prefixEnd_14129 : Nat := 4983230072969 + 3 ^ 40 * 14129 * 2
def baseEnd_14129 : Nat := 6448860593315959042247

theorem tailTrace_14129 : CollatzResearch.WordTrace tailWord_14129 prefixEnd_14129 6448860593315959042247 := by
  unfold tailWord_14129
  simp only [CollatzResearch.WordTrace]
  refine ⟨515326965820520886197441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 343551310547013924131627 515326965820520886197441)
  ·
    refine ⟨386495224365390664648081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 515326965820520886197441 386495224365390664648081)
    ·
      refine ⟨289871418274042998486061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386495224365390664648081 289871418274042998486061)
      ·
        refine ⟨108701781852766124432273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289871418274042998486061 108701781852766124432273)
        ·
          refine ⟨81526336389574593324205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108701781852766124432273 81526336389574593324205)
          ·
            refine ⟨30572376146090472496577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81526336389574593324205 30572376146090472496577)
            ·
              refine ⟨22929282109567854372433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30572376146090472496577 22929282109567854372433)
              ·
                refine ⟨17196961582175890779325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22929282109567854372433 17196961582175890779325)
                ·
                  refine ⟨6448860593315959042247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17196961582175890779325 6448860593315959042247)
                  ·
                    rfl

theorem cell20_14129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_14129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14129 prefixEnd_14129 := by exact prefixLift 14129
  have htrace : WordTrace (prefixWord ++ tailWord_14129) baseStart_14129 baseEnd_14129 := by
    simpa [prefixWord, tailWord_14129, baseEnd_14129] using wordTrace_append hprefix tailTrace_14129
  have hstable : (prefixWord ++ tailWord_14129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14129).length < 2 ^ (prefixWord ++ tailWord_14129).sum := by decide
  have hdescent : baseEnd_14129 < baseStart_14129 := by decide
  rcases family_descends (prefixWord ++ tailWord_14129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14132 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_14132 : Nat := 118140960795 + 14132 * 2 ^ 59
def prefixEnd_14132 : Nat := 4983230072969 + 3 ^ 40 * 14132 * 2
def baseEnd_14132 : Nat := 6450229875061281942235

theorem tailTrace_14132 : CollatzResearch.WordTrace tailWord_14132 prefixEnd_14132 6450229875061281942235 := by
  unfold tailWord_14132
  simp only [CollatzResearch.WordTrace]
  refine ⟨257718192404826199278325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 343624256539768265704433 257718192404826199278325)
  ·
    refine ⟨24161080537952456182343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257718192404826199278325 24161080537952456182343)
    ·
      refine ⟨36241620806928684273515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24161080537952456182343 36241620806928684273515)
      ·
        refine ⟨54362431210393026410273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36241620806928684273515 54362431210393026410273)
        ·
          refine ⟨40771823407794769807705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54362431210393026410273 40771823407794769807705)
          ·
            refine ⟨30578867555846077355779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40771823407794769807705 30578867555846077355779)
            ·
              refine ⟨45868301333769116033669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30578867555846077355779 45868301333769116033669)
              ·
                refine ⟨8600306500081709256313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45868301333769116033669 8600306500081709256313)
                ·
                  refine ⟨6450229875061281942235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600306500081709256313 6450229875061281942235)
                  ·
                    rfl

theorem cell20_14132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_14132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14132 prefixEnd_14132 := by exact prefixLift 14132
  have htrace : WordTrace (prefixWord ++ tailWord_14132) baseStart_14132 baseEnd_14132 := by
    simpa [prefixWord, tailWord_14132, baseEnd_14132] using wordTrace_append hprefix tailTrace_14132
  have hstable : (prefixWord ++ tailWord_14132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14132).length < 2 ^ (prefixWord ++ tailWord_14132).sum := by decide
  have hdescent : baseEnd_14132 < baseStart_14132 := by decide
  rcases family_descends (prefixWord ++ tailWord_14132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14188 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_14188 : Nat := 118140960795 + 14188 * 2 ^ 59
def prefixEnd_14188 : Nat := 4983230072969 + 3 ^ 40 * 14188 * 2
def baseEnd_14188 : Nat := 6475789800973976075339

theorem tailTrace_14188 : CollatzResearch.WordTrace tailWord_14188 prefixEnd_14188 6475789800973976075339 := by
  unfold tailWord_14188
  simp only [CollatzResearch.WordTrace]
  refine ⟨258739436303386981297609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 344985915071182641730145 258739436303386981297609)
  ·
    refine ⟨194054577227540235973207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258739436303386981297609 194054577227540235973207)
    ·
      refine ⟨291081865841310353959811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194054577227540235973207 291081865841310353959811)
      ·
        refine ⟨436622798761965530939717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291081865841310353959811 436622798761965530939717)
        ·
          refine ⟨81866774767868537051197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436622798761965530939717 81866774767868537051197)
          ·
            refine ⟨30700040537950701394199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81866774767868537051197 30700040537950701394199)
            ·
              refine ⟨46050060806926052091299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30700040537950701394199 46050060806926052091299)
              ·
                refine ⟨69075091210389078136949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46050060806926052091299 69075091210389078136949)
                ·
                  refine ⟨6475789800973976075339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69075091210389078136949 6475789800973976075339)
                  ·
                    rfl

theorem cell20_14188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_14188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14188 prefixEnd_14188 := by exact prefixLift 14188
  have htrace : WordTrace (prefixWord ++ tailWord_14188) baseStart_14188 baseEnd_14188 := by
    simpa [prefixWord, tailWord_14188, baseEnd_14188] using wordTrace_append hprefix tailTrace_14188
  have hstable : (prefixWord ++ tailWord_14188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14188).length < 2 ^ (prefixWord ++ tailWord_14188).sum := by decide
  have hdescent : baseEnd_14188 < baseStart_14188 := by decide
  rcases family_descends (prefixWord ++ tailWord_14188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14215 : List Nat := [1, 1, 4, 2, 5, 1, 2, 4]
def baseStart_14215 : Nat := 118140960795 + 14215 * 2 ^ 59
def prefixEnd_14215 : Nat := 4983230072969 + 3 ^ 40 * 14215 * 2
def baseEnd_14215 : Nat := 2162704445560627391743

theorem tailTrace_14215 : CollatzResearch.WordTrace tailWord_14215 prefixEnd_14215 2162704445560627391743 := by
  unfold tailWord_14215
  simp only [CollatzResearch.WordTrace]
  refine ⟨518463643508957573828099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 345642429005971715885399 518463643508957573828099)
  ·
    refine ⟨777695465263436360742149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 518463643508957573828099 777695465263436360742149)
    ·
      refine ⟨145817899736894317639153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 777695465263436360742149 145817899736894317639153)
      ·
        refine ⟨109363424802670738229365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145817899736894317639153 109363424802670738229365)
        ·
          refine ⟨10252821075250381709003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109363424802670738229365 10252821075250381709003)
          ·
            refine ⟨15379231612875572563505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10252821075250381709003 15379231612875572563505)
            ·
              refine ⟨11534423709656679422629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15379231612875572563505 11534423709656679422629)
              ·
                refine ⟨2162704445560627391743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11534423709656679422629 2162704445560627391743)
                ·
                  rfl

theorem cell20_14215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_14215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14215 prefixEnd_14215 := by exact prefixLift 14215
  have htrace : WordTrace (prefixWord ++ tailWord_14215) baseStart_14215 baseEnd_14215 := by
    simpa [prefixWord, tailWord_14215, baseEnd_14215] using wordTrace_append hprefix tailTrace_14215
  have hstable : (prefixWord ++ tailWord_14215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14215).length < 2 ^ (prefixWord ++ tailWord_14215).sum := by decide
  have hdescent : baseEnd_14215 < baseStart_14215 := by decide
  rcases family_descends (prefixWord ++ tailWord_14215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14257 : List Nat := [1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_14257 : Nat := 118140960795 + 14257 * 2 ^ 59
def prefixEnd_14257 : Nat := 4983230072969 + 3 ^ 40 * 14257 * 2
def baseEnd_14257 : Nat := 2169094427038800925019

theorem tailTrace_14257 : CollatzResearch.WordTrace tailWord_14257 prefixEnd_14257 2169094427038800925019 := by
  unfold tailWord_14257
  simp only [CollatzResearch.WordTrace]
  refine ⟨519995509356798746857025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 346663672904532497904683 519995509356798746857025)
  ·
    refine ⟨389996632017599060142769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 519995509356798746857025 389996632017599060142769)
    ·
      refine ⟨292497474013199295107077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389996632017599060142769 292497474013199295107077)
      ·
        refine ⟨54843276377474867832577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292497474013199295107077 54843276377474867832577)
        ·
          refine ⟨41132457283106150874433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54843276377474867832577 41132457283106150874433)
          ·
            refine ⟨30849342962329613155825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41132457283106150874433 30849342962329613155825)
            ·
              refine ⟨23137007221747209866869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30849342962329613155825 23137007221747209866869)
              ·
                refine ⟨2169094427038800925019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23137007221747209866869 2169094427038800925019)
                ·
                  rfl

theorem cell20_14257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_14257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14257 prefixEnd_14257 := by exact prefixLift 14257
  have htrace : WordTrace (prefixWord ++ tailWord_14257) baseStart_14257 baseEnd_14257 := by
    simpa [prefixWord, tailWord_14257, baseEnd_14257] using wordTrace_append hprefix tailTrace_14257
  have hstable : (prefixWord ++ tailWord_14257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14257).length < 2 ^ (prefixWord ++ tailWord_14257).sum := by decide
  have hdescent : baseEnd_14257 < baseStart_14257 := by decide
  rcases family_descends (prefixWord ++ tailWord_14257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14264 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_14264 : Nat := 118140960795 + 14264 * 2 ^ 59
def prefixEnd_14264 : Nat := 4983230072969 + 3 ^ 40 * 14264 * 2
def baseEnd_14264 : Nat := 6510478271855489541695

theorem tailTrace_14264 : CollatzResearch.WordTrace tailWord_14264 prefixEnd_14264 6510478271855489541695 := by
  unfold tailWord_14264
  simp only [CollatzResearch.WordTrace]
  refine ⟨260125410165719471180923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 346833880220959294907897 260125410165719471180923)
  ·
    refine ⟨390188115248579206771385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260125410165719471180923 390188115248579206771385)
    ·
      refine ⟨292641086436434405078539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390188115248579206771385 292641086436434405078539)
      ·
        refine ⟨438961629654651607617809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292641086436434405078539 438961629654651607617809)
        ·
          refine ⟨329221222240988705713357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438961629654651607617809 329221222240988705713357)
          ·
            refine ⟨123457958340370764642509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329221222240988705713357 123457958340370764642509)
            ·
              refine ⟨46296734377639036740941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123457958340370764642509 46296734377639036740941)
              ·
                refine ⟨17361275391614638777853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46296734377639036740941 17361275391614638777853)
                ·
                  refine ⟨6510478271855489541695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17361275391614638777853 6510478271855489541695)
                  ·
                    rfl

theorem cell20_14264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_14264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14264 prefixEnd_14264 := by exact prefixLift 14264
  have htrace : WordTrace (prefixWord ++ tailWord_14264) baseStart_14264 baseEnd_14264 := by
    simpa [prefixWord, tailWord_14264, baseEnd_14264] using wordTrace_append hprefix tailTrace_14264
  have hstable : (prefixWord ++ tailWord_14264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14264).length < 2 ^ (prefixWord ++ tailWord_14264).sum := by decide
  have hdescent : baseEnd_14264 < baseStart_14264 := by decide
  rcases family_descends (prefixWord ++ tailWord_14264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14301 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 2]
def baseStart_14301 : Nat := 118140960795 + 14301 * 2 ^ 59
def prefixEnd_14301 : Nat := 4983230072969 + 3 ^ 40 * 14301 * 2
def baseEnd_14301 : Nat := 6527366080047805308211

theorem tailTrace_14301 : CollatzResearch.WordTrace tailWord_14301 prefixEnd_14301 6527366080047805308211 := by
  unfold tailWord_14301
  simp only [CollatzResearch.WordTrace]
  refine ⟨521600321197394261458757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 347733547464929507639171 521600321197394261458757)
  ·
    refine ⟨97800060224511424023517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 521600321197394261458757 97800060224511424023517)
    ·
      refine ⟨36675022584191784008819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97800060224511424023517 36675022584191784008819)
      ·
        refine ⟨55012533876287676013229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36675022584191784008819 55012533876287676013229)
        ·
          refine ⟨20629700203607878504961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55012533876287676013229 20629700203607878504961)
          ·
            refine ⟨15472275152705908878721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20629700203607878504961 15472275152705908878721)
            ·
              refine ⟨11604206364529431659041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15472275152705908878721 11604206364529431659041)
              ·
                refine ⟨8703154773397073744281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11604206364529431659041 8703154773397073744281)
                ·
                  refine ⟨6527366080047805308211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703154773397073744281 6527366080047805308211)
                  ·
                    rfl

theorem cell20_14301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_14301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14301 prefixEnd_14301 := by exact prefixLift 14301
  have htrace : WordTrace (prefixWord ++ tailWord_14301) baseStart_14301 baseEnd_14301 := by
    simpa [prefixWord, tailWord_14301, baseEnd_14301] using wordTrace_append hprefix tailTrace_14301
  have hstable : (prefixWord ++ tailWord_14301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14301).length < 2 ^ (prefixWord ++ tailWord_14301).sum := by decide
  have hdescent : baseEnd_14301 < baseStart_14301 := by decide
  rcases family_descends (prefixWord ++ tailWord_14301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14305 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 2]
def baseStart_14305 : Nat := 118140960795 + 14305 * 2 ^ 59
def prefixEnd_14305 : Nat := 4983230072969 + 3 ^ 40 * 14305 * 2
def baseEnd_14305 : Nat := 6529191789041569174861

theorem tailTrace_14305 : CollatzResearch.WordTrace tailWord_14305 prefixEnd_14305 6529191789041569174861 := by
  unfold tailWord_14305
  simp only [CollatzResearch.WordTrace]
  refine ⟨521746213182902944604369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 347830808788601963069579 521746213182902944604369)
  ·
    refine ⟨391309659887177208453277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521746213182902944604369 391309659887177208453277)
    ·
      refine ⟨146741122457691453169979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391309659887177208453277 146741122457691453169979)
      ·
        refine ⟨220111683686537179754969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146741122457691453169979 220111683686537179754969)
        ·
          refine ⟨165083762764902884816227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220111683686537179754969 165083762764902884816227)
          ·
            refine ⟨247625644147354327224341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165083762764902884816227 247625644147354327224341)
            ·
              refine ⟨11607452069407234088641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247625644147354327224341 11607452069407234088641)
              ·
                refine ⟨8705589052055425566481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11607452069407234088641 8705589052055425566481)
                ·
                  refine ⟨6529191789041569174861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705589052055425566481 6529191789041569174861)
                  ·
                    rfl

theorem cell20_14305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_14305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14305 prefixEnd_14305 := by exact prefixLift 14305
  have htrace : WordTrace (prefixWord ++ tailWord_14305) baseStart_14305 baseEnd_14305 := by
    simpa [prefixWord, tailWord_14305, baseEnd_14305] using wordTrace_append hprefix tailTrace_14305
  have hstable : (prefixWord ++ tailWord_14305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14305).length < 2 ^ (prefixWord ++ tailWord_14305).sum := by decide
  have hdescent : baseEnd_14305 < baseStart_14305 := by decide
  rcases family_descends (prefixWord ++ tailWord_14305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14343 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 2]
def baseStart_14343 : Nat := 118140960795 + 14343 * 2 ^ 59
def prefixEnd_14343 : Nat := 4983230072969 + 3 ^ 40 * 14343 * 2
def baseEnd_14343 : Nat := 6546536024482325908039

theorem tailTrace_14343 : CollatzResearch.WordTrace tailWord_14343 prefixEnd_14343 6546536024482325908039 := by
  unfold tailWord_14343
  simp only [CollatzResearch.WordTrace]
  refine ⟨523132187045235434487683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 348754791363490289658455 523132187045235434487683)
  ·
    refine ⟨784698280567853151731525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523132187045235434487683 784698280567853151731525)
    ·
      refine ⟨147130927606472465949661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 784698280567853151731525 147130927606472465949661)
      ·
        refine ⟨55174097852427174731123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147130927606472465949661 55174097852427174731123)
        ·
          refine ⟨82761146778640762096685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55174097852427174731123 82761146778640762096685)
          ·
            refine ⟨31035430041990285786257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82761146778640762096685 31035430041990285786257)
            ·
              refine ⟨23276572531492714339693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31035430041990285786257 23276572531492714339693)
              ·
                refine ⟨8728714699309767877385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23276572531492714339693 8728714699309767877385)
                ·
                  refine ⟨6546536024482325908039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8728714699309767877385 6546536024482325908039)
                  ·
                    rfl

theorem cell20_14343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2].length) (baseStart_14343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14343 prefixEnd_14343 := by exact prefixLift 14343
  have htrace : WordTrace (prefixWord ++ tailWord_14343) baseStart_14343 baseEnd_14343 := by
    simpa [prefixWord, tailWord_14343, baseEnd_14343] using wordTrace_append hprefix tailTrace_14343
  have hstable : (prefixWord ++ tailWord_14343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14343).length < 2 ^ (prefixWord ++ tailWord_14343).sum := by decide
  have hdescent : baseEnd_14343 < baseStart_14343 := by decide
  rcases family_descends (prefixWord ++ tailWord_14343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14349 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 3]
def baseStart_14349 : Nat := 118140960795 + 14349 * 2 ^ 59
def prefixEnd_14349 : Nat := 4983230072969 + 3 ^ 40 * 14349 * 2
def baseEnd_14349 : Nat := 6549274587972971708015

theorem tailTrace_14349 : CollatzResearch.WordTrace tailWord_14349 prefixEnd_14349 6549274587972971708015 := by
  unfold tailWord_14349
  simp only [CollatzResearch.WordTrace]
  refine ⟨523351025023498459206101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 348900683348998972804067 523351025023498459206101)
  ·
    refine ⟨12266039648988245137643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 523351025023498459206101 12266039648988245137643)
    ·
      refine ⟨18399059473482367706465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12266039648988245137643 18399059473482367706465)
      ·
        refine ⟨13799294605111775779849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18399059473482367706465 13799294605111775779849)
        ·
          refine ⟨10349470953833831834887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799294605111775779849 10349470953833831834887)
          ·
            refine ⟨15524206430750747752331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10349470953833831834887 15524206430750747752331)
            ·
              refine ⟨23286309646126121628497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15524206430750747752331 23286309646126121628497)
              ·
                refine ⟨17464732234594591221373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23286309646126121628497 17464732234594591221373)
                ·
                  refine ⟨6549274587972971708015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17464732234594591221373 6549274587972971708015)
                  ·
                    rfl

theorem cell20_14349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_14349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14349 prefixEnd_14349 := by exact prefixLift 14349
  have htrace : WordTrace (prefixWord ++ tailWord_14349) baseStart_14349 baseEnd_14349 := by
    simpa [prefixWord, tailWord_14349, baseEnd_14349] using wordTrace_append hprefix tailTrace_14349
  have hstable : (prefixWord ++ tailWord_14349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14349).length < 2 ^ (prefixWord ++ tailWord_14349).sum := by decide
  have hdescent : baseEnd_14349 < baseStart_14349 := by decide
  rcases family_descends (prefixWord ++ tailWord_14349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14364 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_14364 : Nat := 118140960795 + 14364 * 2 ^ 59
def prefixEnd_14364 : Nat := 4983230072969 + 3 ^ 40 * 14364 * 2
def baseEnd_14364 : Nat := 6556120996699586207953

theorem tailTrace_14364 : CollatzResearch.WordTrace tailWord_14364 prefixEnd_14364 6556120996699586207953 := by
  unfold tailWord_14364
  simp only [CollatzResearch.WordTrace]
  refine ⟨261949059984578010501073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 349265413312770680668097 261949059984578010501073)
  ·
    refine ⟨196461794988433507875805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261949059984578010501073 196461794988433507875805)
    ·
      refine ⟨73673173120662565453427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196461794988433507875805 73673173120662565453427)
      ·
        refine ⟨110509759680993848180141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73673173120662565453427 110509759680993848180141)
        ·
          refine ⟨41441159880372693067553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110509759680993848180141 41441159880372693067553)
          ·
            refine ⟨31080869910279519800665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41441159880372693067553 31080869910279519800665)
            ·
              refine ⟨23310652432709639850499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31080869910279519800665 23310652432709639850499)
              ·
                refine ⟨34965978649064459775749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23310652432709639850499 34965978649064459775749)
                ·
                  refine ⟨6556120996699586207953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34965978649064459775749 6556120996699586207953)
                  ·
                    rfl

theorem cell20_14364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_14364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14364 prefixEnd_14364 := by exact prefixLift 14364
  have htrace : WordTrace (prefixWord ++ tailWord_14364) baseStart_14364 baseEnd_14364 := by
    simpa [prefixWord, tailWord_14364, baseEnd_14364] using wordTrace_append hprefix tailTrace_14364
  have hstable : (prefixWord ++ tailWord_14364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14364).length < 2 ^ (prefixWord ++ tailWord_14364).sum := by decide
  have hdescent : baseEnd_14364 < baseStart_14364 := by decide
  rcases family_descends (prefixWord ++ tailWord_14364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14385 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_14385 : Nat := 118140960795 + 14385 * 2 ^ 59
def prefixEnd_14385 : Nat := 4983230072969 + 3 ^ 40 * 14385 * 2
def baseEnd_14385 : Nat := 6565705968916846507867

theorem tailTrace_14385 : CollatzResearch.WordTrace tailWord_14385 prefixEnd_14385 6565705968916846507867 := by
  unfold tailWord_14385
  simp only [CollatzResearch.WordTrace]
  refine ⟨524664052893076607516609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 349776035262051071677739 524664052893076607516609)
  ·
    refine ⟨393498039669807455637457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 524664052893076607516609 393498039669807455637457)
    ·
      refine ⟨295123529752355591728093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393498039669807455637457 295123529752355591728093)
      ·
        refine ⟨110671323657133346898035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295123529752355591728093 110671323657133346898035)
        ·
          refine ⟨166006985485700020347053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110671323657133346898035 166006985485700020347053)
          ·
            refine ⟨62252619557137507630145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166006985485700020347053 62252619557137507630145)
            ·
              refine ⟨46689464667853130722609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62252619557137507630145 46689464667853130722609)
              ·
                refine ⟨35017098500889848041957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46689464667853130722609 35017098500889848041957)
                ·
                  refine ⟨6565705968916846507867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35017098500889848041957 6565705968916846507867)
                  ·
                    rfl

theorem cell20_14385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_14385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14385 prefixEnd_14385 := by exact prefixLift 14385
  have htrace : WordTrace (prefixWord ++ tailWord_14385) baseStart_14385 baseEnd_14385 := by
    simpa [prefixWord, tailWord_14385, baseEnd_14385] using wordTrace_append hprefix tailTrace_14385
  have hstable : (prefixWord ++ tailWord_14385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14385).length < 2 ^ (prefixWord ++ tailWord_14385).sum := by decide
  have hdescent : baseEnd_14385 < baseStart_14385 := by decide
  rcases family_descends (prefixWord ++ tailWord_14385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14388 : List Nat := [2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_14388 : Nat := 118140960795 + 14388 * 2 ^ 59
def prefixEnd_14388 : Nat := 4983230072969 + 3 ^ 40 * 14388 * 2
def baseEnd_14388 : Nat := 2189025083554056469285

theorem tailTrace_14388 : CollatzResearch.WordTrace tailWord_14388 prefixEnd_14388 2189025083554056469285 := by
  unfold tailWord_14388
  simp only [CollatzResearch.WordTrace]
  refine ⟨262386735941104059937909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 349848981254805413250545 262386735941104059937909)
  ·
    refine ⟨24598756494478505619179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262386735941104059937909 24598756494478505619179)
    ·
      refine ⟨36898134741717758428769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24598756494478505619179 36898134741717758428769)
      ·
        refine ⟨27673601056288318821577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36898134741717758428769 27673601056288318821577)
        ·
          refine ⟨20755200792216239116183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27673601056288318821577 20755200792216239116183)
          ·
            refine ⟨31132801188324358674275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20755200792216239116183 31132801188324358674275)
            ·
              refine ⟨46699201782486538011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31132801188324358674275 46699201782486538011413)
              ·
                refine ⟨2189025083554056469285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46699201782486538011413 2189025083554056469285)
                ·
                  rfl

theorem cell20_14388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_14388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14388 prefixEnd_14388 := by exact prefixLift 14388
  have htrace : WordTrace (prefixWord ++ tailWord_14388) baseStart_14388 baseEnd_14388 := by
    simpa [prefixWord, tailWord_14388, baseEnd_14388] using wordTrace_append hprefix tailTrace_14388
  have hstable : (prefixWord ++ tailWord_14388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14388).length < 2 ^ (prefixWord ++ tailWord_14388).sum := by decide
  have hdescent : baseEnd_14388 < baseStart_14388 := by decide
  rcases family_descends (prefixWord ++ tailWord_14388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14399 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_14399 : Nat := 118140960795 + 14399 * 2 ^ 59
def prefixEnd_14399 : Nat := 4983230072969 + 3 ^ 40 * 14399 * 2
def baseEnd_14399 : Nat := 6572095950395020041143

theorem tailTrace_14399 : CollatzResearch.WordTrace tailWord_14399 prefixEnd_14399 6572095950395020041143 := by
  unfold tailWord_14399
  simp only [CollatzResearch.WordTrace]
  refine ⟨525174674842356998526251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 350116449894904665684167 525174674842356998526251)
  ·
    refine ⟨787762012263535497789377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525174674842356998526251 787762012263535497789377)
    ·
      refine ⟨590821509197651623342033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787762012263535497789377 590821509197651623342033)
      ·
        refine ⟨443116131898238717506525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590821509197651623342033 443116131898238717506525)
        ·
          refine ⟨166168549461839519064947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443116131898238717506525 166168549461839519064947)
          ·
            refine ⟨249252824192759278597421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166168549461839519064947 249252824192759278597421)
            ·
              refine ⟨93469809072284729474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249252824192759278597421 93469809072284729474033)
              ·
                refine ⟨70102356804213547105525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93469809072284729474033 70102356804213547105525)
                ·
                  refine ⟨6572095950395020041143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70102356804213547105525 6572095950395020041143)
                  ·
                    rfl

theorem cell20_14399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_14399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14399 prefixEnd_14399 := by exact prefixLift 14399
  have htrace : WordTrace (prefixWord ++ tailWord_14399) baseStart_14399 baseEnd_14399 := by
    simpa [prefixWord, tailWord_14399, baseEnd_14399] using wordTrace_append hprefix tailTrace_14399
  have hstable : (prefixWord ++ tailWord_14399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14399).length < 2 ^ (prefixWord ++ tailWord_14399).sum := by decide
  have hdescent : baseEnd_14399 < baseStart_14399 := by decide
  rcases family_descends (prefixWord ++ tailWord_14399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14423 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_14423 : Nat := 118140960795 + 14423 * 2 ^ 59
def prefixEnd_14423 : Nat := 4983230072969 + 3 ^ 40 * 14423 * 2
def baseEnd_14423 : Nat := 6583050204357603241045

theorem tailTrace_14423 : CollatzResearch.WordTrace tailWord_14423 prefixEnd_14423 6583050204357603241045 := by
  unfold tailWord_14423
  simp only [CollatzResearch.WordTrace]
  refine ⟨526050026755409097399923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 350700017836939398266615 526050026755409097399923)
  ·
    refine ⟨789075040133113646099885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526050026755409097399923 789075040133113646099885)
    ·
      refine ⟨295903140049917617287457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 789075040133113646099885 295903140049917617287457)
      ·
        refine ⟨221927355037438212965593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295903140049917617287457 221927355037438212965593)
        ·
          refine ⟨166445516278078659724195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221927355037438212965593 166445516278078659724195)
          ·
            refine ⟨249668274417117989586293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166445516278078659724195 249668274417117989586293)
            ·
              refine ⟨23406400726604811523715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249668274417117989586293 23406400726604811523715)
              ·
                refine ⟨35109601089907217285573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23406400726604811523715 35109601089907217285573)
                ·
                  refine ⟨6583050204357603241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35109601089907217285573 6583050204357603241045)
                  ·
                    rfl

theorem cell20_14423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_14423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14423 prefixEnd_14423 := by exact prefixLift 14423
  have htrace : WordTrace (prefixWord ++ tailWord_14423) baseStart_14423 baseEnd_14423 := by
    simpa [prefixWord, tailWord_14423, baseEnd_14423] using wordTrace_append hprefix tailTrace_14423
  have hstable : (prefixWord ++ tailWord_14423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14423).length < 2 ^ (prefixWord ++ tailWord_14423).sum := by decide
  have hdescent : baseEnd_14423 < baseStart_14423 := by decide
  rcases family_descends (prefixWord ++ tailWord_14423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14429 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 3]
def baseStart_14429 : Nat := 118140960795 + 14429 * 2 ^ 59
def prefixEnd_14429 : Nat := 4983230072969 + 3 ^ 40 * 14429 * 2
def baseEnd_14429 : Nat := 6585788767848249041021

theorem tailTrace_14429 : CollatzResearch.WordTrace tailWord_14429 prefixEnd_14429 6585788767848249041021 := by
  unfold tailWord_14429
  simp only [CollatzResearch.WordTrace]
  refine ⟨526268864733672122118341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 350845909822448081412227 526268864733672122118341)
  ·
    refine ⟨98675412137563522897189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 526268864733672122118341 98675412137563522897189)
    ·
      refine ⟨18501639775793160543223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98675412137563522897189 18501639775793160543223)
      ·
        refine ⟨27752459663689740814835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501639775793160543223 27752459663689740814835)
        ·
          refine ⟨41628689495534611222253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27752459663689740814835 41628689495534611222253)
          ·
            refine ⟨15610758560825479208345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41628689495534611222253 15610758560825479208345)
            ·
              refine ⟨11708068920619109406259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15610758560825479208345 11708068920619109406259)
              ·
                refine ⟨17562103380928664109389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11708068920619109406259 17562103380928664109389)
                ·
                  refine ⟨6585788767848249041021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17562103380928664109389 6585788767848249041021)
                  ·
                    rfl

theorem cell20_14429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_14429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14429 prefixEnd_14429 := by exact prefixLift 14429
  have htrace : WordTrace (prefixWord ++ tailWord_14429) baseStart_14429 baseEnd_14429 := by
    simpa [prefixWord, tailWord_14429, baseEnd_14429] using wordTrace_append hprefix tailTrace_14429
  have hstable : (prefixWord ++ tailWord_14429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14429).length < 2 ^ (prefixWord ++ tailWord_14429).sum := by decide
  have hdescent : baseEnd_14429 < baseStart_14429 := by decide
  rcases family_descends (prefixWord ++ tailWord_14429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14474 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_14474 : Nat := 118140960795 + 14474 * 2 ^ 59
def prefixEnd_14474 : Nat := 4983230072969 + 3 ^ 40 * 14474 * 2
def baseEnd_14474 : Nat := 6606327994028092540837

theorem tailTrace_14474 : CollatzResearch.WordTrace tailWord_14474 prefixEnd_14474 6606327994028092540837 := by
  unfold tailWord_14474
  simp only [CollatzResearch.WordTrace]
  refine ⟨131977537392661201876619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 351940099713763205004317 131977537392661201876619)
  ·
    refine ⟨197966306088991802814929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131977537392661201876619 197966306088991802814929)
    ·
      refine ⟨148474729566743852111197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197966306088991802814929 148474729566743852111197)
      ·
        refine ⟨55678023587528944541699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148474729566743852111197 55678023587528944541699)
        ·
          refine ⟨83517035381293416812549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55678023587528944541699 83517035381293416812549)
          ·
            refine ⟨15659444133992515652353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83517035381293416812549 15659444133992515652353)
            ·
              refine ⟨11744583100494386739265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15659444133992515652353 11744583100494386739265)
              ·
                refine ⟨8808437325370790054449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744583100494386739265 8808437325370790054449)
                ·
                  refine ⟨6606327994028092540837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8808437325370790054449 6606327994028092540837)
                  ·
                    rfl

theorem cell20_14474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_14474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14474 prefixEnd_14474 := by exact prefixLift 14474
  have htrace : WordTrace (prefixWord ++ tailWord_14474) baseStart_14474 baseEnd_14474 := by
    simpa [prefixWord, tailWord_14474, baseEnd_14474] using wordTrace_append hprefix tailTrace_14474
  have hstable : (prefixWord ++ tailWord_14474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14474).length < 2 ^ (prefixWord ++ tailWord_14474).sum := by decide
  have hdescent : baseEnd_14474 < baseStart_14474 := by decide
  rcases family_descends (prefixWord ++ tailWord_14474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14492 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_14492 : Nat := 118140960795 + 14492 * 2 ^ 59
def prefixEnd_14492 : Nat := 4983230072969 + 3 ^ 40 * 14492 * 2
def baseEnd_14492 : Nat := 6614543684500029940763

theorem tailTrace_14492 : CollatzResearch.WordTrace tailWord_14492 prefixEnd_14492 6614543684500029940763 := by
  unfold tailWord_14492
  simp only [CollatzResearch.WordTrace]
  refine ⟨264283331752716940830865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 352377775670289254441153 264283331752716940830865)
  ·
    refine ⟨198212498814537705623149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264283331752716940830865 198212498814537705623149)
    ·
      refine ⟨74329687055451639608681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198212498814537705623149 74329687055451639608681)
      ·
        refine ⟨55747265291588729706511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74329687055451639608681 55747265291588729706511)
        ·
          refine ⟨83620897937383094559767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55747265291588729706511 83620897937383094559767)
          ·
            refine ⟨125431346906074641839651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83620897937383094559767 125431346906074641839651)
            ·
              refine ⟨188147020359111962759477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125431346906074641839651 188147020359111962759477)
              ·
                refine ⟨17638783158666746508701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188147020359111962759477 17638783158666746508701)
                ·
                  refine ⟨6614543684500029940763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17638783158666746508701 6614543684500029940763)
                  ·
                    rfl

theorem cell20_14492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_14492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14492 prefixEnd_14492 := by exact prefixLift 14492
  have htrace : WordTrace (prefixWord ++ tailWord_14492) baseStart_14492 baseEnd_14492 := by
    simpa [prefixWord, tailWord_14492, baseEnd_14492] using wordTrace_append hprefix tailTrace_14492
  have hstable : (prefixWord ++ tailWord_14492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14492).length < 2 ^ (prefixWord ++ tailWord_14492).sum := by decide
  have hdescent : baseEnd_14492 < baseStart_14492 := by decide
  rcases family_descends (prefixWord ++ tailWord_14492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14520 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_14520 : Nat := 118140960795 + 14520 * 2 ^ 59
def prefixEnd_14520 : Nat := 4983230072969 + 3 ^ 40 * 14520 * 2
def baseEnd_14520 : Nat := 6627323647456377007315

theorem tailTrace_14520 : CollatzResearch.WordTrace tailWord_14520 prefixEnd_14520 6627323647456377007315 := by
  unfold tailWord_14520
  simp only [CollatzResearch.WordTrace]
  refine ⟨264793953701997331840507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 353058604935996442454009 264793953701997331840507)
  ·
    refine ⟨397190930552995997760761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264793953701997331840507 397190930552995997760761)
    ·
      refine ⟨297893197914746998320571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397190930552995997760761 297893197914746998320571)
      ·
        refine ⟨446839796872120497480857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297893197914746998320571 446839796872120497480857)
        ·
          refine ⟨335129847654090373110643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446839796872120497480857 335129847654090373110643)
          ·
            refine ⟨502694771481135559665965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335129847654090373110643 502694771481135559665965)
            ·
              refine ⟨188510539305425834874737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502694771481135559665965 188510539305425834874737)
              ·
                refine ⟨141382904479069376156053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188510539305425834874737 141382904479069376156053)
                ·
                  refine ⟨6627323647456377007315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141382904479069376156053 6627323647456377007315)
                  ·
                    rfl

theorem cell20_14520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_14520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14520 prefixEnd_14520 := by exact prefixLift 14520
  have htrace : WordTrace (prefixWord ++ tailWord_14520) baseStart_14520 baseEnd_14520 := by
    simpa [prefixWord, tailWord_14520, baseEnd_14520] using wordTrace_append hprefix tailTrace_14520
  have hstable : (prefixWord ++ tailWord_14520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14520).length < 2 ^ (prefixWord ++ tailWord_14520).sum := by decide
  have hdescent : baseEnd_14520 < baseStart_14520 := by decide
  rcases family_descends (prefixWord ++ tailWord_14520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14526 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_14526 : Nat := 118140960795 + 14526 * 2 ^ 59
def prefixEnd_14526 : Nat := 4983230072969 + 3 ^ 40 * 14526 * 2
def baseEnd_14526 : Nat := 6630062210947022807291

theorem tailTrace_14526 : CollatzResearch.WordTrace tailWord_14526 prefixEnd_14526 6630062210947022807291 := by
  unfold tailWord_14526
  simp only [CollatzResearch.WordTrace]
  refine ⟨66225843172782211049929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 353204496921505125599621 66225843172782211049929)
  ·
    refine ⟨49669382379586658287447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66225843172782211049929 49669382379586658287447)
    ·
      refine ⟨74504073569379987431171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49669382379586658287447 74504073569379987431171)
      ·
        refine ⟨111756110354069981146757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74504073569379987431171 111756110354069981146757)
        ·
          refine ⟨20954270691388121465017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111756110354069981146757 20954270691388121465017)
          ·
            refine ⟨15715703018541091098763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20954270691388121465017 15715703018541091098763)
            ·
              refine ⟨23573554527811636648145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715703018541091098763 23573554527811636648145)
              ·
                refine ⟨17680165895858727486109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23573554527811636648145 17680165895858727486109)
                ·
                  refine ⟨6630062210947022807291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17680165895858727486109 6630062210947022807291)
                  ·
                    rfl

theorem cell20_14526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_14526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14526 prefixEnd_14526 := by exact prefixLift 14526
  have htrace : WordTrace (prefixWord ++ tailWord_14526) baseStart_14526 baseEnd_14526 := by
    simpa [prefixWord, tailWord_14526, baseEnd_14526] using wordTrace_append hprefix tailTrace_14526
  have hstable : (prefixWord ++ tailWord_14526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14526).length < 2 ^ (prefixWord ++ tailWord_14526).sum := by decide
  have hdescent : baseEnd_14526 < baseStart_14526 := by decide
  rcases family_descends (prefixWord ++ tailWord_14526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14582 : List Nat := [5, 1, 1, 1, 1, 1, 10]
def baseStart_14582 : Nat := 118140960795 + 14582 * 2 ^ 59
def prefixEnd_14582 : Nat := 4983230072969 + 3 ^ 40 * 14582 * 2
def baseEnd_14582 : Nat := 739513570762190771155

theorem tailTrace_14582 : CollatzResearch.WordTrace tailWord_14582 prefixEnd_14582 739513570762190771155 := by
  unfold tailWord_14582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33240577073711203277375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 354566155452919501625333 33240577073711203277375)
  ·
    refine ⟨49860865610566804916063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33240577073711203277375 49860865610566804916063)
    ·
      refine ⟨74791298415850207374095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49860865610566804916063 74791298415850207374095)
      ·
        refine ⟨112186947623775311061143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74791298415850207374095 112186947623775311061143)
        ·
          refine ⟨168280421435662966591715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112186947623775311061143 168280421435662966591715)
          ·
            refine ⟨252420632153494449887573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168280421435662966591715 252420632153494449887573)
            ·
              refine ⟨739513570762190771155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 252420632153494449887573 739513570762190771155)
              ·
                rfl

theorem cell20_14582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_14582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14582 prefixEnd_14582 := by exact prefixLift 14582
  have htrace : WordTrace (prefixWord ++ tailWord_14582) baseStart_14582 baseEnd_14582 := by
    simpa [prefixWord, tailWord_14582, baseEnd_14582] using wordTrace_append hprefix tailTrace_14582
  have hstable : (prefixWord ++ tailWord_14582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14582).length < 2 ^ (prefixWord ++ tailWord_14582).sum := by decide
  have hdescent : baseEnd_14582 < baseStart_14582 := by decide
  rcases family_descends (prefixWord ++ tailWord_14582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14606 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_14606 : Nat := 118140960795 + 14606 * 2 ^ 59
def prefixEnd_14606 : Nat := 4983230072969 + 3 ^ 40 * 14606 * 2
def baseEnd_14606 : Nat := 6666576390822300140297

theorem tailTrace_14606 : CollatzResearch.WordTrace tailWord_14606 prefixEnd_14606 6666576390822300140297 := by
  unfold tailWord_14606
  simp only [CollatzResearch.WordTrace]
  refine ⟨66590573136553918913959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 355149723394954234207781 66590573136553918913959)
  ·
    refine ⟨99885859704830878370939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66590573136553918913959 99885859704830878370939)
    ·
      refine ⟨149828789557246317556409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99885859704830878370939 149828789557246317556409)
      ·
        refine ⟨112371592167934738167307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149828789557246317556409 112371592167934738167307)
        ·
          refine ⟨168557388251902107250961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112371592167934738167307 168557388251902107250961)
          ·
            refine ⟨126418041188926580438221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168557388251902107250961 126418041188926580438221)
            ·
              refine ⟨47406765445847467664333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126418041188926580438221 47406765445847467664333)
              ·
                refine ⟨17777537042192800374125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47406765445847467664333 17777537042192800374125)
                ·
                  refine ⟨6666576390822300140297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17777537042192800374125 6666576390822300140297)
                  ·
                    rfl

theorem cell20_14606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_14606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14606 prefixEnd_14606 := by exact prefixLift 14606
  have htrace : WordTrace (prefixWord ++ tailWord_14606) baseStart_14606 baseEnd_14606 := by
    simpa [prefixWord, tailWord_14606, baseEnd_14606] using wordTrace_append hprefix tailTrace_14606
  have hstable : (prefixWord ++ tailWord_14606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14606).length < 2 ^ (prefixWord ++ tailWord_14606).sum := by decide
  have hdescent : baseEnd_14606 < baseStart_14606 := by decide
  rcases family_descends (prefixWord ++ tailWord_14606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14637 : List Nat := [1, 5, 3, 1, 2, 8]
def baseStart_14637 : Nat := 118140960795 + 14637 * 2 ^ 59
def prefixEnd_14637 : Nat := 4983230072969 + 3 ^ 40 * 14637 * 2
def baseEnd_14637 : Nat := 247434282797184078031

theorem tailTrace_14637 : CollatzResearch.WordTrace tailWord_14637 prefixEnd_14637 247434282797184078031 := by
  unfold tailWord_14637
  simp only [CollatzResearch.WordTrace]
  refine ⟨533855247980123645690165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 355903498653415763793443 533855247980123645690165)
  ·
    refine ⟨50048929498136591783453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 533855247980123645690165 50048929498136591783453)
    ·
      refine ⟨18768348561801221918795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50048929498136591783453 18768348561801221918795)
      ·
        refine ⟨28152522842701832878193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18768348561801221918795 28152522842701832878193)
        ·
          refine ⟨21114392132026374658645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28152522842701832878193 21114392132026374658645)
          ·
            refine ⟨247434282797184078031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 21114392132026374658645 247434282797184078031)
            ·
              rfl

theorem cell20_14637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 8].length) (baseStart_14637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14637 prefixEnd_14637 := by exact prefixLift 14637
  have htrace : WordTrace (prefixWord ++ tailWord_14637) baseStart_14637 baseEnd_14637 := by
    simpa [prefixWord, tailWord_14637, baseEnd_14637] using wordTrace_append hprefix tailTrace_14637
  have hstable : (prefixWord ++ tailWord_14637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14637).length < 2 ^ (prefixWord ++ tailWord_14637).sum := by decide
  have hdescent : baseEnd_14637 < baseStart_14637 := by decide
  rcases family_descends (prefixWord ++ tailWord_14637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14641 : List Nat := [1, 2, 2, 3, 12]
def baseStart_14641 : Nat := 118140960795 + 14641 * 2 ^ 59
def prefixEnd_14641 : Nat := 4983230072969 + 3 ^ 40 * 14641 * 2
def baseEnd_14641 : Nat := 82500633882934987327

theorem tailTrace_14641 : CollatzResearch.WordTrace tailWord_14641 prefixEnd_14641 82500633882934987327 := by
  unfold tailWord_14641
  simp only [CollatzResearch.WordTrace]
  refine ⟨534001139965632328835777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 356000759977088219223851 534001139965632328835777)
  ·
    refine ⟨400500854974224246626833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 534001139965632328835777 400500854974224246626833)
    ·
      refine ⟨300375641230668184970125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400500854974224246626833 300375641230668184970125)
      ·
        refine ⟨112640865461500569363797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300375641230668184970125 112640865461500569363797)
        ·
          refine ⟨82500633882934987327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 112640865461500569363797 82500633882934987327)
          ·
            rfl

theorem cell20_14641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 12].length) (baseStart_14641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14641 prefixEnd_14641 := by exact prefixLift 14641
  have htrace : WordTrace (prefixWord ++ tailWord_14641) baseStart_14641 baseEnd_14641 := by
    simpa [prefixWord, tailWord_14641, baseEnd_14641] using wordTrace_append hprefix tailTrace_14641
  have hstable : (prefixWord ++ tailWord_14641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14641).length < 2 ^ (prefixWord ++ tailWord_14641).sum := by decide
  have hdescent : baseEnd_14641 < baseStart_14641 := by decide
  rcases family_descends (prefixWord ++ tailWord_14641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14672 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_14672 : Nat := 118140960795 + 14672 * 2 ^ 59
def prefixEnd_14672 : Nat := 4983230072969 + 3 ^ 40 * 14672 * 2
def baseEnd_14672 : Nat := 6696700589219403940027

theorem tailTrace_14672 : CollatzResearch.WordTrace tailWord_14672 prefixEnd_14672 6696700589219403940027 := by
  unfold tailWord_14672
  simp only [CollatzResearch.WordTrace]
  refine ⟨267565901426662311607135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 356754535235549748809513 267565901426662311607135)
  ·
    refine ⟨401348852139993467410703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267565901426662311607135 401348852139993467410703)
    ·
      refine ⟨602023278209990201116055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401348852139993467410703 602023278209990201116055)
      ·
        refine ⟨903034917314985301674083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602023278209990201116055 903034917314985301674083)
        ·
          refine ⟨1354552375972477952511125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903034917314985301674083 1354552375972477952511125)
          ·
            refine ⟨63494642623709904023959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1354552375972477952511125 63494642623709904023959)
            ·
              refine ⟨95241963935564856035939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63494642623709904023959 95241963935564856035939)
              ·
                refine ⟨142862945903347284053909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95241963935564856035939 142862945903347284053909)
                ·
                  refine ⟨6696700589219403940027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142862945903347284053909 6696700589219403940027)
                  ·
                    rfl

theorem cell20_14672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_14672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14672 prefixEnd_14672 := by exact prefixLift 14672
  have htrace : WordTrace (prefixWord ++ tailWord_14672) baseStart_14672 baseEnd_14672 := by
    simpa [prefixWord, tailWord_14672, baseEnd_14672] using wordTrace_append hprefix tailTrace_14672
  have hstable : (prefixWord ++ tailWord_14672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14672).length < 2 ^ (prefixWord ++ tailWord_14672).sum := by decide
  have hdescent : baseEnd_14672 < baseStart_14672 := by decide
  rcases family_descends (prefixWord ++ tailWord_14672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14696 : List Nat := [2, 1, 4, 2, 2, 2, 7]
def baseStart_14696 : Nat := 118140960795 + 14696 * 2 ^ 59
def prefixEnd_14696 : Nat := 4983230072969 + 3 ^ 40 * 14696 * 2
def baseEnd_14696 : Nat := 745294982575776348881

theorem tailTrace_14696 : CollatzResearch.WordTrace tailWord_14696 prefixEnd_14696 745294982575776348881 := by
  unfold tailWord_14696
  simp only [CollatzResearch.WordTrace]
  refine ⟨268003577383188361043971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 357338103177584481391961 268003577383188361043971)
  ·
    refine ⟨402005366074782541565957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268003577383188361043971 402005366074782541565957)
    ·
      refine ⟨75376006139021726543617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402005366074782541565957 75376006139021726543617)
      ·
        refine ⟨56532004604266294907713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75376006139021726543617 56532004604266294907713)
        ·
          refine ⟨42399003453199721180785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56532004604266294907713 42399003453199721180785)
          ·
            refine ⟨31799252589899790885589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42399003453199721180785 31799252589899790885589)
            ·
              refine ⟨745294982575776348881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31799252589899790885589 745294982575776348881)
              ·
                rfl

theorem cell20_14696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_14696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14696 prefixEnd_14696 := by exact prefixLift 14696
  have htrace : WordTrace (prefixWord ++ tailWord_14696) baseStart_14696 baseEnd_14696 := by
    simpa [prefixWord, tailWord_14696, baseEnd_14696] using wordTrace_append hprefix tailTrace_14696
  have hstable : (prefixWord ++ tailWord_14696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14696).length < 2 ^ (prefixWord ++ tailWord_14696).sum := by decide
  have hdescent : baseEnd_14696 < baseStart_14696 := by decide
  rcases family_descends (prefixWord ++ tailWord_14696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14703 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_14703 : Nat := 118140960795 + 14703 * 2 ^ 59
def prefixEnd_14703 : Nat := 4983230072969 + 3 ^ 40 * 14703 * 2
def baseEnd_14703 : Nat := 6710849833921073906567

theorem tailTrace_14703 : CollatzResearch.WordTrace tailWord_14703 prefixEnd_14703 6710849833921073906567 := by
  unfold tailWord_14703
  simp only [CollatzResearch.WordTrace]
  refine ⟨536262465741016917592763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 357508310494011278395175 536262465741016917592763)
  ·
    refine ⟨804393698611525376389145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536262465741016917592763 804393698611525376389145)
    ·
      refine ⟨603295273958644032291859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804393698611525376389145 603295273958644032291859)
      ·
        refine ⟨904942910937966048437789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603295273958644032291859 904942910937966048437789)
        ·
          refine ⟨339353591601737268164171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904942910937966048437789 339353591601737268164171)
          ·
            refine ⟨509030387402605902246257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339353591601737268164171 509030387402605902246257)
            ·
              refine ⟨381772790551954426684693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509030387402605902246257 381772790551954426684693)
              ·
                refine ⟨17895599557122863750845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 381772790551954426684693 17895599557122863750845)
                ·
                  refine ⟨6710849833921073906567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17895599557122863750845 6710849833921073906567)
                  ·
                    rfl

theorem cell20_14703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_14703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14703 prefixEnd_14703 := by exact prefixLift 14703
  have htrace : WordTrace (prefixWord ++ tailWord_14703) baseStart_14703 baseEnd_14703 := by
    simpa [prefixWord, tailWord_14703, baseEnd_14703] using wordTrace_append hprefix tailTrace_14703
  have hstable : (prefixWord ++ tailWord_14703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14703).length < 2 ^ (prefixWord ++ tailWord_14703).sum := by decide
  have hdescent : baseEnd_14703 < baseStart_14703 := by decide
  rcases family_descends (prefixWord ++ tailWord_14703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14706 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_14706 : Nat := 118140960795 + 14706 * 2 ^ 59
def prefixEnd_14706 : Nat := 4983230072969 + 3 ^ 40 * 14706 * 2
def baseEnd_14706 : Nat := 6712219115666396806555

theorem tailTrace_14706 : CollatzResearch.WordTrace tailWord_14706 prefixEnd_14706 6712219115666396806555 := by
  unfold tailWord_14706
  simp only [CollatzResearch.WordTrace]
  refine ⟨134092971182537107487993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 357581256486765619967981 134092971182537107487993)
  ·
    refine ⟨100569728386902830615995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134092971182537107487993 100569728386902830615995)
    ·
      refine ⟨150854592580354245923993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100569728386902830615995 150854592580354245923993)
      ·
        refine ⟨113140944435265684442995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150854592580354245923993 113140944435265684442995)
        ·
          refine ⟨169711416652898526664493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113140944435265684442995 169711416652898526664493)
          ·
            refine ⟨63641781244836947499185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169711416652898526664493 63641781244836947499185)
            ·
              refine ⟨47731335933627710624389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63641781244836947499185 47731335933627710624389)
              ·
                refine ⟨8949625487555195742073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47731335933627710624389 8949625487555195742073)
                ·
                  refine ⟨6712219115666396806555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8949625487555195742073 6712219115666396806555)
                  ·
                    rfl

theorem cell20_14706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_14706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14706 prefixEnd_14706 := by exact prefixLift 14706
  have htrace : WordTrace (prefixWord ++ tailWord_14706) baseStart_14706 baseEnd_14706 := by
    simpa [prefixWord, tailWord_14706, baseEnd_14706] using wordTrace_append hprefix tailTrace_14706
  have hstable : (prefixWord ++ tailWord_14706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14706).length < 2 ^ (prefixWord ++ tailWord_14706).sum := by decide
  have hdescent : baseEnd_14706 < baseStart_14706 := by decide
  rcases family_descends (prefixWord ++ tailWord_14706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14740 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_14740 : Nat := 118140960795 + 14740 * 2 ^ 59
def prefixEnd_14740 : Nat := 4983230072969 + 3 ^ 40 * 14740 * 2
def baseEnd_14740 : Nat := 6727737642113389673083

theorem tailTrace_14740 : CollatzResearch.WordTrace tailWord_14740 prefixEnd_14740 6727737642113389673083 := by
  unfold tailWord_14740
  simp only [CollatzResearch.WordTrace]
  refine ⟨268805983303486118344837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 358407977737981491126449 268805983303486118344837)
  ·
    refine ⟨50401121869403647189657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268805983303486118344837 50401121869403647189657)
    ·
      refine ⟨37800841402052735392243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50401121869403647189657 37800841402052735392243)
      ·
        refine ⟨56701262103079103088365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37800841402052735392243 56701262103079103088365)
        ·
          refine ⟨21262973288654663658137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56701262103079103088365 21262973288654663658137)
          ·
            refine ⟨15947229966490997743603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21262973288654663658137 15947229966490997743603)
            ·
              refine ⟨23920844949736496615405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15947229966490997743603 23920844949736496615405)
              ·
                refine ⟨8970316856151186230777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23920844949736496615405 8970316856151186230777)
                ·
                  refine ⟨6727737642113389673083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970316856151186230777 6727737642113389673083)
                  ·
                    rfl

theorem cell20_14740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_14740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14740 prefixEnd_14740 := by exact prefixLift 14740
  have htrace : WordTrace (prefixWord ++ tailWord_14740) baseStart_14740 baseEnd_14740 := by
    simpa [prefixWord, tailWord_14740, baseEnd_14740] using wordTrace_append hprefix tailTrace_14740
  have hstable : (prefixWord ++ tailWord_14740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14740).length < 2 ^ (prefixWord ++ tailWord_14740).sum := by decide
  have hdescent : baseEnd_14740 < baseStart_14740 := by decide
  rcases family_descends (prefixWord ++ tailWord_14740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14755 : List Nat := [1, 1, 1, 4, 1, 4, 8]
def baseStart_14755 : Nat := 118140960795 + 14755 * 2 ^ 59
def prefixEnd_14755 : Nat := 4983230072969 + 3 ^ 40 * 14755 * 2
def baseEnd_14755 : Nat := 748287116760000463669

theorem tailTrace_14755 : CollatzResearch.WordTrace tailWord_14755 prefixEnd_14755 748287116760000463669 := by
  unfold tailWord_14755
  simp only [CollatzResearch.WordTrace]
  refine ⟨538159061552629798485719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 358772707701753198990479 538159061552629798485719)
  ·
    refine ⟨807238592328944697728579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538159061552629798485719 807238592328944697728579)
    ·
      refine ⟨1210857888493417046592869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807238592328944697728579 1210857888493417046592869)
      ·
        refine ⟨227035854092515696236163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1210857888493417046592869 227035854092515696236163)
        ·
          refine ⟨340553781138773544354245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227035854092515696236163 340553781138773544354245)
          ·
            refine ⟨63853833963520039566421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340553781138773544354245 63853833963520039566421)
            ·
              refine ⟨748287116760000463669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 63853833963520039566421 748287116760000463669)
              ·
                rfl

theorem cell20_14755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_14755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14755 prefixEnd_14755 := by exact prefixLift 14755
  have htrace : WordTrace (prefixWord ++ tailWord_14755) baseStart_14755 baseEnd_14755 := by
    simpa [prefixWord, tailWord_14755, baseEnd_14755] using wordTrace_append hprefix tailTrace_14755
  have hstable : (prefixWord ++ tailWord_14755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14755).length < 2 ^ (prefixWord ++ tailWord_14755).sum := by decide
  have hdescent : baseEnd_14755 < baseStart_14755 := by decide
  rcases family_descends (prefixWord ++ tailWord_14755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14775 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 3]
def baseStart_14775 : Nat := 118140960795 + 14775 * 2 ^ 59
def prefixEnd_14775 : Nat := 4983230072969 + 3 ^ 40 * 14775 * 2
def baseEnd_14775 : Nat := 6743712595808823506273

theorem tailTrace_14775 : CollatzResearch.WordTrace tailWord_14775 prefixEnd_14775 6743712595808823506273 := by
  unfold tailWord_14775
  simp only [CollatzResearch.WordTrace]
  refine ⟨538888521480173214213779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 359259014320115476142519 538888521480173214213779)
  ·
    refine ⟨808332782220259821320669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538888521480173214213779 808332782220259821320669)
    ·
      refine ⟨303124793332597432995251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 808332782220259821320669 303124793332597432995251)
      ·
        refine ⟨454687189998896149492877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303124793332597432995251 454687189998896149492877)
        ·
          refine ⟨170507696249586056059829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454687189998896149492877 170507696249586056059829)
          ·
            refine ⟨15985096523398692755609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170507696249586056059829 15985096523398692755609)
            ·
              refine ⟨11988822392549019566707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15985096523398692755609 11988822392549019566707)
              ·
                refine ⟨17983233588823529350061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988822392549019566707 17983233588823529350061)
                ·
                  refine ⟨6743712595808823506273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17983233588823529350061 6743712595808823506273)
                  ·
                    rfl

theorem cell20_14775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_14775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14775 prefixEnd_14775 := by exact prefixLift 14775
  have htrace : WordTrace (prefixWord ++ tailWord_14775) baseStart_14775 baseEnd_14775 := by
    simpa [prefixWord, tailWord_14775, baseEnd_14775] using wordTrace_append hprefix tailTrace_14775
  have hstable : (prefixWord ++ tailWord_14775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14775).length < 2 ^ (prefixWord ++ tailWord_14775).sum := by decide
  have hdescent : baseEnd_14775 < baseStart_14775 := by decide
  rcases family_descends (prefixWord ++ tailWord_14775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14793 : List Nat := [1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_14793 : Nat := 118140960795 + 14793 * 2 ^ 59
def prefixEnd_14793 : Nat := 4983230072969 + 3 ^ 40 * 14793 * 2
def baseEnd_14793 : Nat := 2250642762093586968733

theorem tailTrace_14793 : CollatzResearch.WordTrace tailWord_14793 prefixEnd_14793 2250642762093586968733 := by
  unfold tailWord_14793
  simp only [CollatzResearch.WordTrace]
  refine ⟨539545035414962288369033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 359696690276641525579355 539545035414962288369033)
  ·
    refine ⟨404658776561221716276775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 539545035414962288369033 404658776561221716276775)
    ·
      refine ⟨606988164841832574415163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404658776561221716276775 606988164841832574415163)
      ·
        refine ⟨910482247262748861622745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606988164841832574415163 910482247262748861622745)
        ·
          refine ⟨682861685447061646217059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910482247262748861622745 682861685447061646217059)
          ·
            refine ⟨1024292528170592469325589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682861685447061646217059 1024292528170592469325589)
            ·
              refine ⟨48013712257996521999637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1024292528170592469325589 48013712257996521999637)
              ·
                refine ⟨2250642762093586968733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48013712257996521999637 2250642762093586968733)
                ·
                  rfl

theorem cell20_14793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_14793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14793 prefixEnd_14793 := by exact prefixLift 14793
  have htrace : WordTrace (prefixWord ++ tailWord_14793) baseStart_14793 baseEnd_14793 := by
    simpa [prefixWord, tailWord_14793, baseEnd_14793] using wordTrace_append hprefix tailTrace_14793
  have hstable : (prefixWord ++ tailWord_14793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14793).length < 2 ^ (prefixWord ++ tailWord_14793).sum := by decide
  have hdescent : baseEnd_14793 < baseStart_14793 := by decide
  rcases family_descends (prefixWord ++ tailWord_14793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14858 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_14858 : Nat := 118140960795 + 14858 * 2 ^ 59
def prefixEnd_14858 : Nat := 4983230072969 + 3 ^ 40 * 14858 * 2
def baseEnd_14858 : Nat := 6781596057429423739267

theorem tailTrace_14858 : CollatzResearch.WordTrace tailWord_14858 prefixEnd_14858 6781596057429423739267 := by
  unfold tailWord_14858
  simp only [CollatzResearch.WordTrace]
  refine ⟨135478945044869597371307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 361277186786318926323485 135478945044869597371307)
  ·
    refine ⟨203218417567304396056961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135478945044869597371307 203218417567304396056961)
    ·
      refine ⟨152413813175478297042721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203218417567304396056961 152413813175478297042721)
      ·
        refine ⟨114310359881608722782041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152413813175478297042721 114310359881608722782041)
        ·
          refine ⟨85732769911206542086531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114310359881608722782041 85732769911206542086531)
          ·
            refine ⟨128599154866809813129797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85732769911206542086531 128599154866809813129797)
            ·
              refine ⟨24112341537526839961837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128599154866809813129797 24112341537526839961837)
              ·
                refine ⟨9042128076572564985689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24112341537526839961837 9042128076572564985689)
                ·
                  refine ⟨6781596057429423739267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9042128076572564985689 6781596057429423739267)
                  ·
                    rfl

theorem cell20_14858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_14858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14858 prefixEnd_14858 := by exact prefixLift 14858
  have htrace : WordTrace (prefixWord ++ tailWord_14858) baseStart_14858 baseEnd_14858 := by
    simpa [prefixWord, tailWord_14858, baseEnd_14858] using wordTrace_append hprefix tailTrace_14858
  have hstable : (prefixWord ++ tailWord_14858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14858).length < 2 ^ (prefixWord ++ tailWord_14858).sum := by decide
  have hdescent : baseEnd_14858 < baseStart_14858 := by decide
  rcases family_descends (prefixWord ++ tailWord_14858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14868 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_14868 : Nat := 118140960795 + 14868 * 2 ^ 59
def prefixEnd_14868 : Nat := 4983230072969 + 3 ^ 40 * 14868 * 2
def baseEnd_14868 : Nat := 6786160329913833405893

theorem tailTrace_14868 : CollatzResearch.WordTrace tailWord_14868 prefixEnd_14868 6786160329913833405893 := by
  unfold tailWord_14868
  simp only [CollatzResearch.WordTrace]
  refine ⟨271140255071625048674629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 361520340095500064899505 271140255071625048674629)
  ·
    refine ⟨50838797825929696626493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271140255071625048674629 50838797825929696626493)
    ·
      refine ⟨19064549184723636234935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50838797825929696626493 19064549184723636234935)
      ·
        refine ⟨28596823777085454352403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19064549184723636234935 28596823777085454352403)
        ·
          refine ⟨42895235665628181528605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28596823777085454352403 42895235665628181528605)
          ·
            refine ⟨16085713374610568073227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42895235665628181528605 16085713374610568073227)
            ·
              refine ⟨24128570061915852109841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16085713374610568073227 24128570061915852109841)
              ·
                refine ⟨18096427546436889082381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24128570061915852109841 18096427546436889082381)
                ·
                  refine ⟨6786160329913833405893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18096427546436889082381 6786160329913833405893)
                  ·
                    rfl

theorem cell20_14868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_14868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14868 prefixEnd_14868 := by exact prefixLift 14868
  have htrace : WordTrace (prefixWord ++ tailWord_14868) baseStart_14868 baseEnd_14868 := by
    simpa [prefixWord, tailWord_14868, baseEnd_14868] using wordTrace_append hprefix tailTrace_14868
  have hstable : (prefixWord ++ tailWord_14868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14868).length < 2 ^ (prefixWord ++ tailWord_14868).sum := by decide
  have hdescent : baseEnd_14868 < baseStart_14868 := by decide
  rcases family_descends (prefixWord ++ tailWord_14868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14869 : List Nat := [1, 3, 2, 1, 3, 1, 9]
def baseStart_14869 : Nat := 118140960795 + 14869 * 2 ^ 59
def prefixEnd_14869 : Nat := 4983230072969 + 3 ^ 40 * 14869 * 2
def baseEnd_14869 : Nat := 754068528573586041395

theorem tailTrace_14869 : CollatzResearch.WordTrace tailWord_14869 prefixEnd_14869 754068528573586041395 := by
  unfold tailWord_14869
  simp only [CollatzResearch.WordTrace]
  refine ⟨542316983139627268135661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 361544655426418178757107 542316983139627268135661)
  ·
    refine ⟨203368868677360225550873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 542316983139627268135661 203368868677360225550873)
    ·
      refine ⟨152526651508020169163155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203368868677360225550873 152526651508020169163155)
      ·
        refine ⟨228789977262030253744733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152526651508020169163155 228789977262030253744733)
        ·
          refine ⟨85796241473261345154275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228789977262030253744733 85796241473261345154275)
          ·
            refine ⟨128694362209892017731413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85796241473261345154275 128694362209892017731413)
            ·
              refine ⟨754068528573586041395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 128694362209892017731413 754068528573586041395)
              ·
                rfl

theorem cell20_14869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_14869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14869 prefixEnd_14869 := by exact prefixLift 14869
  have htrace : WordTrace (prefixWord ++ tailWord_14869) baseStart_14869 baseEnd_14869 := by
    simpa [prefixWord, tailWord_14869, baseEnd_14869] using wordTrace_append hprefix tailTrace_14869
  have hstable : (prefixWord ++ tailWord_14869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14869).length < 2 ^ (prefixWord ++ tailWord_14869).sum := by decide
  have hdescent : baseEnd_14869 < baseStart_14869 := by decide
  rcases family_descends (prefixWord ++ tailWord_14869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14872 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_14872 : Nat := 118140960795 + 14872 * 2 ^ 59
def prefixEnd_14872 : Nat := 4983230072969 + 3 ^ 40 * 14872 * 2
def baseEnd_14872 : Nat := 6787986038907597272543

theorem tailTrace_14872 : CollatzResearch.WordTrace tailWord_14872 prefixEnd_14872 6787986038907597272543 := by
  unfold tailWord_14872
  simp only [CollatzResearch.WordTrace]
  refine ⟨271213201064379390247435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 361617601419172520329913 271213201064379390247435)
  ·
    refine ⟨406819801596569085371153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271213201064379390247435 406819801596569085371153)
    ·
      refine ⟨305114851197426814028365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406819801596569085371153 305114851197426814028365)
      ·
        refine ⟨114418069199035055260637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305114851197426814028365 114418069199035055260637)
        ·
          refine ⟨42906775949638145722739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114418069199035055260637 42906775949638145722739)
          ·
            refine ⟨64360163924457218584109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42906775949638145722739 64360163924457218584109)
            ·
              refine ⟨24135061471671456969041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64360163924457218584109 24135061471671456969041)
              ·
                refine ⟨18101296103753592726781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24135061471671456969041 18101296103753592726781)
                ·
                  refine ⟨6787986038907597272543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18101296103753592726781 6787986038907597272543)
                  ·
                    rfl

theorem cell20_14872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_14872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14872 prefixEnd_14872 := by exact prefixLift 14872
  have htrace : WordTrace (prefixWord ++ tailWord_14872) baseStart_14872 baseEnd_14872 := by
    simpa [prefixWord, tailWord_14872, baseEnd_14872] using wordTrace_append hprefix tailTrace_14872
  have hstable : (prefixWord ++ tailWord_14872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14872).length < 2 ^ (prefixWord ++ tailWord_14872).sum := by decide
  have hdescent : baseEnd_14872 < baseStart_14872 := by decide
  rcases family_descends (prefixWord ++ tailWord_14872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14913 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 2]
def baseStart_14913 : Nat := 118140960795 + 14913 * 2 ^ 59
def prefixEnd_14913 : Nat := 4983230072969 + 3 ^ 40 * 14913 * 2
def baseEnd_14913 : Nat := 6806699556093676905709

theorem tailTrace_14913 : CollatzResearch.WordTrace tailWord_14913 prefixEnd_14913 6806699556093676905709 := by
  unfold tailWord_14913
  simp only [CollatzResearch.WordTrace]
  refine ⟨543921794980222782737393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 362614529986815188491595 543921794980222782737393)
  ·
    refine ⟨407941346235167087053045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 543921794980222782737393 407941346235167087053045)
    ·
      refine ⟨38244501209546914411223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407941346235167087053045 38244501209546914411223)
      ·
        refine ⟨57366751814320371616835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38244501209546914411223 57366751814320371616835)
        ·
          refine ⟨86050127721480557425253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57366751814320371616835 86050127721480557425253)
          ·
            refine ⟨16134398947777604517235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86050127721480557425253 16134398947777604517235)
            ·
              refine ⟨24201598421666406775853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134398947777604517235 24201598421666406775853)
              ·
                refine ⟨9075599408124902540945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24201598421666406775853 9075599408124902540945)
                ·
                  refine ⟨6806699556093676905709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9075599408124902540945 6806699556093676905709)
                  ·
                    rfl

theorem cell20_14913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_14913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14913 prefixEnd_14913 := by exact prefixLift 14913
  have htrace : WordTrace (prefixWord ++ tailWord_14913) baseStart_14913 baseEnd_14913 := by
    simpa [prefixWord, tailWord_14913, baseEnd_14913] using wordTrace_append hprefix tailTrace_14913
  have hstable : (prefixWord ++ tailWord_14913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14913).length < 2 ^ (prefixWord ++ tailWord_14913).sum := by decide
  have hdescent : baseEnd_14913 < baseStart_14913 := by decide
  rcases family_descends (prefixWord ++ tailWord_14913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14945 : List Nat := [1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_14945 : Nat := 118140960795 + 14945 * 2 ^ 59
def prefixEnd_14945 : Nat := 4983230072969 + 3 ^ 40 * 14945 * 2
def baseEnd_14945 : Nat := 2273768409347929279637

theorem tailTrace_14945 : CollatzResearch.WordTrace tailWord_14945 prefixEnd_14945 2273768409347929279637 := by
  unfold tailWord_14945
  simp only [CollatzResearch.WordTrace]
  refine ⟨545088930864292247902289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 363392620576194831934859 545088930864292247902289)
  ·
    refine ⟨408816698148219185926717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 545088930864292247902289 408816698148219185926717)
    ·
      refine ⟨153306261805582194722519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408816698148219185926717 153306261805582194722519)
      ·
        refine ⟨229959392708373292083779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153306261805582194722519 229959392708373292083779)
        ·
          refine ⟨344939089062559938125669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229959392708373292083779 344939089062559938125669)
          ·
            refine ⟨64676079199229988398563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344939089062559938125669 64676079199229988398563)
            ·
              refine ⟨97014118798844982597845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64676079199229988398563 97014118798844982597845)
              ·
                refine ⟨2273768409347929279637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97014118798844982597845 2273768409347929279637)
                ·
                  rfl

theorem cell20_14945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_14945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_14945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_14945 prefixEnd_14945 := by exact prefixLift 14945
  have htrace : WordTrace (prefixWord ++ tailWord_14945) baseStart_14945 baseEnd_14945 := by
    simpa [prefixWord, tailWord_14945, baseEnd_14945] using wordTrace_append hprefix tailTrace_14945
  have hstable : (prefixWord ++ tailWord_14945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14945).length < 2 ^ (prefixWord ++ tailWord_14945).sum := by decide
  have hdescent : baseEnd_14945 < baseStart_14945 := by decide
  rcases family_descends (prefixWord ++ tailWord_14945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15041 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_15041 : Nat := 118140960795 + 15041 * 2 ^ 59
def prefixEnd_15041 : Nat := 4983230072969 + 3 ^ 40 * 15041 * 2
def baseEnd_15041 : Nat := 6865122243894120638519

theorem tailTrace_15041 : CollatzResearch.WordTrace tailWord_15041 prefixEnd_15041 6865122243894120638519 := by
  unfold tailWord_15041
  simp only [CollatzResearch.WordTrace]
  refine ⟨548590338516500643396977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 365726892344333762264651 548590338516500643396977)
  ·
    refine ⟨411442753887375482547733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 548590338516500643396977 411442753887375482547733)
    ·
      refine ⟨19286379088470725744425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 411442753887375482547733 19286379088470725744425)
      ·
        refine ⟨14464784316353044308319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19286379088470725744425 14464784316353044308319)
        ·
          refine ⟨21697176474529566462479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464784316353044308319 21697176474529566462479)
          ·
            refine ⟨32545764711794349693719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21697176474529566462479 32545764711794349693719)
            ·
              refine ⟨48818647067691524540579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32545764711794349693719 48818647067691524540579)
              ·
                refine ⟨73227970601537286810869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48818647067691524540579 73227970601537286810869)
                ·
                  refine ⟨6865122243894120638519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73227970601537286810869 6865122243894120638519)
                  ·
                    rfl

theorem cell20_15041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_15041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15041 prefixEnd_15041 := by exact prefixLift 15041
  have htrace : WordTrace (prefixWord ++ tailWord_15041) baseStart_15041 baseEnd_15041 := by
    simpa [prefixWord, tailWord_15041, baseEnd_15041] using wordTrace_append hprefix tailTrace_15041
  have hstable : (prefixWord ++ tailWord_15041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15041).length < 2 ^ (prefixWord ++ tailWord_15041).sum := by decide
  have hdescent : baseEnd_15041 < baseStart_15041 := by decide
  rcases family_descends (prefixWord ++ tailWord_15041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15076 : List Nat := [2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_15076 : Nat := 118140960795 + 15076 * 2 ^ 59
def prefixEnd_15076 : Nat := 4983230072969 + 3 ^ 40 * 15076 * 2
def baseEnd_15076 : Nat := 2293699065863184823903

theorem tailTrace_15076 : CollatzResearch.WordTrace tailWord_15076 prefixEnd_15076 2293699065863184823903 := by
  unfold tailWord_15076
  simp only [CollatzResearch.WordTrace]
  refine ⟨274933446694850810460541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 366577928926467747280721 274933446694850810460541)
  ·
    refine ⟨103100042510569053922703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274933446694850810460541 103100042510569053922703)
    ·
      refine ⟨154650063765853580884055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103100042510569053922703 154650063765853580884055)
      ·
        refine ⟨231975095648780371326083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154650063765853580884055 231975095648780371326083)
        ·
          refine ⟨347962643473170556989125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231975095648780371326083 347962643473170556989125)
          ·
            refine ⟨65242995651219479435461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347962643473170556989125 65242995651219479435461)
            ·
              refine ⟨12233061684603652394149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65242995651219479435461 12233061684603652394149)
              ·
                refine ⟨2293699065863184823903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12233061684603652394149 2293699065863184823903)
                ·
                  rfl

theorem cell20_15076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_15076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15076 prefixEnd_15076 := by exact prefixLift 15076
  have htrace : WordTrace (prefixWord ++ tailWord_15076) baseStart_15076 baseEnd_15076 := by
    simpa [prefixWord, tailWord_15076, baseEnd_15076] using wordTrace_append hprefix tailTrace_15076
  have hstable : (prefixWord ++ tailWord_15076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15076).length < 2 ^ (prefixWord ++ tailWord_15076).sum := by decide
  have hdescent : baseEnd_15076 < baseStart_15076 := by decide
  rcases family_descends (prefixWord ++ tailWord_15076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15086 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_15086 : Nat := 118140960795 + 15086 * 2 ^ 59
def prefixEnd_15086 : Nat := 4983230072969 + 3 ^ 40 * 15086 * 2
def baseEnd_15086 : Nat := 6885661470073964138335

theorem tailTrace_15086 : CollatzResearch.WordTrace tailWord_15086 prefixEnd_15086 6885661470073964138335 := by
  unfold tailWord_15086
  simp only [CollatzResearch.WordTrace]
  refine ⟨68778952919184166098139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 366821082235648885856741 68778952919184166098139)
  ·
    refine ⟨103168429378776249147209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68778952919184166098139 103168429378776249147209)
    ·
      refine ⟨77376322034082186860407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103168429378776249147209 77376322034082186860407)
      ·
        refine ⟨116064483051123280290611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77376322034082186860407 116064483051123280290611)
        ·
          refine ⟨174096724576684920435917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116064483051123280290611 174096724576684920435917)
          ·
            refine ⟨65286271716256845163469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174096724576684920435917 65286271716256845163469)
            ·
              refine ⟨24482351893596316936301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65286271716256845163469 24482351893596316936301)
              ·
                refine ⟨9180881960098618851113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24482351893596316936301 9180881960098618851113)
                ·
                  refine ⟨6885661470073964138335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180881960098618851113 6885661470073964138335)
                  ·
                    rfl

theorem cell20_15086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_15086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15086 prefixEnd_15086 := by exact prefixLift 15086
  have htrace : WordTrace (prefixWord ++ tailWord_15086) baseStart_15086 baseEnd_15086 := by
    simpa [prefixWord, tailWord_15086, baseEnd_15086] using wordTrace_append hprefix tailTrace_15086
  have hstable : (prefixWord ++ tailWord_15086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15086).length < 2 ^ (prefixWord ++ tailWord_15086).sum := by decide
  have hdescent : baseEnd_15086 < baseStart_15086 := by decide
  rcases family_descends (prefixWord ++ tailWord_15086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15135 : List Nat := [1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_15135 : Nat := 118140960795 + 15135 * 2 ^ 59
def prefixEnd_15135 : Nat := 4983230072969 + 3 ^ 40 * 15135 * 2
def baseEnd_15135 : Nat := 2302675468415857168267

theorem tailTrace_15135 : CollatzResearch.WordTrace tailWord_15135 prefixEnd_15135 2302675468415857168267 := by
  unfold tailWord_15135
  simp only [CollatzResearch.WordTrace]
  refine ⟨552018800175954697318859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 368012533450636464879239 552018800175954697318859)
  ·
    refine ⟨828028200263932045978289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552018800175954697318859 828028200263932045978289)
    ·
      refine ⟨621021150197949034483717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828028200263932045978289 621021150197949034483717)
      ·
        refine ⟨116441465662115443965697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 621021150197949034483717 116441465662115443965697)
        ·
          refine ⟨87331099246586582974273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116441465662115443965697 87331099246586582974273)
          ·
            refine ⟨65498324434939937230705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87331099246586582974273 65498324434939937230705)
            ·
              refine ⟨49123743326204952923029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65498324434939937230705 49123743326204952923029)
              ·
                refine ⟨2302675468415857168267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49123743326204952923029 2302675468415857168267)
                ·
                  rfl

theorem cell20_15135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_15135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15135 prefixEnd_15135 := by exact prefixLift 15135
  have htrace : WordTrace (prefixWord ++ tailWord_15135) baseStart_15135 baseEnd_15135 := by
    simpa [prefixWord, tailWord_15135, baseEnd_15135] using wordTrace_append hprefix tailTrace_15135
  have hstable : (prefixWord ++ tailWord_15135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15135).length < 2 ^ (prefixWord ++ tailWord_15135).sum := by decide
  have hdescent : baseEnd_15135 < baseStart_15135 := by decide
  rcases family_descends (prefixWord ++ tailWord_15135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15159 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_15159 : Nat := 118140960795 + 15159 * 2 ^ 59
def prefixEnd_15159 : Nat := 4983230072969 + 3 ^ 40 * 15159 * 2
def baseEnd_15159 : Nat := 6918980659210154704703

theorem tailTrace_15159 : CollatzResearch.WordTrace tailWord_15159 prefixEnd_15159 6918980659210154704703 := by
  unfold tailWord_15159
  simp only [CollatzResearch.WordTrace]
  refine ⟨552894152089006796192531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 368596101392671197461687 552894152089006796192531)
  ·
    refine ⟨829341228133510194288797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552894152089006796192531 829341228133510194288797)
    ·
      refine ⟨311002960550066322858299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 829341228133510194288797 311002960550066322858299)
      ·
        refine ⟨466504440825099484287449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311002960550066322858299 466504440825099484287449)
        ·
          refine ⟨349878330618824613215587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466504440825099484287449 349878330618824613215587)
          ·
            refine ⟨524817495928236919823381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349878330618824613215587 524817495928236919823381)
            ·
              refine ⟨24600820121636105616721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 524817495928236919823381 24600820121636105616721)
              ·
                refine ⟨18450615091227079212541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24600820121636105616721 18450615091227079212541)
                ·
                  refine ⟨6918980659210154704703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18450615091227079212541 6918980659210154704703)
                  ·
                    rfl

theorem cell20_15159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_15159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15159 prefixEnd_15159 := by exact prefixLift 15159
  have htrace : WordTrace (prefixWord ++ tailWord_15159) baseStart_15159 baseEnd_15159 := by
    simpa [prefixWord, tailWord_15159, baseEnd_15159] using wordTrace_append hprefix tailTrace_15159
  have hstable : (prefixWord ++ tailWord_15159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15159).length < 2 ^ (prefixWord ++ tailWord_15159).sum := by decide
  have hdescent : baseEnd_15159 < baseStart_15159 := by decide
  rcases family_descends (prefixWord ++ tailWord_15159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15162 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_15162 : Nat := 118140960795 + 15162 * 2 ^ 59
def prefixEnd_15162 : Nat := 4983230072969 + 3 ^ 40 * 15162 * 2
def baseEnd_15162 : Nat := 6920349940955477604691

theorem tailTrace_15162 : CollatzResearch.WordTrace tailWord_15162 prefixEnd_15162 6920349940955477604691 := by
  unfold tailWord_15162
  simp only [CollatzResearch.WordTrace]
  refine ⟨138250892769534577137935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 368669047385425539034493 138250892769534577137935)
  ·
    refine ⟨207376339154301865706903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138250892769534577137935 207376339154301865706903)
    ·
      refine ⟨311064508731452798560355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207376339154301865706903 311064508731452798560355)
      ·
        refine ⟨466596763097179197840533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311064508731452798560355 466596763097179197840533)
        ·
          refine ⟨21871723270180274898775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 466596763097179197840533 21871723270180274898775)
          ·
            refine ⟨32807584905270412348163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21871723270180274898775 32807584905270412348163)
            ·
              refine ⟨49211377357905618522245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32807584905270412348163 49211377357905618522245)
              ·
                refine ⟨9227133254607303472921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49211377357905618522245 9227133254607303472921)
                ·
                  refine ⟨6920349940955477604691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9227133254607303472921 6920349940955477604691)
                  ·
                    rfl

theorem cell20_15162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_15162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15162 prefixEnd_15162 := by exact prefixLift 15162
  have htrace : WordTrace (prefixWord ++ tailWord_15162) baseStart_15162 baseEnd_15162 := by
    simpa [prefixWord, tailWord_15162, baseEnd_15162] using wordTrace_append hprefix tailTrace_15162
  have hstable : (prefixWord ++ tailWord_15162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15162).length < 2 ^ (prefixWord ++ tailWord_15162).sum := by decide
  have hdescent : baseEnd_15162 < baseStart_15162 := by decide
  rcases family_descends (prefixWord ++ tailWord_15162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15214 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_15214 : Nat := 118140960795 + 15214 * 2 ^ 59
def prefixEnd_15214 : Nat := 4983230072969 + 3 ^ 40 * 15214 * 2
def baseEnd_15214 : Nat := 6944084157874407871145

theorem tailTrace_15214 : CollatzResearch.WordTrace tailWord_15214 prefixEnd_15214 6944084157874407871145 := by
  unfold tailWord_15214
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362520861218898680587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 369933444593167459629797 69362520861218898680587)
  ·
    refine ⟨104043781291828348020881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69362520861218898680587 104043781291828348020881)
    ·
      refine ⟨78032835968871261015661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104043781291828348020881 78032835968871261015661)
      ·
        refine ⟨29262313488326722880873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78032835968871261015661 29262313488326722880873)
        ·
          refine ⟨21946735116245042160655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29262313488326722880873 21946735116245042160655)
          ·
            refine ⟨32920102674367563240983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21946735116245042160655 32920102674367563240983)
            ·
              refine ⟨49380154011551344861475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32920102674367563240983 49380154011551344861475)
              ·
                refine ⟨74070231017327017292213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49380154011551344861475 74070231017327017292213)
                ·
                  refine ⟨6944084157874407871145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74070231017327017292213 6944084157874407871145)
                  ·
                    rfl

theorem cell20_15214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_15214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15214 prefixEnd_15214 := by exact prefixLift 15214
  have htrace : WordTrace (prefixWord ++ tailWord_15214) baseStart_15214 baseEnd_15214 := by
    simpa [prefixWord, tailWord_15214, baseEnd_15214] using wordTrace_append hprefix tailTrace_15214
  have hstable : (prefixWord ++ tailWord_15214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15214).length < 2 ^ (prefixWord ++ tailWord_15214).sum := by decide
  have hdescent : baseEnd_15214 < baseStart_15214 := by decide
  rcases family_descends (prefixWord ++ tailWord_15214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15221 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_15221 : Nat := 118140960795 + 15221 * 2 ^ 59
def prefixEnd_15221 : Nat := 4983230072969 + 3 ^ 40 * 15221 * 2
def baseEnd_15221 : Nat := 6947279148613494637783

theorem tailTrace_15221 : CollatzResearch.WordTrace tailWord_15221 prefixEnd_15221 6947279148613494637783 := by
  unfold tailWord_15221
  simp only [CollatzResearch.WordTrace]
  refine ⟨555155477864391384949517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 370103651909594256633011 555155477864391384949517)
  ·
    refine ⟨208183304199146769356069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 555155477864391384949517 208183304199146769356069)
    ·
      refine ⟨39034369537340019254263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208183304199146769356069 39034369537340019254263)
      ·
        refine ⟨58551554306010028881395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39034369537340019254263 58551554306010028881395)
        ·
          refine ⟨87827331459015043322093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58551554306010028881395 87827331459015043322093)
          ·
            refine ⟨32935249297130641245785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87827331459015043322093 32935249297130641245785)
            ·
              refine ⟨24701436972847980934339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32935249297130641245785 24701436972847980934339)
              ·
                refine ⟨37052155459271971401509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24701436972847980934339 37052155459271971401509)
                ·
                  refine ⟨6947279148613494637783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37052155459271971401509 6947279148613494637783)
                  ·
                    rfl

theorem cell20_15221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_15221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15221 prefixEnd_15221 := by exact prefixLift 15221
  have htrace : WordTrace (prefixWord ++ tailWord_15221) baseStart_15221 baseEnd_15221 := by
    simpa [prefixWord, tailWord_15221, baseEnd_15221] using wordTrace_append hprefix tailTrace_15221
  have hstable : (prefixWord ++ tailWord_15221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15221).length < 2 ^ (prefixWord ++ tailWord_15221).sum := by decide
  have hdescent : baseEnd_15221 < baseStart_15221 := by decide
  rcases family_descends (prefixWord ++ tailWord_15221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15266 : List Nat := [3, 3, 1, 2, 2, 3, 6]
def baseStart_15266 : Nat := 118140960795 + 15266 * 2 ^ 59
def prefixEnd_15266 : Nat := 4983230072969 + 3 ^ 40 * 15266 * 2
def baseEnd_15266 : Nat := 774202041643704237511

theorem tailTrace_15266 : CollatzResearch.WordTrace tailWord_15266 prefixEnd_15266 774202041643704237511 := by
  unfold tailWord_15266
  simp only [CollatzResearch.WordTrace]
  refine ⟨139199190675341017584413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 371197841800909380225101 139199190675341017584413)
  ·
    refine ⟨52199696503252881594155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139199190675341017584413 52199696503252881594155)
    ·
      refine ⟨78299544754879322391233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52199696503252881594155 78299544754879322391233)
      ·
        refine ⟨58724658566159491793425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78299544754879322391233 58724658566159491793425)
        ·
          refine ⟨44043493924619618845069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58724658566159491793425 44043493924619618845069)
          ·
            refine ⟨16516310221732357066901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44043493924619618845069 16516310221732357066901)
            ·
              refine ⟨774202041643704237511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16516310221732357066901 774202041643704237511)
              ·
                rfl

theorem cell20_15266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_15266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15266 prefixEnd_15266 := by exact prefixLift 15266
  have htrace : WordTrace (prefixWord ++ tailWord_15266) baseStart_15266 baseEnd_15266 := by
    simpa [prefixWord, tailWord_15266, baseEnd_15266] using wordTrace_append hprefix tailTrace_15266
  have hstable : (prefixWord ++ tailWord_15266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15266).length < 2 ^ (prefixWord ++ tailWord_15266).sum := by decide
  have hdescent : baseEnd_15266 < baseStart_15266 := by decide
  rcases family_descends (prefixWord ++ tailWord_15266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15325 : List Nat := [1, 4, 3, 1, 2, 9]
def baseStart_15325 : Nat := 118140960795 + 15325 * 2 ^ 59
def prefixEnd_15325 : Nat := 4983230072969 + 3 ^ 40 * 15325 * 2
def baseEnd_15325 : Nat := 259064725275976117433

theorem tailTrace_15325 : CollatzResearch.WordTrace tailWord_15325 prefixEnd_15325 259064725275976117433 := by
  unfold tailWord_15325
  simp only [CollatzResearch.WordTrace]
  refine ⟨558948669487617146735429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 372632446325078097823619 558948669487617146735429)
  ·
    refine ⟨104802875528928215012893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 558948669487617146735429 104802875528928215012893)
    ·
      refine ⟨39301078323348080629835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104802875528928215012893 39301078323348080629835)
      ·
        refine ⟨58951617485022120944753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39301078323348080629835 58951617485022120944753)
        ·
          refine ⟨44213713113766590708565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58951617485022120944753 44213713113766590708565)
          ·
            refine ⟨259064725275976117433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 44213713113766590708565 259064725275976117433)
            ·
              rfl

theorem cell20_15325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 9].length) (baseStart_15325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15325 prefixEnd_15325 := by exact prefixLift 15325
  have htrace : WordTrace (prefixWord ++ tailWord_15325) baseStart_15325 baseEnd_15325 := by
    simpa [prefixWord, tailWord_15325, baseEnd_15325] using wordTrace_append hprefix tailTrace_15325
  have hstable : (prefixWord ++ tailWord_15325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15325).length < 2 ^ (prefixWord ++ tailWord_15325).sum := by decide
  have hdescent : baseEnd_15325 < baseStart_15325 := by decide
  rcases family_descends (prefixWord ++ tailWord_15325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15348 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_15348 : Nat := 118140960795 + 15348 * 2 ^ 59
def prefixEnd_15348 : Nat := 4983230072969 + 3 ^ 40 * 15348 * 2
def baseEnd_15348 : Nat := 7005245409165497403931

theorem tailTrace_15348 : CollatzResearch.WordTrace tailWord_15348 prefixEnd_15348 7005245409165497403931 := by
  unfold tailWord_15348
  simp only [CollatzResearch.WordTrace]
  refine ⟨279893774202146037411349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 373191698936194716548465 279893774202146037411349)
  ·
    refine ⟨13120020665725595503657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279893774202146037411349 13120020665725595503657)
    ·
      refine ⟨9840015499294196627743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13120020665725595503657 9840015499294196627743)
      ·
        refine ⟨14760023248941294941615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9840015499294196627743 14760023248941294941615)
        ·
          refine ⟨22140034873411942412423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14760023248941294941615 22140034873411942412423)
          ·
            refine ⟨33210052310117913618635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22140034873411942412423 33210052310117913618635)
            ·
              refine ⟨49815078465176870427953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33210052310117913618635 49815078465176870427953)
              ·
                refine ⟨37361308848882652820965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49815078465176870427953 37361308848882652820965)
                ·
                  refine ⟨7005245409165497403931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37361308848882652820965 7005245409165497403931)
                  ·
                    rfl

theorem cell20_15348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_15348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15348 prefixEnd_15348 := by exact prefixLift 15348
  have htrace : WordTrace (prefixWord ++ tailWord_15348) baseStart_15348 baseEnd_15348 := by
    simpa [prefixWord, tailWord_15348, baseEnd_15348] using wordTrace_append hprefix tailTrace_15348
  have hstable : (prefixWord ++ tailWord_15348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15348).length < 2 ^ (prefixWord ++ tailWord_15348).sum := by decide
  have hdescent : baseEnd_15348 < baseStart_15348 := by decide
  rcases family_descends (prefixWord ++ tailWord_15348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15356 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_15356 : Nat := 118140960795 + 15356 * 2 ^ 59
def prefixEnd_15356 : Nat := 4983230072969 + 3 ^ 40 * 15356 * 2
def baseEnd_15356 : Nat := 7008896827153025137231

theorem tailTrace_15356 : CollatzResearch.WordTrace tailWord_15356 prefixEnd_15356 7008896827153025137231 := by
  unfold tailWord_15356
  simp only [CollatzResearch.WordTrace]
  refine ⟨280039666187654720556961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 373386221583539627409281 280039666187654720556961)
  ·
    refine ⟨210029749640741040417721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280039666187654720556961 210029749640741040417721)
    ·
      refine ⟨157522312230555780313291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210029749640741040417721 157522312230555780313291)
      ·
        refine ⟨236283468345833670469937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157522312230555780313291 236283468345833670469937)
        ·
          refine ⟨177212601259375252852453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236283468345833670469937 177212601259375252852453)
          ·
            refine ⟨33227362736132859909835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177212601259375252852453 33227362736132859909835)
            ·
              refine ⟨49841044104199289864753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33227362736132859909835 49841044104199289864753)
              ·
                refine ⟨37380783078149467398565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49841044104199289864753 37380783078149467398565)
                ·
                  refine ⟨7008896827153025137231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37380783078149467398565 7008896827153025137231)
                  ·
                    rfl

theorem cell20_15356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_15356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15356 prefixEnd_15356 := by exact prefixLift 15356
  have htrace : WordTrace (prefixWord ++ tailWord_15356) baseStart_15356 baseEnd_15356 := by
    simpa [prefixWord, tailWord_15356, baseEnd_15356] using wordTrace_append hprefix tailTrace_15356
  have hstable : (prefixWord ++ tailWord_15356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15356).length < 2 ^ (prefixWord ++ tailWord_15356).sum := by decide
  have hdescent : baseEnd_15356 < baseStart_15356 := by decide
  rcases family_descends (prefixWord ++ tailWord_15356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15394 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_15394 : Nat := 118140960795 + 15394 * 2 ^ 59
def prefixEnd_15394 : Nat := 4983230072969 + 3 ^ 40 * 15394 * 2
def baseEnd_15394 : Nat := 7026241062593781870409

theorem tailTrace_15394 : CollatzResearch.WordTrace tailWord_15394 prefixEnd_15394 7026241062593781870409 := by
  unfold tailWord_15394
  simp only [CollatzResearch.WordTrace]
  refine ⟨140366326559410482749309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 374310204158427953998157 140366326559410482749309)
  ·
    refine ⟨52637372459778931030991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140366326559410482749309 52637372459778931030991)
    ·
      refine ⟨78956058689668396546487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52637372459778931030991 78956058689668396546487)
      ·
        refine ⟨118434088034502594819731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78956058689668396546487 118434088034502594819731)
        ·
          refine ⟨177651132051753892229597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118434088034502594819731 177651132051753892229597)
          ·
            refine ⟨66619174519407709586099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177651132051753892229597 66619174519407709586099)
            ·
              refine ⟨99928761779111564379149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66619174519407709586099 99928761779111564379149)
              ·
                refine ⟨37473285667166836642181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99928761779111564379149 37473285667166836642181)
                ·
                  refine ⟨7026241062593781870409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37473285667166836642181 7026241062593781870409)
                  ·
                    rfl

theorem cell20_15394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_15394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15394 prefixEnd_15394 := by exact prefixLift 15394
  have htrace : WordTrace (prefixWord ++ tailWord_15394) baseStart_15394 baseEnd_15394 := by
    simpa [prefixWord, tailWord_15394, baseEnd_15394] using wordTrace_append hprefix tailTrace_15394
  have hstable : (prefixWord ++ tailWord_15394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15394).length < 2 ^ (prefixWord ++ tailWord_15394).sum := by decide
  have hdescent : baseEnd_15394 < baseStart_15394 := by decide
  rcases family_descends (prefixWord ++ tailWord_15394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15463 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_15463 : Nat := 118140960795 + 15463 * 2 ^ 59
def prefixEnd_15463 : Nat := 4983230072969 + 3 ^ 40 * 15463 * 2
def baseEnd_15463 : Nat := 7057734542736208570127

theorem tailTrace_15463 : CollatzResearch.WordTrace tailWord_15463 prefixEnd_15463 7057734542736208570127 := by
  unfold tailWord_15463
  simp only [CollatzResearch.WordTrace]
  refine ⟨563981942987666715259043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 375987961991777810172695 563981942987666715259043)
  ·
    refine ⟨845972914481500072888565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563981942987666715259043 845972914481500072888565)
    ·
      refine ⟨79309960732640631833303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 845972914481500072888565 79309960732640631833303)
      ·
        refine ⟨118964941098960947749955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79309960732640631833303 118964941098960947749955)
        ·
          refine ⟨178447411648441421624933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118964941098960947749955 178447411648441421624933)
          ·
            refine ⟨33458889684082766554675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178447411648441421624933 33458889684082766554675)
            ·
              refine ⟨50188334526124149832013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33458889684082766554675 50188334526124149832013)
              ·
                refine ⟨18820625447296556187005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50188334526124149832013 18820625447296556187005)
                ·
                  refine ⟨7057734542736208570127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18820625447296556187005 7057734542736208570127)
                  ·
                    rfl

theorem cell20_15463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_15463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15463 prefixEnd_15463 := by exact prefixLift 15463
  have htrace : WordTrace (prefixWord ++ tailWord_15463) baseStart_15463 baseEnd_15463 := by
    simpa [prefixWord, tailWord_15463, baseEnd_15463] using wordTrace_append hprefix tailTrace_15463
  have hstable : (prefixWord ++ tailWord_15463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15463).length < 2 ^ (prefixWord ++ tailWord_15463).sum := by decide
  have hdescent : baseEnd_15463 < baseStart_15463 := by decide
  rcases family_descends (prefixWord ++ tailWord_15463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15518 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_15518 : Nat := 118140960795 + 15518 * 2 ^ 59
def prefixEnd_15518 : Nat := 4983230072969 + 3 ^ 40 * 15518 * 2
def baseEnd_15518 : Nat := 7082838041400461736569

theorem tailTrace_15518 : CollatzResearch.WordTrace tailWord_15518 prefixEnd_15518 7082838041400461736569 := by
  unfold tailWord_15518
  simp only [CollatzResearch.WordTrace]
  refine ⟨70748494723551388563901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 377325305192274072340805 70748494723551388563901)
  ·
    refine ⟨26530685521331770711463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70748494723551388563901 26530685521331770711463)
    ·
      refine ⟨39796028281997656067195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26530685521331770711463 39796028281997656067195)
      ·
        refine ⟨59694042422996484100793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39796028281997656067195 59694042422996484100793)
        ·
          refine ⟨44770531817247363075595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59694042422996484100793 44770531817247363075595)
          ·
            refine ⟨67155797725871044613393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44770531817247363075595 67155797725871044613393)
            ·
              refine ⟨50366848294403283460045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67155797725871044613393 50366848294403283460045)
              ·
                refine ⟨18887568110401231297517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50366848294403283460045 18887568110401231297517)
                ·
                  refine ⟨7082838041400461736569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18887568110401231297517 7082838041400461736569)
                  ·
                    rfl

theorem cell20_15518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_15518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15518 prefixEnd_15518 := by exact prefixLift 15518
  have htrace : WordTrace (prefixWord ++ tailWord_15518) baseStart_15518 baseEnd_15518 := by
    simpa [prefixWord, tailWord_15518, baseEnd_15518] using wordTrace_append hprefix tailTrace_15518
  have hstable : (prefixWord ++ tailWord_15518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15518).length < 2 ^ (prefixWord ++ tailWord_15518).sum := by decide
  have hdescent : baseEnd_15518 < baseStart_15518 := by decide
  rcases family_descends (prefixWord ++ tailWord_15518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15598 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_15598 : Nat := 118140960795 + 15598 * 2 ^ 59
def prefixEnd_15598 : Nat := 4983230072969 + 3 ^ 40 * 15598 * 2
def baseEnd_15598 : Nat := 7119352221275739069575

theorem tailTrace_15598 : CollatzResearch.WordTrace tailWord_15598 prefixEnd_15598 7119352221275739069575 := by
  unfold tailWord_15598
  simp only [CollatzResearch.WordTrace]
  refine ⟨71113224687323096427931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 379270531665723180948965 71113224687323096427931)
  ·
    refine ⟨106669837030984644641897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71113224687323096427931 106669837030984644641897)
    ·
      refine ⟨80002377773238483481423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106669837030984644641897 80002377773238483481423)
      ·
        refine ⟨120003566659857725222135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80002377773238483481423 120003566659857725222135)
        ·
          refine ⟨180005349989786587833203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120003566659857725222135 180005349989786587833203)
          ·
            refine ⟨270008024984679881749805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180005349989786587833203 270008024984679881749805)
            ·
              refine ⟨101253009369254955656177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270008024984679881749805 101253009369254955656177)
              ·
                refine ⟨75939757026941216742133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101253009369254955656177 75939757026941216742133)
                ·
                  refine ⟨7119352221275739069575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75939757026941216742133 7119352221275739069575)
                  ·
                    rfl

theorem cell20_15598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_15598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15598 prefixEnd_15598 := by exact prefixLift 15598
  have htrace : WordTrace (prefixWord ++ tailWord_15598) baseStart_15598 baseEnd_15598 := by
    simpa [prefixWord, tailWord_15598, baseEnd_15598] using wordTrace_append hprefix tailTrace_15598
  have hstable : (prefixWord ++ tailWord_15598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15598).length < 2 ^ (prefixWord ++ tailWord_15598).sum := by decide
  have hdescent : baseEnd_15598 < baseStart_15598 := by decide
  rcases family_descends (prefixWord ++ tailWord_15598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15604 : List Nat := [2, 6, 1, 2, 1, 2, 6]
def baseStart_15604 : Nat := 118140960795 + 15604 * 2 ^ 59
def prefixEnd_15604 : Nat := 4983230072969 + 3 ^ 40 * 15604 * 2
def baseEnd_15604 : Nat := 791343420529598318839

theorem tailTrace_15604 : CollatzResearch.WordTrace tailWord_15604 prefixEnd_15604 791343420529598318839 := by
  unfold tailWord_15604
  simp only [CollatzResearch.WordTrace]
  refine ⟨284562317738423898070933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 379416423651231864094577 284562317738423898070933)
  ·
    refine ⟨13338858643988620222075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284562317738423898070933 13338858643988620222075)
    ·
      refine ⟨20008287965982930333113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338858643988620222075 20008287965982930333113)
      ·
        refine ⟨15006215974487197749835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20008287965982930333113 15006215974487197749835)
        ·
          refine ⟨22509323961730796624753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15006215974487197749835 22509323961730796624753)
          ·
            refine ⟨16881992971298097468565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22509323961730796624753 16881992971298097468565)
            ·
              refine ⟨791343420529598318839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16881992971298097468565 791343420529598318839)
              ·
                rfl

theorem cell20_15604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_15604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15604 prefixEnd_15604 := by exact prefixLift 15604
  have htrace : WordTrace (prefixWord ++ tailWord_15604) baseStart_15604 baseEnd_15604 := by
    simpa [prefixWord, tailWord_15604, baseEnd_15604] using wordTrace_append hprefix tailTrace_15604
  have hstable : (prefixWord ++ tailWord_15604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15604).length < 2 ^ (prefixWord ++ tailWord_15604).sum := by decide
  have hdescent : baseEnd_15604 < baseStart_15604 := by decide
  rcases family_descends (prefixWord ++ tailWord_15604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15618 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_15618 : Nat := 118140960795 + 15618 * 2 ^ 59
def prefixEnd_15618 : Nat := 4983230072969 + 3 ^ 40 * 15618 * 2
def baseEnd_15618 : Nat := 7128480766244558402827

theorem tailTrace_15618 : CollatzResearch.WordTrace tailWord_15618 prefixEnd_15618 7128480766244558402827 := by
  unfold tailWord_15618
  simp only [CollatzResearch.WordTrace]
  refine ⟨142408814356532046787877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 379756838284085458101005 142408814356532046787877)
  ·
    refine ⟨26701652691849758772727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142408814356532046787877 26701652691849758772727)
    ·
      refine ⟨40052479037774638159091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26701652691849758772727 40052479037774638159091)
      ·
        refine ⟨60078718556661957238637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40052479037774638159091 60078718556661957238637)
        ·
          refine ⟨22529519458748233964489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60078718556661957238637 22529519458748233964489)
          ·
            refine ⟨16897139594061175473367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22529519458748233964489 16897139594061175473367)
            ·
              refine ⟨25345709391091763210051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897139594061175473367 25345709391091763210051)
              ·
                refine ⟨38018564086637644815077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25345709391091763210051 38018564086637644815077)
                ·
                  refine ⟨7128480766244558402827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38018564086637644815077 7128480766244558402827)
                  ·
                    rfl

theorem cell20_15618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_15618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15618 prefixEnd_15618 := by exact prefixLift 15618
  have htrace : WordTrace (prefixWord ++ tailWord_15618) baseStart_15618 baseEnd_15618 := by
    simpa [prefixWord, tailWord_15618, baseEnd_15618] using wordTrace_append hprefix tailTrace_15618
  have hstable : (prefixWord ++ tailWord_15618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15618).length < 2 ^ (prefixWord ++ tailWord_15618).sum := by decide
  have hdescent : baseEnd_15618 < baseStart_15618 := by decide
  rcases family_descends (prefixWord ++ tailWord_15618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15660 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_15660 : Nat := 118140960795 + 15660 * 2 ^ 59
def prefixEnd_15660 : Nat := 4983230072969 + 3 ^ 40 * 15660 * 2
def baseEnd_15660 : Nat := 7147650710679079002655

theorem tailTrace_15660 : CollatzResearch.WordTrace tailWord_15660 prefixEnd_15660 7147650710679079002655 := by
  unfold tailWord_15660
  simp only [CollatzResearch.WordTrace]
  refine ⟨285583561636984680090217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 380778082182646240120289 285583561636984680090217)
  ·
    refine ⟨214187671227738510067663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285583561636984680090217 214187671227738510067663)
    ·
      refine ⟨321281506841607765101495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214187671227738510067663 321281506841607765101495)
      ·
        refine ⟨481922260262411647652243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321281506841607765101495 481922260262411647652243)
        ·
          refine ⟨722883390393617471478365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481922260262411647652243 722883390393617471478365)
          ·
            refine ⟨271081271397606551804387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722883390393617471478365 271081271397606551804387)
            ·
              refine ⟨406621907096409827706581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271081271397606551804387 406621907096409827706581)
              ·
                refine ⟨9530200947572105336873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 406621907096409827706581 9530200947572105336873)
                ·
                  refine ⟨7147650710679079002655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9530200947572105336873 7147650710679079002655)
                  ·
                    rfl

theorem cell20_15660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_15660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15660 prefixEnd_15660 := by exact prefixLift 15660
  have htrace : WordTrace (prefixWord ++ tailWord_15660) baseStart_15660 baseEnd_15660 := by
    simpa [prefixWord, tailWord_15660, baseEnd_15660] using wordTrace_append hprefix tailTrace_15660
  have hstable : (prefixWord ++ tailWord_15660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15660).length < 2 ^ (prefixWord ++ tailWord_15660).sum := by decide
  have hdescent : baseEnd_15660 < baseStart_15660 := by decide
  rcases family_descends (prefixWord ++ tailWord_15660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15673 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 2]
def baseStart_15673 : Nat := 118140960795 + 15673 * 2 ^ 59
def prefixEnd_15673 : Nat := 4983230072969 + 3 ^ 40 * 15673 * 2
def baseEnd_15673 : Nat := 7153584264908811569269

theorem tailTrace_15673 : CollatzResearch.WordTrace tailWord_15673 prefixEnd_15673 7153584264908811569269 := by
  unfold tailWord_15673
  simp only [CollatzResearch.WordTrace]
  refine ⟨571641272226872580403673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 381094181484581720269115 571641272226872580403673)
  ·
    refine ⟨428730954170154435302755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 571641272226872580403673 428730954170154435302755)
    ·
      refine ⟨643096431255231652954133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428730954170154435302755 643096431255231652954133)
      ·
        refine ⟨30145145215088983732225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 643096431255231652954133 30145145215088983732225)
        ·
          refine ⟨22608858911316737799169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30145145215088983732225 22608858911316737799169)
          ·
            refine ⟨16956644183487553349377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22608858911316737799169 16956644183487553349377)
            ·
              refine ⟨12717483137615665012033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16956644183487553349377 12717483137615665012033)
              ·
                refine ⟨9538112353211748759025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12717483137615665012033 9538112353211748759025)
                ·
                  refine ⟨7153584264908811569269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9538112353211748759025 7153584264908811569269)
                  ·
                    rfl

theorem cell20_15673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_15673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15673 prefixEnd_15673 := by exact prefixLift 15673
  have htrace : WordTrace (prefixWord ++ tailWord_15673) baseStart_15673 baseEnd_15673 := by
    simpa [prefixWord, tailWord_15673, baseEnd_15673] using wordTrace_append hprefix tailTrace_15673
  have hstable : (prefixWord ++ tailWord_15673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15673).length < 2 ^ (prefixWord ++ tailWord_15673).sum := by decide
  have hdescent : baseEnd_15673 < baseStart_15673 := by decide
  rcases family_descends (prefixWord ++ tailWord_15673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15684 : List Nat := [2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_15684 : Nat := 118140960795 + 15684 * 2 ^ 59
def prefixEnd_15684 : Nat := 4983230072969 + 3 ^ 40 * 15684 * 2
def baseEnd_15684 : Nat := 2386201654880554067519

theorem tailTrace_15684 : CollatzResearch.WordTrace tailWord_15684 prefixEnd_15684 2386201654880554067519 := by
  unfold tailWord_15684
  simp only [CollatzResearch.WordTrace]
  refine ⟨286021237593510729527053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 381361650124680972702737 286021237593510729527053)
  ·
    refine ⟨107257964097566523572645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286021237593510729527053 107257964097566523572645)
    ·
      refine ⟨20110868268293723169871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107257964097566523572645 20110868268293723169871)
      ·
        refine ⟨30166302402440584754807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20110868268293723169871 30166302402440584754807)
        ·
          refine ⟨45249453603660877132211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30166302402440584754807 45249453603660877132211)
          ·
            refine ⟨67874180405491315698317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45249453603660877132211 67874180405491315698317)
            ·
              refine ⟨25452817652059243386869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67874180405491315698317 25452817652059243386869)
              ·
                refine ⟨2386201654880554067519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25452817652059243386869 2386201654880554067519)
                ·
                  rfl

theorem cell20_15684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_15684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15684 prefixEnd_15684 := by exact prefixLift 15684
  have htrace : WordTrace (prefixWord ++ tailWord_15684) baseStart_15684 baseEnd_15684 := by
    simpa [prefixWord, tailWord_15684, baseEnd_15684] using wordTrace_append hprefix tailTrace_15684
  have hstable : (prefixWord ++ tailWord_15684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15684).length < 2 ^ (prefixWord ++ tailWord_15684).sum := by decide
  have hdescent : baseEnd_15684 < baseStart_15684 := by decide
  rcases family_descends (prefixWord ++ tailWord_15684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15715 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 2]
def baseStart_15715 : Nat := 118140960795 + 15715 * 2 ^ 59
def prefixEnd_15715 : Nat := 4983230072969 + 3 ^ 40 * 15715 * 2
def baseEnd_15715 : Nat := 7172754209343332169097

theorem tailTrace_15715 : CollatzResearch.WordTrace tailWord_15715 prefixEnd_15715 7172754209343332169097 := by
  unfold tailWord_15715
  simp only [CollatzResearch.WordTrace]
  refine ⟨573173138074713753432599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 382115425383142502288399 573173138074713753432599)
  ·
    refine ⟨859759707112070630148899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573173138074713753432599 859759707112070630148899)
    ·
      refine ⟨1289639560668105945223349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859759707112070630148899 1289639560668105945223349)
      ·
        refine ⟨120903708812634932364689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1289639560668105945223349 120903708812634932364689)
        ·
          refine ⟨90677781609476199273517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120903708812634932364689 90677781609476199273517)
          ·
            refine ⟨34004168103553574727569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90677781609476199273517 34004168103553574727569)
            ·
              refine ⟨25503126077665181045677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34004168103553574727569 25503126077665181045677)
              ·
                refine ⟨9563672279124442892129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25503126077665181045677 9563672279124442892129)
                ·
                  refine ⟨7172754209343332169097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9563672279124442892129 7172754209343332169097)
                  ·
                    rfl

theorem cell20_15715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2].length) (baseStart_15715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15715 prefixEnd_15715 := by exact prefixLift 15715
  have htrace : WordTrace (prefixWord ++ tailWord_15715) baseStart_15715 baseEnd_15715 := by
    simpa [prefixWord, tailWord_15715, baseEnd_15715] using wordTrace_append hprefix tailTrace_15715
  have hstable : (prefixWord ++ tailWord_15715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15715).length < 2 ^ (prefixWord ++ tailWord_15715).sum := by decide
  have hdescent : baseEnd_15715 < baseStart_15715 := by decide
  rcases family_descends (prefixWord ++ tailWord_15715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15742 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_15742 : Nat := 118140960795 + 15742 * 2 ^ 59
def prefixEnd_15742 : Nat := 4983230072969 + 3 ^ 40 * 15742 * 2
def baseEnd_15742 : Nat := 7185077745051238268987

theorem tailTrace_15742 : CollatzResearch.WordTrace tailWord_15742 prefixEnd_15742 7185077745051238268987 := by
  unfold tailWord_15742
  simp only [CollatzResearch.WordTrace]
  refine ⟨71769738622112170583185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 382771939317931576443653 71769738622112170583185)
  ·
    refine ⟨53827303966584127937389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71769738622112170583185 53827303966584127937389)
    ·
      refine ⟨20185238987469047976521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53827303966584127937389 20185238987469047976521)
      ·
        refine ⟨15138929240601785982391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20185238987469047976521 15138929240601785982391)
        ·
          refine ⟨22708393860902678973587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138929240601785982391 22708393860902678973587)
          ·
            refine ⟨34062590791354018460381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22708393860902678973587 34062590791354018460381)
            ·
              refine ⟨12773471546757756922643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34062590791354018460381 12773471546757756922643)
              ·
                refine ⟨19160207320136635383965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773471546757756922643 19160207320136635383965)
                ·
                  refine ⟨7185077745051238268987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19160207320136635383965 7185077745051238268987)
                  ·
                    rfl

theorem cell20_15742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_15742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15742 prefixEnd_15742 := by exact prefixLift 15742
  have htrace : WordTrace (prefixWord ++ tailWord_15742) baseStart_15742 baseEnd_15742 := by
    simpa [prefixWord, tailWord_15742, baseEnd_15742] using wordTrace_append hprefix tailTrace_15742
  have hstable : (prefixWord ++ tailWord_15742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15742).length < 2 ^ (prefixWord ++ tailWord_15742).sum := by decide
  have hdescent : baseEnd_15742 < baseStart_15742 := by decide
  rcases family_descends (prefixWord ++ tailWord_15742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15801 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 3]
def baseStart_15801 : Nat := 118140960795 + 15801 * 2 ^ 59
def prefixEnd_15801 : Nat := 4983230072969 + 3 ^ 40 * 15801 * 2
def baseEnd_15801 : Nat := 7212006952709255302079

theorem tailTrace_15801 : CollatzResearch.WordTrace tailWord_15801 prefixEnd_15801 7212006952709255302079 := by
  unfold tailWord_15801
  simp only [CollatzResearch.WordTrace]
  refine ⟨576309815763150441063257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 384206543842100294042171 576309815763150441063257)
  ·
    refine ⟨432232361822362830797443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 576309815763150441063257 432232361822362830797443)
    ·
      refine ⟨648348542733544246196165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432232361822362830797443 648348542733544246196165)
      ·
        refine ⟨121565351762539546161781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 648348542733544246196165 121565351762539546161781)
        ·
          refine ⟨11396751727738082452667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121565351762539546161781 11396751727738082452667)
          ·
            refine ⟨17095127591607123679001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396751727738082452667 17095127591607123679001)
            ·
              refine ⟨12821345693705342759251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17095127591607123679001 12821345693705342759251)
              ·
                refine ⟨19232018540558014138877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821345693705342759251 19232018540558014138877)
                ·
                  refine ⟨7212006952709255302079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19232018540558014138877 7212006952709255302079)
                  ·
                    rfl

theorem cell20_15801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_15801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15801 prefixEnd_15801 := by exact prefixLift 15801
  have htrace : WordTrace (prefixWord ++ tailWord_15801) baseStart_15801 baseEnd_15801 := by
    simpa [prefixWord, tailWord_15801, baseEnd_15801] using wordTrace_append hprefix tailTrace_15801
  have hstable : (prefixWord ++ tailWord_15801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15801).length < 2 ^ (prefixWord ++ tailWord_15801).sum := by decide
  have hdescent : baseEnd_15801 < baseStart_15801 := by decide
  rcases family_descends (prefixWord ++ tailWord_15801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15843 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_15843 : Nat := 118140960795 + 15843 * 2 ^ 59
def prefixEnd_15843 : Nat := 4983230072969 + 3 ^ 40 * 15843 * 2
def baseEnd_15843 : Nat := 7231176897143775901907

theorem tailTrace_15843 : CollatzResearch.WordTrace tailWord_15843 prefixEnd_15843 7231176897143775901907 := by
  unfold tailWord_15843
  simp only [CollatzResearch.WordTrace]
  refine ⟨577841681610991614092183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 385227787740661076061455 577841681610991614092183)
  ·
    refine ⟨866762522416487421138275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577841681610991614092183 866762522416487421138275)
    ·
      refine ⟨1300143783624731131707413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866762522416487421138275 1300143783624731131707413)
      ·
        refine ⟨60944239857409271798785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1300143783624731131707413 60944239857409271798785)
        ·
          refine ⟨45708179893056953849089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60944239857409271798785 45708179893056953849089)
          ·
            refine ⟨34281134919792715386817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45708179893056953849089 34281134919792715386817)
            ·
              refine ⟨25710851189844536540113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34281134919792715386817 25710851189844536540113)
              ·
                refine ⟨19283138392383402405085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25710851189844536540113 19283138392383402405085)
                ·
                  refine ⟨7231176897143775901907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19283138392383402405085 7231176897143775901907)
                  ·
                    rfl

theorem cell20_15843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_15843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15843 prefixEnd_15843 := by exact prefixLift 15843
  have htrace : WordTrace (prefixWord ++ tailWord_15843) baseStart_15843 baseEnd_15843 := by
    simpa [prefixWord, tailWord_15843, baseEnd_15843] using wordTrace_append hprefix tailTrace_15843
  have hstable : (prefixWord ++ tailWord_15843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15843).length < 2 ^ (prefixWord ++ tailWord_15843).sum := by decide
  have hdescent : baseEnd_15843 < baseStart_15843 := by decide
  rcases family_descends (prefixWord ++ tailWord_15843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15853 : List Nat := [1, 5, 1, 3, 3, 1, 1, 5]
def baseStart_15853 : Nat := 118140960795 + 15853 * 2 ^ 59
def prefixEnd_15853 : Nat := 4983230072969 + 3 ^ 40 * 15853 * 2
def baseEnd_15853 : Nat := 2411913723209395189511

theorem tailTrace_15853 : CollatzResearch.WordTrace tailWord_15853 prefixEnd_15853 2411913723209395189511 := by
  unfold tailWord_15853
  simp only [CollatzResearch.WordTrace]
  refine ⟨578206411574763321956213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 385470941049842214637475 578206411574763321956213)
  ·
    refine ⟨54206851085134061433395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 578206411574763321956213 54206851085134061433395)
    ·
      refine ⟨81310276627701092150093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54206851085134061433395 81310276627701092150093)
      ·
        refine ⟨30491353735387909556285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81310276627701092150093 30491353735387909556285)
        ·
          refine ⟨11434257650770466083607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30491353735387909556285 11434257650770466083607)
          ·
            refine ⟨17151386476155699125411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434257650770466083607 17151386476155699125411)
            ·
              refine ⟨25727079714233548688117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17151386476155699125411 25727079714233548688117)
              ·
                refine ⟨2411913723209395189511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25727079714233548688117 2411913723209395189511)
                ·
                  rfl

theorem cell20_15853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_15853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15853 prefixEnd_15853 := by exact prefixLift 15853
  have htrace : WordTrace (prefixWord ++ tailWord_15853) baseStart_15853 baseEnd_15853 := by
    simpa [prefixWord, tailWord_15853, baseEnd_15853] using wordTrace_append hprefix tailTrace_15853
  have hstable : (prefixWord ++ tailWord_15853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15853).length < 2 ^ (prefixWord ++ tailWord_15853).sum := by decide
  have hdescent : baseEnd_15853 < baseStart_15853 := by decide
  rcases family_descends (prefixWord ++ tailWord_15853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15857 : List Nat := [1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_15857 : Nat := 118140960795 + 15857 * 2 ^ 59
def prefixEnd_15857 : Nat := 4983230072969 + 3 ^ 40 * 15857 * 2
def baseEnd_15857 : Nat := 2412522292873983145061

theorem tailTrace_15857 : CollatzResearch.WordTrace tailWord_15857 prefixEnd_15857 2412522292873983145061 := by
  unfold tailWord_15857
  simp only [CollatzResearch.WordTrace]
  refine ⟨578352303560272005101825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 385568202373514670067883 578352303560272005101825)
  ·
    refine ⟨433764227670204003826369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 578352303560272005101825 433764227670204003826369)
    ·
      refine ⟨325323170752653002869777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433764227670204003826369 325323170752653002869777)
      ·
        refine ⟨243992378064489752152333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325323170752653002869777 243992378064489752152333)
        ·
          refine ⟨91497141774183657057125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243992378064489752152333 91497141774183657057125)
          ·
            refine ⟨17155714082659435698211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91497141774183657057125 17155714082659435698211)
            ·
              refine ⟨25733571123989153547317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155714082659435698211 25733571123989153547317)
              ·
                refine ⟨2412522292873983145061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25733571123989153547317 2412522292873983145061)
                ·
                  rfl

theorem cell20_15857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_15857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15857 prefixEnd_15857 := by exact prefixLift 15857
  have htrace : WordTrace (prefixWord ++ tailWord_15857) baseStart_15857 baseEnd_15857 := by
    simpa [prefixWord, tailWord_15857, baseEnd_15857] using wordTrace_append hprefix tailTrace_15857
  have hstable : (prefixWord ++ tailWord_15857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15857).length < 2 ^ (prefixWord ++ tailWord_15857).sum := by decide
  have hdescent : baseEnd_15857 < baseStart_15857 := by decide
  rcases family_descends (prefixWord ++ tailWord_15857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15864 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_15864 : Nat := 118140960795 + 15864 * 2 ^ 59
def prefixEnd_15864 : Nat := 4983230072969 + 3 ^ 40 * 15864 * 2
def baseEnd_15864 : Nat := 7240761869361036201821

theorem tailTrace_15864 : CollatzResearch.WordTrace tailWord_15864 prefixEnd_15864 7240761869361036201821 := by
  unfold tailWord_15864
  simp only [CollatzResearch.WordTrace]
  refine ⟨289303807267456100303323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 385738409689941467071097 289303807267456100303323)
  ·
    refine ⟨433955710901184150454985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289303807267456100303323 433955710901184150454985)
    ·
      refine ⟨325466783175888112841239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433955710901184150454985 325466783175888112841239)
      ·
        refine ⟨488200174763832169261859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325466783175888112841239 488200174763832169261859)
        ·
          refine ⟨732300262145748253892789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488200174763832169261859 732300262145748253892789)
          ·
            refine ⟨68653149576163898802449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 732300262145748253892789 68653149576163898802449)
            ·
              refine ⟨51489862182122924101837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68653149576163898802449 51489862182122924101837)
              ·
                refine ⟨19308698318296096538189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51489862182122924101837 19308698318296096538189)
                ·
                  refine ⟨7240761869361036201821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19308698318296096538189 7240761869361036201821)
                  ·
                    rfl

theorem cell20_15864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_15864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15864 prefixEnd_15864 := by exact prefixLift 15864
  have htrace : WordTrace (prefixWord ++ tailWord_15864) baseStart_15864 baseEnd_15864 := by
    simpa [prefixWord, tailWord_15864, baseEnd_15864] using wordTrace_append hprefix tailTrace_15864
  have hstable : (prefixWord ++ tailWord_15864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15864).length < 2 ^ (prefixWord ++ tailWord_15864).sum := by decide
  have hdescent : baseEnd_15864 < baseStart_15864 := by decide
  rcases family_descends (prefixWord ++ tailWord_15864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15933 : List Nat := [1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_15933 : Nat := 118140960795 + 15933 * 2 ^ 59
def prefixEnd_15933 : Nat := 4983230072969 + 3 ^ 40 * 15933 * 2
def baseEnd_15933 : Nat := 2424085116501154300513

theorem tailTrace_15933 : CollatzResearch.WordTrace tailWord_15933 prefixEnd_15933 2424085116501154300513 := by
  unfold tailWord_15933
  simp only [CollatzResearch.WordTrace]
  refine ⟨581124251284936984868453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 387416167523291323245635 581124251284936984868453)
  ·
    refine ⟨108960797115925684662835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 581124251284936984868453 108960797115925684662835)
    ·
      refine ⟨163441195673888526994253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108960797115925684662835 163441195673888526994253)
      ·
        refine ⟨61290448377708197622845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163441195673888526994253 61290448377708197622845)
        ·
          refine ⟨22983918141640574108567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61290448377708197622845 22983918141640574108567)
          ·
            refine ⟨34475877212460861162851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22983918141640574108567 34475877212460861162851)
            ·
              refine ⟨51713815818691291744277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34475877212460861162851 51713815818691291744277)
              ·
                refine ⟨2424085116501154300513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51713815818691291744277 2424085116501154300513)
                ·
                  rfl

theorem cell20_15933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_15933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15933 prefixEnd_15933 := by exact prefixLift 15933
  have htrace : WordTrace (prefixWord ++ tailWord_15933) baseStart_15933 baseEnd_15933 := by
    simpa [prefixWord, tailWord_15933, baseEnd_15933] using wordTrace_append hprefix tailTrace_15933
  have hstable : (prefixWord ++ tailWord_15933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15933).length < 2 ^ (prefixWord ++ tailWord_15933).sum := by decide
  have hdescent : baseEnd_15933 < baseStart_15933 := by decide
  rcases family_descends (prefixWord ++ tailWord_15933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15954 : List Nat := [3, 2, 2, 1, 2, 2, 8]
def baseStart_15954 : Nat := 118140960795 + 15954 * 2 ^ 59
def prefixEnd_15954 : Nat := 4983230072969 + 3 ^ 40 * 15954 * 2
def baseEnd_15954 : Nat := 809093369080080355717

theorem tailTrace_15954 : CollatzResearch.WordTrace tailWord_15954 prefixEnd_15954 809093369080080355717 := by
  unfold tailWord_15954
  simp only [CollatzResearch.WordTrace]
  refine ⟨145472546052214392845729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 387926789472571714255277 145472546052214392845729)
  ·
    refine ⟨109104409539160794634297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145472546052214392845729 109104409539160794634297)
    ·
      refine ⟨81828307154370595975723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109104409539160794634297 81828307154370595975723)
      ·
        refine ⟨122742460731555893963585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81828307154370595975723 122742460731555893963585)
        ·
          refine ⟨92056845548666920472689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122742460731555893963585 92056845548666920472689)
          ·
            refine ⟨69042634161500190354517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92056845548666920472689 69042634161500190354517)
            ·
              refine ⟨809093369080080355717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69042634161500190354517 809093369080080355717)
              ·
                rfl

theorem cell20_15954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_15954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15954 prefixEnd_15954 := by exact prefixLift 15954
  have htrace : WordTrace (prefixWord ++ tailWord_15954) baseStart_15954 baseEnd_15954 := by
    simpa [prefixWord, tailWord_15954, baseEnd_15954] using wordTrace_append hprefix tailTrace_15954
  have hstable : (prefixWord ++ tailWord_15954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15954).length < 2 ^ (prefixWord ++ tailWord_15954).sum := by decide
  have hdescent : baseEnd_15954 < baseStart_15954 := by decide
  rcases family_descends (prefixWord ++ tailWord_15954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15964 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_15964 : Nat := 118140960795 + 15964 * 2 ^ 59
def prefixEnd_15964 : Nat := 4983230072969 + 3 ^ 40 * 15964 * 2
def baseEnd_15964 : Nat := 7286404594205132868079

theorem tailTrace_15964 : CollatzResearch.WordTrace tailWord_15964 prefixEnd_15964 7286404594205132868079 := by
  unfold tailWord_15964
  simp only [CollatzResearch.WordTrace]
  refine ⟨291127457086314639623473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 388169942781752852831297 291127457086314639623473)
  ·
    refine ⟨218345592814735979717605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291127457086314639623473 218345592814735979717605)
    ·
      refine ⟨40939798652762996197051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218345592814735979717605 40939798652762996197051)
      ·
        refine ⟨61409697979144494295577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40939798652762996197051 61409697979144494295577)
        ·
          refine ⟨46057273484358370721683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61409697979144494295577 46057273484358370721683)
          ·
            refine ⟨69085910226537556082525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46057273484358370721683 69085910226537556082525)
            ·
              refine ⟨25907216334951583530947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69085910226537556082525 25907216334951583530947)
              ·
                refine ⟨38860824502427375296421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25907216334951583530947 38860824502427375296421)
                ·
                  refine ⟨7286404594205132868079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38860824502427375296421 7286404594205132868079)
                  ·
                    rfl

theorem cell20_15964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_15964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_15964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_15964 prefixEnd_15964 := by exact prefixLift 15964
  have htrace : WordTrace (prefixWord ++ tailWord_15964) baseStart_15964 baseEnd_15964 := by
    simpa [prefixWord, tailWord_15964, baseEnd_15964] using wordTrace_append hprefix tailTrace_15964
  have hstable : (prefixWord ++ tailWord_15964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15964).length < 2 ^ (prefixWord ++ tailWord_15964).sum := by decide
  have hdescent : baseEnd_15964 < baseStart_15964 := by decide
  rcases family_descends (prefixWord ++ tailWord_15964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16013 : List Nat := [1, 19]
def baseStart_16013 : Nat := 118140960795 + 16013 * 2 ^ 59
def prefixEnd_16013 : Nat := 4983230072969 + 3 ^ 40 * 16013 * 2
def baseEnd_16013 : Nat := 3341915651293434035

theorem tailTrace_16013 : CollatzResearch.WordTrace tailWord_16013 prefixEnd_16013 3341915651293434035 := by
  unfold tailWord_16013
  simp only [CollatzResearch.WordTrace]
  refine ⟨584042090995110647780693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 389361393996740431853795 584042090995110647780693)
  ·
    refine ⟨3341915651293434035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 19 584042090995110647780693 3341915651293434035)
    ·
      rfl

theorem cell20_16013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 19].length) (baseStart_16013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16013 prefixEnd_16013 := by exact prefixLift 16013
  have htrace : WordTrace (prefixWord ++ tailWord_16013) baseStart_16013 baseEnd_16013 := by
    simpa [prefixWord, tailWord_16013, baseEnd_16013] using wordTrace_append hprefix tailTrace_16013
  have hstable : (prefixWord ++ tailWord_16013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16013).length < 2 ^ (prefixWord ++ tailWord_16013).sum := by decide
  have hdescent : baseEnd_16013 < baseStart_16013 := by decide
  rcases family_descends (prefixWord ++ tailWord_16013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16068 : List Nat := [2, 3, 3, 1, 1, 1, 9]
def baseStart_16068 : Nat := 118140960795 + 16068 * 2 ^ 59
def prefixEnd_16068 : Nat := 4983230072969 + 3 ^ 40 * 16068 * 2
def baseEnd_16068 : Nat := 814874780893665933443

theorem tailTrace_16068 : CollatzResearch.WordTrace tailWord_16068 prefixEnd_16068 814874780893665933443 := by
  unfold tailWord_16068
  simp only [CollatzResearch.WordTrace]
  refine ⟨293024052897927520516429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 390698737197236694021905 293024052897927520516429)
  ·
    refine ⟨109884019836722820193661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293024052897927520516429 109884019836722820193661)
    ·
      refine ⟨41206507438771057572623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109884019836722820193661 41206507438771057572623)
      ·
        refine ⟨61809761158156586358935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41206507438771057572623 61809761158156586358935)
        ·
          refine ⟨92714641737234879538403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61809761158156586358935 92714641737234879538403)
          ·
            refine ⟨139071962605852319307605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92714641737234879538403 139071962605852319307605)
            ·
              refine ⟨814874780893665933443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 139071962605852319307605 814874780893665933443)
              ·
                rfl

theorem cell20_16068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_16068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16068 prefixEnd_16068 := by exact prefixLift 16068
  have htrace : WordTrace (prefixWord ++ tailWord_16068) baseStart_16068 baseEnd_16068 := by
    simpa [prefixWord, tailWord_16068, baseEnd_16068] using wordTrace_append hprefix tailTrace_16068
  have hstable : (prefixWord ++ tailWord_16068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16068).length < 2 ^ (prefixWord ++ tailWord_16068).sum := by decide
  have hdescent : baseEnd_16068 < baseStart_16068 := by decide
  rcases family_descends (prefixWord ++ tailWord_16068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16078 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_16078 : Nat := 118140960795 + 16078 * 2 ^ 59
def prefixEnd_16078 : Nat := 4983230072969 + 3 ^ 40 * 16078 * 2
def baseEnd_16078 : Nat := 7338437300527403067613

theorem tailTrace_16078 : CollatzResearch.WordTrace tailWord_16078 prefixEnd_16078 7338437300527403067613 := by
  unfold tailWord_16078
  simp only [CollatzResearch.WordTrace]
  refine ⟨73301604469953343612111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 390941890506417832597925 73301604469953343612111)
  ·
    refine ⟨109952406704930015418167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73301604469953343612111 109952406704930015418167)
    ·
      refine ⟨164928610057395023127251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109952406704930015418167 164928610057395023127251)
      ·
        refine ⟨247392915086092534690877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164928610057395023127251 247392915086092534690877)
        ·
          refine ⟨92772343157284700509079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247392915086092534690877 92772343157284700509079)
          ·
            refine ⟨139158514735927050763619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92772343157284700509079 139158514735927050763619)
            ·
              refine ⟨208737772103890576145429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139158514735927050763619 208737772103890576145429)
              ·
                refine ⟨9784583067369870756817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208737772103890576145429 9784583067369870756817)
                ·
                  refine ⟨7338437300527403067613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9784583067369870756817 7338437300527403067613)
                  ·
                    rfl

theorem cell20_16078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_16078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16078 prefixEnd_16078 := by exact prefixLift 16078
  have htrace : WordTrace (prefixWord ++ tailWord_16078) baseStart_16078 baseEnd_16078 := by
    simpa [prefixWord, tailWord_16078, baseEnd_16078] using wordTrace_append hprefix tailTrace_16078
  have hstable : (prefixWord ++ tailWord_16078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16078).length < 2 ^ (prefixWord ++ tailWord_16078).sum := by decide
  have hdescent : baseEnd_16078 < baseStart_16078 := by decide
  rcases family_descends (prefixWord ++ tailWord_16078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16113 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_16113 : Nat := 118140960795 + 16113 * 2 ^ 59
def prefixEnd_16113 : Nat := 4983230072969 + 3 ^ 40 * 16113 * 2
def baseEnd_16113 : Nat := 7354412254222836900803

theorem tailTrace_16113 : CollatzResearch.WordTrace tailWord_16113 prefixEnd_16113 7354412254222836900803 := by
  unfold tailWord_16113
  simp only [CollatzResearch.WordTrace]
  refine ⟨587689390632827726420993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 391792927088551817613995 587689390632827726420993)
  ·
    refine ⟨440767042974620794815745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 587689390632827726420993 440767042974620794815745)
    ·
      refine ⟨330575282230965596111809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440767042974620794815745 330575282230965596111809)
      ·
        refine ⟨247931461673224197083857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330575282230965596111809 247931461673224197083857)
        ·
          refine ⟨185948596254918147812893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247931461673224197083857 185948596254918147812893)
          ·
            refine ⟨69730723595594305429835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185948596254918147812893 69730723595594305429835)
            ·
              refine ⟨104596085393391458144753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69730723595594305429835 104596085393391458144753)
              ·
                refine ⟨78447064045043593608565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104596085393391458144753 78447064045043593608565)
                ·
                  refine ⟨7354412254222836900803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78447064045043593608565 7354412254222836900803)
                  ·
                    rfl

theorem cell20_16113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_16113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16113 prefixEnd_16113 := by exact prefixLift 16113
  have htrace : WordTrace (prefixWord ++ tailWord_16113) baseStart_16113 baseEnd_16113 := by
    simpa [prefixWord, tailWord_16113, baseEnd_16113] using wordTrace_append hprefix tailTrace_16113
  have hstable : (prefixWord ++ tailWord_16113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16113).length < 2 ^ (prefixWord ++ tailWord_16113).sum := by decide
  have hdescent : baseEnd_16113 < baseStart_16113 := by decide
  rcases family_descends (prefixWord ++ tailWord_16113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16127 : List Nat := [1, 1, 2, 2, 1, 3, 10]
def baseStart_16127 : Nat := 118140960795 + 16127 * 2 ^ 59
def prefixEnd_16127 : Nat := 4983230072969 + 3 ^ 40 * 16127 * 2
def baseEnd_16127 : Nat := 817866915077890048231

theorem tailTrace_16127 : CollatzResearch.WordTrace tailWord_16127 prefixEnd_16127 817866915077890048231 := by
  unfold tailWord_16127
  simp only [CollatzResearch.WordTrace]
  refine ⟨588200012582108117430635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 392133341721405411620423 588200012582108117430635)
  ·
    refine ⟨882300018873162176145953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588200012582108117430635 882300018873162176145953)
    ·
      refine ⟨661725014154871632109465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882300018873162176145953 661725014154871632109465)
      ·
        refine ⟨496293760616153724082099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661725014154871632109465 496293760616153724082099)
        ·
          refine ⟨744440640924230586123149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496293760616153724082099 744440640924230586123149)
          ·
            refine ⟨279165240346586469796181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744440640924230586123149 279165240346586469796181)
            ·
              refine ⟨817866915077890048231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 279165240346586469796181 817866915077890048231)
              ·
                rfl

theorem cell20_16127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_16127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16127 prefixEnd_16127 := by exact prefixLift 16127
  have htrace : WordTrace (prefixWord ++ tailWord_16127) baseStart_16127 baseEnd_16127 := by
    simpa [prefixWord, tailWord_16127, baseEnd_16127] using wordTrace_append hprefix tailTrace_16127
  have hstable : (prefixWord ++ tailWord_16127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16127).length < 2 ^ (prefixWord ++ tailWord_16127).sum := by decide
  have hdescent : baseEnd_16127 < baseStart_16127 := by decide
  rcases family_descends (prefixWord ++ tailWord_16127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16130 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_16130 : Nat := 118140960795 + 16130 * 2 ^ 59
def prefixEnd_16130 : Nat := 4983230072969 + 3 ^ 40 * 16130 * 2
def baseEnd_16130 : Nat := 7362171517446333334067

theorem tailTrace_16130 : CollatzResearch.WordTrace tailWord_16130 prefixEnd_16130 7362171517446333334067 := by
  unfold tailWord_16130
  simp only [CollatzResearch.WordTrace]
  refine ⟨147077357892809907447461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 392206287714159753193229 147077357892809907447461)
  ·
    refine ⟨27577004604901857646399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147077357892809907447461 27577004604901857646399)
    ·
      refine ⟨41365506907352786469599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27577004604901857646399 41365506907352786469599)
      ·
        refine ⟨62048260361029179704399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41365506907352786469599 62048260361029179704399)
        ·
          refine ⟨93072390541543769556599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62048260361029179704399 93072390541543769556599)
          ·
            refine ⟨139608585812315654334899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93072390541543769556599 139608585812315654334899)
            ·
              refine ⟨209412878718473481502349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139608585812315654334899 209412878718473481502349)
              ·
                refine ⟨78529829519427555563381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209412878718473481502349 78529829519427555563381)
                ·
                  refine ⟨7362171517446333334067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78529829519427555563381 7362171517446333334067)
                  ·
                    rfl

theorem cell20_16130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_16130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16130 prefixEnd_16130 := by exact prefixLift 16130
  have htrace : WordTrace (prefixWord ++ tailWord_16130) baseStart_16130 baseEnd_16130 := by
    simpa [prefixWord, tailWord_16130, baseEnd_16130] using wordTrace_append hprefix tailTrace_16130
  have hstable : (prefixWord ++ tailWord_16130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16130).length < 2 ^ (prefixWord ++ tailWord_16130).sum := by decide
  have hdescent : baseEnd_16130 < baseStart_16130 := by decide
  rcases family_descends (prefixWord ++ tailWord_16130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16213 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_16213 : Nat := 118140960795 + 16213 * 2 ^ 59
def prefixEnd_16213 : Nat := 4983230072969 + 3 ^ 40 * 16213 * 2
def baseEnd_16213 : Nat := 7400054979066933567061

theorem tailTrace_16213 : CollatzResearch.WordTrace tailWord_16213 prefixEnd_16213 7400054979066933567061 := by
  unfold tailWord_16213
  simp only [CollatzResearch.WordTrace]
  refine ⟨591336690270544805061293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 394224460180363203374195 591336690270544805061293)
  ·
    refine ⟨221751258851454301897985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 591336690270544805061293 221751258851454301897985)
    ·
      refine ⟨166313444138590726423489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221751258851454301897985 166313444138590726423489)
      ·
        refine ⟨124735083103943044817617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166313444138590726423489 124735083103943044817617)
        ·
          refine ⟨93551312327957283613213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124735083103943044817617 93551312327957283613213)
          ·
            refine ⟨35081742122983981354955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93551312327957283613213 35081742122983981354955)
            ·
              refine ⟨52622613184475972032433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35081742122983981354955 52622613184475972032433)
              ·
                refine ⟨39466959888356979024325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52622613184475972032433 39466959888356979024325)
                ·
                  refine ⟨7400054979066933567061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39466959888356979024325 7400054979066933567061)
                  ·
                    rfl

theorem cell20_16213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_16213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16213 prefixEnd_16213 := by exact prefixLift 16213
  have htrace : WordTrace (prefixWord ++ tailWord_16213) baseStart_16213 baseEnd_16213 := by
    simpa [prefixWord, tailWord_16213, baseEnd_16213] using wordTrace_append hprefix tailTrace_16213
  have hstable : (prefixWord ++ tailWord_16213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16213).length < 2 ^ (prefixWord ++ tailWord_16213).sum := by decide
  have hdescent : baseEnd_16213 < baseStart_16213 := by decide
  rcases family_descends (prefixWord ++ tailWord_16213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16241 : List Nat := [1, 2, 2, 2, 1, 3, 9]
def baseStart_16241 : Nat := 118140960795 + 16241 * 2 ^ 59
def prefixEnd_16241 : Nat := 4983230072969 + 3 ^ 40 * 16241 * 2
def baseEnd_16241 : Nat := 823648326891475625957

theorem tailTrace_16241 : CollatzResearch.WordTrace tailWord_16241 prefixEnd_16241 823648326891475625957 := by
  unfold tailWord_16241
  simp only [CollatzResearch.WordTrace]
  refine ⟨592357934169105587080577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 394905289446070391387051 592357934169105587080577)
  ·
    refine ⟨444268450626829190310433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 592357934169105587080577 444268450626829190310433)
    ·
      refine ⟨333201337970121892732825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444268450626829190310433 333201337970121892732825)
      ·
        refine ⟨249901003477591419549619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333201337970121892732825 249901003477591419549619)
        ·
          refine ⟨374851505216387129324429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249901003477591419549619 374851505216387129324429)
          ·
            refine ⟨140569314456145173496661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374851505216387129324429 140569314456145173496661)
            ·
              refine ⟨823648326891475625957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 140569314456145173496661 823648326891475625957)
              ·
                rfl

theorem cell20_16241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_16241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16241 prefixEnd_16241 := by exact prefixLift 16241
  have htrace : WordTrace (prefixWord ++ tailWord_16241) baseStart_16241 baseEnd_16241 := by
    simpa [prefixWord, tailWord_16241, baseEnd_16241] using wordTrace_append hprefix tailTrace_16241
  have hstable : (prefixWord ++ tailWord_16241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16241).length < 2 ^ (prefixWord ++ tailWord_16241).sum := by decide
  have hdescent : baseEnd_16241 < baseStart_16241 := by decide
  rcases family_descends (prefixWord ++ tailWord_16241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16285 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 2]
def baseStart_16285 : Nat := 118140960795 + 16285 * 2 ^ 59
def prefixEnd_16285 : Nat := 4983230072969 + 3 ^ 40 * 16285 * 2
def baseEnd_16285 : Nat := 7432917740954683166767

theorem tailTrace_16285 : CollatzResearch.WordTrace tailWord_16285 prefixEnd_16285 7432917740954683166767 := by
  unfold tailWord_16285
  simp only [CollatzResearch.WordTrace]
  refine ⟨593962746009701101682309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 395975164006467401121539 593962746009701101682309)
  ·
    refine ⟨111368014876818956565433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 593962746009701101682309 111368014876818956565433)
    ·
      refine ⟨83526011157614217424075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111368014876818956565433 83526011157614217424075)
      ·
        refine ⟨125289016736421326136113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83526011157614217424075 125289016736421326136113)
        ·
          refine ⟨93966762552315994602085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125289016736421326136113 93966762552315994602085)
          ·
            refine ⟨17618767978559248987891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93966762552315994602085 17618767978559248987891)
            ·
              refine ⟨26428151967838873481837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17618767978559248987891 26428151967838873481837)
              ·
                refine ⟨9910556987939577555689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26428151967838873481837 9910556987939577555689)
                ·
                  refine ⟨7432917740954683166767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9910556987939577555689 7432917740954683166767)
                  ·
                    rfl

theorem cell20_16285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_16285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16285 prefixEnd_16285 := by exact prefixLift 16285
  have htrace : WordTrace (prefixWord ++ tailWord_16285) baseStart_16285 baseEnd_16285 := by
    simpa [prefixWord, tailWord_16285, baseEnd_16285] using wordTrace_append hprefix tailTrace_16285
  have hstable : (prefixWord ++ tailWord_16285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16285).length < 2 ^ (prefixWord ++ tailWord_16285).sum := by decide
  have hdescent : baseEnd_16285 < baseStart_16285 := by decide
  rcases family_descends (prefixWord ++ tailWord_16285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16303 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_16303 : Nat := 118140960795 + 16303 * 2 ^ 59
def prefixEnd_16303 : Nat := 4983230072969 + 3 ^ 40 * 16303 * 2
def baseEnd_16303 : Nat := 7441133431426620566693

theorem tailTrace_16303 : CollatzResearch.WordTrace tailWord_16303 prefixEnd_16303 7441133431426620566693 := by
  unfold tailWord_16303
  simp only [CollatzResearch.WordTrace]
  refine ⟨594619259944490175837563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 396412839962993450558375 594619259944490175837563)
  ·
    refine ⟨891928889916735263756345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 594619259944490175837563 891928889916735263756345)
    ·
      refine ⟨668946667437551447817259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 891928889916735263756345 668946667437551447817259)
      ·
        refine ⟨1003420001156327171725889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668946667437551447817259 1003420001156327171725889)
        ·
          refine ⟨752565000867245378794417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003420001156327171725889 752565000867245378794417)
          ·
            refine ⟨564423750650434034095813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752565000867245378794417 564423750650434034095813)
            ·
              refine ⟨105829453246956381392965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564423750650434034095813 105829453246956381392965)
              ·
                refine ⟨19843022483804321511181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105829453246956381392965 19843022483804321511181)
                ·
                  refine ⟨7441133431426620566693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19843022483804321511181 7441133431426620566693)
                  ·
                    rfl

theorem cell20_16303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_16303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16303 prefixEnd_16303 := by exact prefixLift 16303
  have htrace : WordTrace (prefixWord ++ tailWord_16303) baseStart_16303 baseEnd_16303 := by
    simpa [prefixWord, tailWord_16303, baseEnd_16303] using wordTrace_append hprefix tailTrace_16303
  have hstable : (prefixWord ++ tailWord_16303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16303).length < 2 ^ (prefixWord ++ tailWord_16303).sum := by decide
  have hdescent : baseEnd_16303 < baseStart_16303 := by decide
  rcases family_descends (prefixWord ++ tailWord_16303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16354 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_16354 : Nat := 118140960795 + 16354 * 2 ^ 59
def prefixEnd_16354 : Nat := 4983230072969 + 3 ^ 40 * 16354 * 2
def baseEnd_16354 : Nat := 7464411221097109866485

theorem tailTrace_16354 : CollatzResearch.WordTrace tailWord_16354 prefixEnd_16354 7464411221097109866485 := by
  unfold tailWord_16354
  simp only [CollatzResearch.WordTrace]
  refine ⟨149119845689931471486029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 397652921839817257296077 149119845689931471486029)
  ·
    refine ⟨55919942133724301807261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149119845689931471486029 55919942133724301807261)
    ·
      refine ⟨20969978300146613177723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55919942133724301807261 20969978300146613177723)
      ·
        refine ⟨31454967450219919766585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20969978300146613177723 31454967450219919766585)
        ·
          refine ⟨23591225587664939824939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31454967450219919766585 23591225587664939824939)
          ·
            refine ⟨35386838381497409737409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591225587664939824939 35386838381497409737409)
            ·
              refine ⟨26540128786123057303057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35386838381497409737409 26540128786123057303057)
              ·
                refine ⟨19905096589592292977293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26540128786123057303057 19905096589592292977293)
                ·
                  refine ⟨7464411221097109866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19905096589592292977293 7464411221097109866485)
                  ·
                    rfl

theorem cell20_16354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_16354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16354 prefixEnd_16354 := by exact prefixLift 16354
  have htrace : WordTrace (prefixWord ++ tailWord_16354) baseStart_16354 baseEnd_16354 := by
    simpa [prefixWord, tailWord_16354, baseEnd_16354] using wordTrace_append hprefix tailTrace_16354
  have hstable : (prefixWord ++ tailWord_16354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16354).length < 2 ^ (prefixWord ++ tailWord_16354).sum := by decide
  have hdescent : baseEnd_16354 < baseStart_16354 := by decide
  rcases family_descends (prefixWord ++ tailWord_16354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16355 : List Nat := [1, 1, 1, 6, 1, 10]
def baseStart_16355 : Nat := 118140960795 + 16355 * 2 ^ 59
def prefixEnd_16355 : Nat := 4983230072969 + 3 ^ 40 * 16355 * 2
def baseEnd_16355 : Nat := 276476579568353734561

theorem tailTrace_16355 : CollatzResearch.WordTrace tailWord_16355 prefixEnd_16355 276476579568353734561 := by
  unfold tailWord_16355
  simp only [CollatzResearch.WordTrace]
  refine ⟨596515855756103056730519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 397677237170735371153679 596515855756103056730519)
  ·
    refine ⟨894773783634154585095779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596515855756103056730519 894773783634154585095779)
    ·
      refine ⟨1342160675451231877643669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894773783634154585095779 1342160675451231877643669)
      ·
        refine ⟨62913781661776494264547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1342160675451231877643669 62913781661776494264547)
        ·
          refine ⟨94370672492664741396821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62913781661776494264547 94370672492664741396821)
          ·
            refine ⟨276476579568353734561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 94370672492664741396821 276476579568353734561)
            ·
              rfl

theorem cell20_16355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 10].length) (baseStart_16355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16355 prefixEnd_16355 := by exact prefixLift 16355
  have htrace : WordTrace (prefixWord ++ tailWord_16355) baseStart_16355 baseEnd_16355 := by
    simpa [prefixWord, tailWord_16355, baseEnd_16355] using wordTrace_append hprefix tailTrace_16355
  have hstable : (prefixWord ++ tailWord_16355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16355).length < 2 ^ (prefixWord ++ tailWord_16355).sum := by decide
  have hdescent : baseEnd_16355 < baseStart_16355 := by decide
  rcases family_descends (prefixWord ++ tailWord_16355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16379 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_16379 : Nat := 118140960795 + 16379 * 2 ^ 59
def prefixEnd_16379 : Nat := 4983230072969 + 3 ^ 40 * 16379 * 2
def baseEnd_16379 : Nat := 7475821902308134033049

theorem tailTrace_16379 : CollatzResearch.WordTrace tailWord_16379 prefixEnd_16379 7475821902308134033049 := by
  unfold tailWord_16379
  simp only [CollatzResearch.WordTrace]
  refine ⟨597391207669155155604191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 398260805112770103736127 597391207669155155604191)
  ·
    refine ⟨896086811503732733406287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 597391207669155155604191 896086811503732733406287)
    ·
      refine ⟨1344130217255599100109431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896086811503732733406287 1344130217255599100109431)
      ·
        refine ⟨2016195325883398650164147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344130217255599100109431 2016195325883398650164147)
        ·
          refine ⟨3024292988825097975246221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2016195325883398650164147 3024292988825097975246221)
          ·
            refine ⟨1134109870809411740717333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3024292988825097975246221 1134109870809411740717333)
            ·
              refine ⟨53161400194191175346125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1134109870809411740717333 53161400194191175346125)
              ·
                refine ⟨19935525072821690754797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53161400194191175346125 19935525072821690754797)
                ·
                  refine ⟨7475821902308134033049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19935525072821690754797 7475821902308134033049)
                  ·
                    rfl

theorem cell20_16379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_16379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16379 prefixEnd_16379 := by exact prefixLift 16379
  have htrace : WordTrace (prefixWord ++ tailWord_16379) baseStart_16379 baseEnd_16379 := by
    simpa [prefixWord, tailWord_16379, baseEnd_16379] using wordTrace_append hprefix tailTrace_16379
  have hstable : (prefixWord ++ tailWord_16379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16379).length < 2 ^ (prefixWord ++ tailWord_16379).sum := by decide
  have hdescent : baseEnd_16379 < baseStart_16379 := by decide
  rcases family_descends (prefixWord ++ tailWord_16379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16382 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_16382 : Nat := 118140960795 + 16382 * 2 ^ 59
def prefixEnd_16382 : Nat := 4983230072969 + 3 ^ 40 * 16382 * 2
def baseEnd_16382 : Nat := 7477191184053456933037

theorem tailTrace_16382 : CollatzResearch.WordTrace tailWord_16382 prefixEnd_16382 7477191184053456933037 := by
  unfold tailWord_16382
  simp only [CollatzResearch.WordTrace]
  refine ⟨74687578332285833495425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 398333751105524445308933 74687578332285833495425)
  ·
    refine ⟨56015683749214375121569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74687578332285833495425 56015683749214375121569)
    ·
      refine ⟨42011762811910781341177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56015683749214375121569 42011762811910781341177)
      ·
        refine ⟨31508822108933086005883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42011762811910781341177 31508822108933086005883)
        ·
          refine ⟨47263233163399629008825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31508822108933086005883 47263233163399629008825)
          ·
            refine ⟨35447424872549721756619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47263233163399629008825 35447424872549721756619)
            ·
              refine ⟨53171137308824582634929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35447424872549721756619 53171137308824582634929)
              ·
                refine ⟨39878352981618436976197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53171137308824582634929 39878352981618436976197)
                ·
                  refine ⟨7477191184053456933037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39878352981618436976197 7477191184053456933037)
                  ·
                    rfl

theorem cell20_16382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_16382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16382 prefixEnd_16382 := by exact prefixLift 16382
  have htrace : WordTrace (prefixWord ++ tailWord_16382) baseStart_16382 baseEnd_16382 := by
    simpa [prefixWord, tailWord_16382, baseEnd_16382] using wordTrace_append hprefix tailTrace_16382
  have hstable : (prefixWord ++ tailWord_16382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16382).length < 2 ^ (prefixWord ++ tailWord_16382).sum := by decide
  have hdescent : baseEnd_16382 < baseStart_16382 := by decide
  rcases family_descends (prefixWord ++ tailWord_16382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16400 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_16400 : Nat := 118140960795 + 16400 * 2 ^ 59
def prefixEnd_16400 : Nat := 4983230072969 + 3 ^ 40 * 16400 * 2
def baseEnd_16400 : Nat := 7485406874525394332963

theorem tailTrace_16400 : CollatzResearch.WordTrace tailWord_16400 prefixEnd_16400 7485406874525394332963 := by
  unfold tailWord_16400
  simp only [CollatzResearch.WordTrace]
  refine ⟨299078570296537871059327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 398771427062050494745769 299078570296537871059327)
  ·
    refine ⟨448617855444806806588991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299078570296537871059327 448617855444806806588991)
    ·
      refine ⟨672926783167210209883487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448617855444806806588991 672926783167210209883487)
      ·
        refine ⟨1009390174750815314825231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672926783167210209883487 1009390174750815314825231)
        ·
          refine ⟨1514085262126222972237847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009390174750815314825231 1514085262126222972237847)
          ·
            refine ⟨2271127893189334458356771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514085262126222972237847 2271127893189334458356771)
            ·
              refine ⟨3406691839784001687535157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271127893189334458356771 3406691839784001687535157)
              ·
                refine ⟨319377359979750158206421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3406691839784001687535157 319377359979750158206421)
                ·
                  refine ⟨7485406874525394332963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319377359979750158206421 7485406874525394332963)
                  ·
                    rfl

theorem cell20_16400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_16400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16400 prefixEnd_16400 := by exact prefixLift 16400
  have htrace : WordTrace (prefixWord ++ tailWord_16400) baseStart_16400 baseEnd_16400 := by
    simpa [prefixWord, tailWord_16400, baseEnd_16400] using wordTrace_append hprefix tailTrace_16400
  have hstable : (prefixWord ++ tailWord_16400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16400).length < 2 ^ (prefixWord ++ tailWord_16400).sum := by decide
  have hdescent : baseEnd_16400 < baseStart_16400 := by decide
  rcases family_descends (prefixWord ++ tailWord_16400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16403 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 2]
def baseStart_16403 : Nat := 118140960795 + 16403 * 2 ^ 59
def prefixEnd_16403 : Nat := 4983230072969 + 3 ^ 40 * 16403 * 2
def baseEnd_16403 : Nat := 7486776156270717232951

theorem tailTrace_16403 : CollatzResearch.WordTrace tailWord_16403 prefixEnd_16403 7486776156270717232951 := by
  unfold tailWord_16403
  simp only [CollatzResearch.WordTrace]
  refine ⟨598266559582207254477863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 398844373054804836318575 598266559582207254477863)
  ·
    refine ⟨897399839373310881716795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598266559582207254477863 897399839373310881716795)
    ·
      refine ⟨1346099759059966322575193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897399839373310881716795 1346099759059966322575193)
      ·
        refine ⟨1009574819294974741931395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1346099759059966322575193 1009574819294974741931395)
        ·
          refine ⟨1514362228942462112897093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009574819294974741931395 1514362228942462112897093)
          ·
            refine ⟨283942917926711646168205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1514362228942462112897093 283942917926711646168205)
            ·
              refine ⟨106478594222516867313077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283942917926711646168205 106478594222516867313077)
              ·
                refine ⟨9982368208360956310601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106478594222516867313077 9982368208360956310601)
                ·
                  refine ⟨7486776156270717232951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9982368208360956310601 7486776156270717232951)
                  ·
                    rfl

theorem cell20_16403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2].length) (baseStart_16403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16403 prefixEnd_16403 := by exact prefixLift 16403
  have htrace : WordTrace (prefixWord ++ tailWord_16403) baseStart_16403 baseEnd_16403 := by
    simpa [prefixWord, tailWord_16403, baseEnd_16403] using wordTrace_append hprefix tailTrace_16403
  have hstable : (prefixWord ++ tailWord_16403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16403).length < 2 ^ (prefixWord ++ tailWord_16403).sum := by decide
  have hdescent : baseEnd_16403 < baseStart_16403 := by decide
  rcases family_descends (prefixWord ++ tailWord_16403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16413 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_16413 : Nat := 118140960795 + 16413 * 2 ^ 59
def prefixEnd_16413 : Nat := 4983230072969 + 3 ^ 40 * 16413 * 2
def baseEnd_16413 : Nat := 7491340428755126899577

theorem tailTrace_16413 : CollatzResearch.WordTrace tailWord_16413 prefixEnd_16413 7491340428755126899577 := by
  unfold tailWord_16413
  simp only [CollatzResearch.WordTrace]
  refine ⟨598631289545978962341893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 399087526363985974894595 598631289545978962341893)
  ·
    refine ⟨112243366789871055439105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 598631289545978962341893 112243366789871055439105)
    ·
      refine ⟨84182525092403291579329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112243366789871055439105 84182525092403291579329)
      ·
        refine ⟨63136893819302468684497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84182525092403291579329 63136893819302468684497)
        ·
          refine ⟨47352670364476851513373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63136893819302468684497 47352670364476851513373)
          ·
            refine ⟨17757251386678819317515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47352670364476851513373 17757251386678819317515)
            ·
              refine ⟨26635877080018228976273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757251386678819317515 26635877080018228976273)
              ·
                refine ⟨19976907810013671732205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26635877080018228976273 19976907810013671732205)
                ·
                  refine ⟨7491340428755126899577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19976907810013671732205 7491340428755126899577)
                  ·
                    rfl

theorem cell20_16413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_16413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16413 prefixEnd_16413 := by exact prefixLift 16413
  have htrace : WordTrace (prefixWord ++ tailWord_16413) baseStart_16413 baseEnd_16413 := by
    simpa [prefixWord, tailWord_16413, baseEnd_16413] using wordTrace_append hprefix tailTrace_16413
  have hstable : (prefixWord ++ tailWord_16413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16413).length < 2 ^ (prefixWord ++ tailWord_16413).sum := by decide
  have hdescent : baseEnd_16413 < baseStart_16413 := by decide
  rcases family_descends (prefixWord ++ tailWord_16413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16420 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_16420 : Nat := 118140960795 + 16420 * 2 ^ 59
def prefixEnd_16420 : Nat := 4983230072969 + 3 ^ 40 * 16420 * 2
def baseEnd_16420 : Nat := 7494535419494213666215

theorem tailTrace_16420 : CollatzResearch.WordTrace tailWord_16420 prefixEnd_16420 7494535419494213666215 := by
  unfold tailWord_16420
  simp only [CollatzResearch.WordTrace]
  refine ⟨299443300260309578923357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 399257733680412771897809 299443300260309578923357)
  ·
    refine ⟨112291237597616092096259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299443300260309578923357 112291237597616092096259)
    ·
      refine ⟨168436856396424138144389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112291237597616092096259 168436856396424138144389)
      ·
        refine ⟨31581910574329525902073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168436856396424138144389 31581910574329525902073)
        ·
          refine ⟨23686432930747144426555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31581910574329525902073 23686432930747144426555)
          ·
            refine ⟨35529649396120716639833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23686432930747144426555 35529649396120716639833)
            ·
              refine ⟨26647237047090537479875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35529649396120716639833 26647237047090537479875)
              ·
                refine ⟨39970855570635806219813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26647237047090537479875 39970855570635806219813)
                ·
                  refine ⟨7494535419494213666215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39970855570635806219813 7494535419494213666215)
                  ·
                    rfl

theorem cell20_16420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_16420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16420 prefixEnd_16420 := by exact prefixLift 16420
  have htrace : WordTrace (prefixWord ++ tailWord_16420) baseStart_16420 baseEnd_16420 := by
    simpa [prefixWord, tailWord_16420, baseEnd_16420] using wordTrace_append hprefix tailTrace_16420
  have hstable : (prefixWord ++ tailWord_16420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16420).length < 2 ^ (prefixWord ++ tailWord_16420).sum := by decide
  have hdescent : baseEnd_16420 < baseStart_16420 := by decide
  rcases family_descends (prefixWord ++ tailWord_16420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16448 : List Nat := [2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_16448 : Nat := 118140960795 + 16448 * 2 ^ 59
def prefixEnd_16448 : Nat := 4983230072969 + 3 ^ 40 * 16448 * 2
def baseEnd_16448 : Nat := 2502438460816853577589

theorem tailTrace_16448 : CollatzResearch.WordTrace tailWord_16448 prefixEnd_16448 2502438460816853577589 := by
  unfold tailWord_16448
  simp only [CollatzResearch.WordTrace]
  refine ⟨299953922209589969932999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 399938562946119959910665 299953922209589969932999)
  ·
    refine ⟨449930883314384954899499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299953922209589969932999 449930883314384954899499)
    ·
      refine ⟨674896324971577432349249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449930883314384954899499 674896324971577432349249)
      ·
        refine ⟨506172243728683074261937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674896324971577432349249 506172243728683074261937)
        ·
          refine ⟨379629182796512305696453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506172243728683074261937 379629182796512305696453)
          ·
            refine ⟨71180471774346057318085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379629182796512305696453 71180471774346057318085)
            ·
              refine ⟨13346338457689885747141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71180471774346057318085 13346338457689885747141)
              ·
                refine ⟨2502438460816853577589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13346338457689885747141 2502438460816853577589)
                ·
                  rfl

theorem cell20_16448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_16448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16448 prefixEnd_16448 := by exact prefixLift 16448
  have htrace : WordTrace (prefixWord ++ tailWord_16448) baseStart_16448 baseEnd_16448 := by
    simpa [prefixWord, tailWord_16448, baseEnd_16448] using wordTrace_append hprefix tailTrace_16448
  have hstable : (prefixWord ++ tailWord_16448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16448).length < 2 ^ (prefixWord ++ tailWord_16448).sum := by decide
  have hdescent : baseEnd_16448 < baseStart_16448 := by decide
  rcases family_descends (prefixWord ++ tailWord_16448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16469 : List Nat := [1, 3, 2, 2, 1, 3, 8]
def baseStart_16469 : Nat := 118140960795 + 16469 * 2 ^ 59
def prefixEnd_16469 : Nat := 4983230072969 + 3 ^ 40 * 16469 * 2
def baseEnd_16469 : Nat := 835211150518646781409

theorem tailTrace_16469 : CollatzResearch.WordTrace tailWord_16469 prefixEnd_16469 835211150518646781409 := by
  unfold tailWord_16469
  simp only [CollatzResearch.WordTrace]
  refine ⟨600673777343100526380461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 400449184895400350920307 600673777343100526380461)
  ·
    refine ⟨225252666503662697392673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 600673777343100526380461 225252666503662697392673)
    ·
      refine ⟨168939499877747023044505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225252666503662697392673 168939499877747023044505)
      ·
        refine ⟨126704624908310267283379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168939499877747023044505 126704624908310267283379)
        ·
          refine ⟨190056937362465400925069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126704624908310267283379 190056937362465400925069)
          ·
            refine ⟨71271351510924525346901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190056937362465400925069 71271351510924525346901)
            ·
              refine ⟨835211150518646781409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 71271351510924525346901 835211150518646781409)
              ·
                rfl

theorem cell20_16469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_16469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16469 prefixEnd_16469 := by exact prefixLift 16469
  have htrace : WordTrace (prefixWord ++ tailWord_16469) baseStart_16469 baseEnd_16469 := by
    simpa [prefixWord, tailWord_16469, baseEnd_16469] using wordTrace_append hprefix tailTrace_16469
  have hstable : (prefixWord ++ tailWord_16469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16469).length < 2 ^ (prefixWord ++ tailWord_16469).sum := by decide
  have hdescent : baseEnd_16469 < baseStart_16469 := by decide
  rcases family_descends (prefixWord ++ tailWord_16469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16562 : List Nat := [3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_16562 : Nat := 118140960795 + 16562 * 2 ^ 59
def prefixEnd_16562 : Nat := 4983230072969 + 3 ^ 40 * 16562 * 2
def baseEnd_16562 : Nat := 2519782696257610310767

theorem tailTrace_16562 : CollatzResearch.WordTrace tailWord_16562 prefixEnd_16562 2519782696257610310767 := by
  unfold tailWord_16562
  simp only [CollatzResearch.WordTrace]
  refine ⟨151016441501544352378985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 402710510670784939677293 151016441501544352378985)
  ·
    refine ⟨113262331126158264284239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151016441501544352378985 113262331126158264284239)
    ·
      refine ⟨169893496689237396426359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113262331126158264284239 169893496689237396426359)
      ·
        refine ⟨254840245033856094639539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169893496689237396426359 254840245033856094639539)
        ·
          refine ⟨382260367550784141959309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254840245033856094639539 382260367550784141959309)
          ·
            refine ⟨143347637831544053234741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382260367550784141959309 143347637831544053234741)
            ·
              refine ⟨13438841046707254990757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143347637831544053234741 13438841046707254990757)
              ·
                refine ⟨2519782696257610310767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13438841046707254990757 2519782696257610310767)
                ·
                  rfl

theorem cell20_16562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_16562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16562 prefixEnd_16562 := by exact prefixLift 16562
  have htrace : WordTrace (prefixWord ++ tailWord_16562) baseStart_16562 baseEnd_16562 := by
    simpa [prefixWord, tailWord_16562, baseEnd_16562] using wordTrace_append hprefix tailTrace_16562
  have hstable : (prefixWord ++ tailWord_16562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16562).length < 2 ^ (prefixWord ++ tailWord_16562).sum := by decide
  have hdescent : baseEnd_16562 < baseStart_16562 := by decide
  rcases family_descends (prefixWord ++ tailWord_16562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16593 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 2]
def baseStart_16593 : Nat := 118140960795 + 16593 * 2 ^ 59
def prefixEnd_16593 : Nat := 4983230072969 + 3 ^ 40 * 16593 * 2
def baseEnd_16593 : Nat := 7573497333474500898841

theorem tailTrace_16593 : CollatzResearch.WordTrace tailWord_16593 prefixEnd_16593 7573497333474500898841 := by
  unfold tailWord_16593
  simp only [CollatzResearch.WordTrace]
  refine ⟨605196428893869703894433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 403464285929246469262955 605196428893869703894433)
  ·
    refine ⟨453897321670402277920825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 605196428893869703894433 453897321670402277920825)
    ·
      refine ⟨340422991252801708440619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453897321670402277920825 340422991252801708440619)
      ·
        refine ⟨510634486879202562660929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340422991252801708440619 510634486879202562660929)
        ·
          refine ⟨382975865159401921995697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510634486879202562660929 382975865159401921995697)
          ·
            refine ⟨287231898869551441496773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382975865159401921995697 287231898869551441496773)
            ·
              refine ⟨53855981038040895280645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287231898869551441496773 53855981038040895280645)
              ·
                refine ⟨10097996444632667865121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53855981038040895280645 10097996444632667865121)
                ·
                  refine ⟨7573497333474500898841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10097996444632667865121 7573497333474500898841)
                  ·
                    rfl

theorem cell20_16593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_16593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16593 prefixEnd_16593 := by exact prefixLift 16593
  have htrace : WordTrace (prefixWord ++ tailWord_16593) baseStart_16593 baseEnd_16593 := by
    simpa [prefixWord, tailWord_16593, baseEnd_16593] using wordTrace_append hprefix tailTrace_16593
  have hstable : (prefixWord ++ tailWord_16593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16593).length < 2 ^ (prefixWord ++ tailWord_16593).sum := by decide
  have hdescent : baseEnd_16593 < baseStart_16593 := by decide
  rcases family_descends (prefixWord ++ tailWord_16593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16697 : List Nat := [1, 2, 1, 6, 1, 9]
def baseStart_16697 : Nat := 118140960795 + 16697 * 2 ^ 59
def prefixEnd_16697 : Nat := 4983230072969 + 3 ^ 40 * 16697 * 2
def baseEnd_16697 : Nat := 282257991381939312287

theorem tailTrace_16697 : CollatzResearch.WordTrace tailWord_16697 prefixEnd_16697 282257991381939312287 := by
  unfold tailWord_16697
  simp only [CollatzResearch.WordTrace]
  refine ⟨608989620517095465680345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 405993080344730310453563 608989620517095465680345)
  ·
    refine ⟨456742215387821599260259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 608989620517095465680345 456742215387821599260259)
    ·
      refine ⟨685113323081732398890389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456742215387821599260259 685113323081732398890389)
      ·
        refine ⟨32114687019456206197987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 685113323081732398890389 32114687019456206197987)
        ·
          refine ⟨48172030529184309296981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32114687019456206197987 48172030529184309296981)
          ·
            refine ⟨282257991381939312287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 48172030529184309296981 282257991381939312287)
            ·
              rfl

theorem cell20_16697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 9].length) (baseStart_16697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16697 prefixEnd_16697 := by exact prefixLift 16697
  have htrace : WordTrace (prefixWord ++ tailWord_16697) baseStart_16697 baseEnd_16697 := by
    simpa [prefixWord, tailWord_16697, baseEnd_16697] using wordTrace_append hprefix tailTrace_16697
  have hstable : (prefixWord ++ tailWord_16697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16697).length < 2 ^ (prefixWord ++ tailWord_16697).sum := by decide
  have hdescent : baseEnd_16697 < baseStart_16697 := by decide
  rcases family_descends (prefixWord ++ tailWord_16697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16721 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_16721 : Nat := 118140960795 + 16721 * 2 ^ 59
def prefixEnd_16721 : Nat := 4983230072969 + 3 ^ 40 * 16721 * 2
def baseEnd_16721 : Nat := 7631920021274944631651

theorem tailTrace_16721 : CollatzResearch.WordTrace tailWord_16721 prefixEnd_16721 7631920021274944631651 := by
  unfold tailWord_16721
  simp only [CollatzResearch.WordTrace]
  refine ⟨609864972430147564554017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 406576648286765043036011 609864972430147564554017)
  ·
    refine ⟨457398729322610673415513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 609864972430147564554017 457398729322610673415513)
    ·
      refine ⟨343049046991958005061635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457398729322610673415513 343049046991958005061635)
      ·
        refine ⟨514573570487937007592453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343049046991958005061635 514573570487937007592453)
        ·
          refine ⟨96482544466488188923585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514573570487937007592453 96482544466488188923585)
          ·
            refine ⟨72361908349866141692689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96482544466488188923585 72361908349866141692689)
            ·
              refine ⟨54271431262399606269517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72361908349866141692689 54271431262399606269517)
              ·
                refine ⟨20351786723399852351069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54271431262399606269517 20351786723399852351069)
                ·
                  refine ⟨7631920021274944631651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20351786723399852351069 7631920021274944631651)
                  ·
                    rfl

theorem cell20_16721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_16721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16721 prefixEnd_16721 := by exact prefixLift 16721
  have htrace : WordTrace (prefixWord ++ tailWord_16721) baseStart_16721 baseEnd_16721 := by
    simpa [prefixWord, tailWord_16721, baseEnd_16721] using wordTrace_append hprefix tailTrace_16721
  have hstable : (prefixWord ++ tailWord_16721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16721).length < 2 ^ (prefixWord ++ tailWord_16721).sum := by decide
  have hdescent : baseEnd_16721 < baseStart_16721 := by decide
  rcases family_descends (prefixWord ++ tailWord_16721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16745 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 2]
def baseStart_16745 : Nat := 118140960795 + 16745 * 2 ^ 59
def prefixEnd_16745 : Nat := 4983230072969 + 3 ^ 40 * 16745 * 2
def baseEnd_16745 : Nat := 7642874275237527831553

theorem tailTrace_16745 : CollatzResearch.WordTrace tailWord_16745 prefixEnd_16745 7642874275237527831553 := by
  unfold tailWord_16745
  simp only [CollatzResearch.WordTrace]
  refine ⟨610740324343199663427689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 407160216228799775618459 610740324343199663427689)
  ·
    refine ⟨458055243257399747570767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 610740324343199663427689 458055243257399747570767)
    ·
      refine ⟨687082864886099621356151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458055243257399747570767 687082864886099621356151)
      ·
        refine ⟨1030624297329149432034227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687082864886099621356151 1030624297329149432034227)
        ·
          refine ⟨1545936445993724148051341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030624297329149432034227 1545936445993724148051341)
          ·
            refine ⟨579726167247646555519253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1545936445993724148051341 579726167247646555519253)
            ·
              refine ⟨27174664089733432289965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 579726167247646555519253 27174664089733432289965)
              ·
                refine ⟨10190499033650037108737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27174664089733432289965 10190499033650037108737)
                ·
                  refine ⟨7642874275237527831553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10190499033650037108737 7642874275237527831553)
                  ·
                    rfl

theorem cell20_16745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_16745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16745 prefixEnd_16745 := by exact prefixLift 16745
  have htrace : WordTrace (prefixWord ++ tailWord_16745) baseStart_16745 baseEnd_16745 := by
    simpa [prefixWord, tailWord_16745, baseEnd_16745] using wordTrace_append hprefix tailTrace_16745
  have hstable : (prefixWord ++ tailWord_16745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16745).length < 2 ^ (prefixWord ++ tailWord_16745).sum := by decide
  have hdescent : baseEnd_16745 < baseStart_16745 := by decide
  rcases family_descends (prefixWord ++ tailWord_16745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16776 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_16776 : Nat := 118140960795 + 16776 * 2 ^ 59
def prefixEnd_16776 : Nat := 4983230072969 + 3 ^ 40 * 16776 * 2
def baseEnd_16776 : Nat := 7657023519939197798093

theorem tailTrace_16776 : CollatzResearch.WordTrace tailWord_16776 prefixEnd_16776 7657023519939197798093 := by
  unfold tailWord_16776
  simp only [CollatzResearch.WordTrace]
  refine ⟨305935493615445978903091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 407913991487261305204121 305935493615445978903091)
  ·
    refine ⟨458903240423168968354637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305935493615445978903091 458903240423168968354637)
    ·
      refine ⟨172088715158688363132989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458903240423168968354637 172088715158688363132989)
      ·
        refine ⟨64533268184508136174871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172088715158688363132989 64533268184508136174871)
        ·
          refine ⟨96799902276762204262307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64533268184508136174871 96799902276762204262307)
          ·
            refine ⟨145199853415143306393461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96799902276762204262307 145199853415143306393461)
            ·
              refine ⟨13612486257669684974387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145199853415143306393461 13612486257669684974387)
              ·
                refine ⟨20418729386504527461581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612486257669684974387 20418729386504527461581)
                ·
                  refine ⟨7657023519939197798093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20418729386504527461581 7657023519939197798093)
                  ·
                    rfl

theorem cell20_16776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_16776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16776 prefixEnd_16776 := by exact prefixLift 16776
  have htrace : WordTrace (prefixWord ++ tailWord_16776) baseStart_16776 baseEnd_16776 := by
    simpa [prefixWord, tailWord_16776, baseEnd_16776] using wordTrace_append hprefix tailTrace_16776
  have hstable : (prefixWord ++ tailWord_16776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16776).length < 2 ^ (prefixWord ++ tailWord_16776).sum := by decide
  have hdescent : baseEnd_16776 < baseStart_16776 := by decide
  rcases family_descends (prefixWord ++ tailWord_16776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16800 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_16800 : Nat := 118140960795 + 16800 * 2 ^ 59
def prefixEnd_16800 : Nat := 4983230072969 + 3 ^ 40 * 16800 * 2
def baseEnd_16800 : Nat := 7667977773901780997995

theorem tailTrace_16800 : CollatzResearch.WordTrace tailWord_16800 prefixEnd_16800 7667977773901780997995 := by
  unfold tailWord_16800
  simp only [CollatzResearch.WordTrace]
  refine ⟨306373169571972028339927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 408497559429296037786569 306373169571972028339927)
  ·
    refine ⟨459559754357958042509891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 306373169571972028339927 459559754357958042509891)
    ·
      refine ⟨689339631536937063764837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459559754357958042509891 689339631536937063764837)
      ·
        refine ⟨129251180913175699455907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 689339631536937063764837 129251180913175699455907)
        ·
          refine ⟨193876771369763549183861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129251180913175699455907 193876771369763549183861)
          ·
            refine ⟨18175947315915332735987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193876771369763549183861 18175947315915332735987)
            ·
              refine ⟨27263920973872999103981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18175947315915332735987 27263920973872999103981)
              ·
                refine ⟨10223970365202374663993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27263920973872999103981 10223970365202374663993)
                ·
                  refine ⟨7667977773901780997995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10223970365202374663993 7667977773901780997995)
                  ·
                    rfl

theorem cell20_16800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_16800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16800 prefixEnd_16800 := by exact prefixLift 16800
  have htrace : WordTrace (prefixWord ++ tailWord_16800) baseStart_16800 baseEnd_16800 := by
    simpa [prefixWord, tailWord_16800, baseEnd_16800] using wordTrace_append hprefix tailTrace_16800
  have hstable : (prefixWord ++ tailWord_16800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16800).length < 2 ^ (prefixWord ++ tailWord_16800).sum := by decide
  have hdescent : baseEnd_16800 < baseStart_16800 := by decide
  rcases family_descends (prefixWord ++ tailWord_16800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16818 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_16818 : Nat := 118140960795 + 16818 * 2 ^ 59
def prefixEnd_16818 : Nat := 4983230072969 + 3 ^ 40 * 16818 * 2
def baseEnd_16818 : Nat := 7676193464373718397921

theorem tailTrace_16818 : CollatzResearch.WordTrace tailWord_16818 prefixEnd_16818 7676193464373718397921 := by
  unfold tailWord_16818
  simp only [CollatzResearch.WordTrace]
  refine ⟨153350713269683282708777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 408935235385822087223405 153350713269683282708777)
  ·
    refine ⟨115013034952262462031583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153350713269683282708777 115013034952262462031583)
    ·
      refine ⟨172519552428393693047375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115013034952262462031583 172519552428393693047375)
      ·
        refine ⟨258779328642590539571063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172519552428393693047375 258779328642590539571063)
        ·
          refine ⟨388168992963885809356595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258779328642590539571063 388168992963885809356595)
          ·
            refine ⟨582253489445828714034893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388168992963885809356595 582253489445828714034893)
            ·
              refine ⟨218345058542185767763085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582253489445828714034893 218345058542185767763085)
              ·
                refine ⟨81879396953319662911157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218345058542185767763085 81879396953319662911157)
                ·
                  refine ⟨7676193464373718397921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81879396953319662911157 7676193464373718397921)
                  ·
                    rfl

theorem cell20_16818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_16818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16818 prefixEnd_16818 := by exact prefixLift 16818
  have htrace : WordTrace (prefixWord ++ tailWord_16818) baseStart_16818 baseEnd_16818 := by
    simpa [prefixWord, tailWord_16818, baseEnd_16818] using wordTrace_append hprefix tailTrace_16818
  have hstable : (prefixWord ++ tailWord_16818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16818).length < 2 ^ (prefixWord ++ tailWord_16818).sum := by decide
  have hdescent : baseEnd_16818 < baseStart_16818 := by decide
  rcases family_descends (prefixWord ++ tailWord_16818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16828 : List Nat := [2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_16828 : Nat := 118140960795 + 16828 * 2 ^ 59
def prefixEnd_16828 : Nat := 4983230072969 + 3 ^ 40 * 16828 * 2
def baseEnd_16828 : Nat := 2560252578952709354849

theorem tailTrace_16828 : CollatzResearch.WordTrace tailWord_16828 prefixEnd_16828 2560252578952709354849 := by
  unfold tailWord_16828
  simp only [CollatzResearch.WordTrace]
  refine ⟨306883791521252419349569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 409178388695003225799425 306883791521252419349569)
  ·
    refine ⟨230162843640939314512177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 306883791521252419349569 230162843640939314512177)
    ·
      refine ⟨172622132730704485884133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230162843640939314512177 172622132730704485884133)
      ·
        refine ⟨32366649887007091103275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172622132730704485884133 32366649887007091103275)
        ·
          refine ⟨48549974830510636654913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32366649887007091103275 48549974830510636654913)
          ·
            refine ⟨36412481122882977491185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48549974830510636654913 36412481122882977491185)
            ·
              refine ⟨27309360842162233118389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36412481122882977491185 27309360842162233118389)
              ·
                refine ⟨2560252578952709354849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27309360842162233118389 2560252578952709354849)
                ·
                  rfl

theorem cell20_16828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_16828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16828 prefixEnd_16828 := by exact prefixLift 16828
  have htrace : WordTrace (prefixWord ++ tailWord_16828) baseStart_16828 baseEnd_16828 := by
    simpa [prefixWord, tailWord_16828, baseEnd_16828] using wordTrace_append hprefix tailTrace_16828
  have hstable : (prefixWord ++ tailWord_16828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16828).length < 2 ^ (prefixWord ++ tailWord_16828).sum := by decide
  have hdescent : baseEnd_16828 < baseStart_16828 := by decide
  rcases family_descends (prefixWord ++ tailWord_16828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16866 : List Nat := [3, 3, 3, 2, 9]
def baseStart_16866 : Nat := 118140960795 + 16866 * 2 ^ 59
def prefixEnd_16866 : Nat := 4983230072969 + 3 ^ 40 * 16866 * 2
def baseEnd_16866 : Nat := 95038295954307219725

theorem tailTrace_16866 : CollatzResearch.WordTrace tailWord_16866 prefixEnd_16866 95038295954307219725 := by
  unfold tailWord_16866
  simp only [CollatzResearch.WordTrace]
  refine ⟨153788389226209332145613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 410102371269891552388301 153788389226209332145613)
  ·
    refine ⟨57670645959828499554605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153788389226209332145613 57670645959828499554605)
    ·
      refine ⟨21626492234935687332977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57670645959828499554605 21626492234935687332977)
      ·
        refine ⟨16219869176201765499733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21626492234935687332977 16219869176201765499733)
        ·
          refine ⟨95038295954307219725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 16219869176201765499733 95038295954307219725)
          ·
            rfl

theorem cell20_16866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 9].length) (baseStart_16866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16866 prefixEnd_16866 := by exact prefixLift 16866
  have htrace : WordTrace (prefixWord ++ tailWord_16866) baseStart_16866 baseEnd_16866 := by
    simpa [prefixWord, tailWord_16866, baseEnd_16866] using wordTrace_append hprefix tailTrace_16866
  have hstable : (prefixWord ++ tailWord_16866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16866).length < 2 ^ (prefixWord ++ tailWord_16866).sum := by decide
  have hdescent : baseEnd_16866 < baseStart_16866 := by decide
  rcases family_descends (prefixWord ++ tailWord_16866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16901 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_16901 : Nat := 118140960795 + 16901 * 2 ^ 59
def prefixEnd_16901 : Nat := 4983230072969 + 3 ^ 40 * 16901 * 2
def baseEnd_16901 : Nat := 7714076925994318630915

theorem tailTrace_16901 : CollatzResearch.WordTrace tailWord_16901 prefixEnd_16901 7714076925994318630915 := by
  unfold tailWord_16901
  simp only [CollatzResearch.WordTrace]
  refine ⟨616430111778038306106557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 410953407852025537404371 616430111778038306106557)
  ·
    refine ⟨231161291916764364789959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 616430111778038306106557 231161291916764364789959)
    ·
      refine ⟨346741937875146547184939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231161291916764364789959 346741937875146547184939)
      ·
        refine ⟨520112906812719820777409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346741937875146547184939 520112906812719820777409)
        ·
          refine ⟨390084680109539865583057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520112906812719820777409 390084680109539865583057)
          ·
            refine ⟨292563510082154899187293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390084680109539865583057 292563510082154899187293)
            ·
              refine ⟨109711316280808087195235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292563510082154899187293 109711316280808087195235)
              ·
                refine ⟨164566974421212130792853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109711316280808087195235 164566974421212130792853)
                ·
                  refine ⟨7714076925994318630915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 164566974421212130792853 7714076925994318630915)
                  ·
                    rfl

theorem cell20_16901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_16901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16901 prefixEnd_16901 := by exact prefixLift 16901
  have htrace : WordTrace (prefixWord ++ tailWord_16901) baseStart_16901 baseEnd_16901 := by
    simpa [prefixWord, tailWord_16901, baseEnd_16901] using wordTrace_append hprefix tailTrace_16901
  have hstable : (prefixWord ++ tailWord_16901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16901).length < 2 ^ (prefixWord ++ tailWord_16901).sum := by decide
  have hdescent : baseEnd_16901 < baseStart_16901 := by decide
  rcases family_descends (prefixWord ++ tailWord_16901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16925 : List Nat := [1, 4, 2, 2, 1, 3, 7]
def baseStart_16925 : Nat := 118140960795 + 16925 * 2 ^ 59
def prefixEnd_16925 : Nat := 4983230072969 + 3 ^ 40 * 16925 * 2
def baseEnd_16925 : Nat := 858336797772989092313

theorem tailTrace_16925 : CollatzResearch.WordTrace tailWord_16925 prefixEnd_16925 858336797772989092313 := by
  unfold tailWord_16925
  simp only [CollatzResearch.WordTrace]
  refine ⟨617305463691090404980229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 411536975794060269986819 617305463691090404980229)
  ·
    refine ⟨115744774442079450933793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 617305463691090404980229 115744774442079450933793)
    ·
      refine ⟨86808580831559588200345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115744774442079450933793 86808580831559588200345)
      ·
        refine ⟨65106435623669691150259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86808580831559588200345 65106435623669691150259)
        ·
          refine ⟨97659653435504536725389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65106435623669691150259 97659653435504536725389)
          ·
            refine ⟨36622370038314201272021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97659653435504536725389 36622370038314201272021)
            ·
              refine ⟨858336797772989092313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36622370038314201272021 858336797772989092313)
              ·
                rfl

theorem cell20_16925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_16925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16925 prefixEnd_16925 := by exact prefixLift 16925
  have htrace : WordTrace (prefixWord ++ tailWord_16925) baseStart_16925 baseEnd_16925 := by
    simpa [prefixWord, tailWord_16925, baseEnd_16925] using wordTrace_append hprefix tailTrace_16925
  have hstable : (prefixWord ++ tailWord_16925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16925).length < 2 ^ (prefixWord ++ tailWord_16925).sum := by decide
  have hdescent : baseEnd_16925 < baseStart_16925 := by decide
  rcases family_descends (prefixWord ++ tailWord_16925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16941 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 3]
def baseStart_16941 : Nat := 118140960795 + 16941 * 2 ^ 59
def prefixEnd_16941 : Nat := 4983230072969 + 3 ^ 40 * 16941 * 2
def baseEnd_16941 : Nat := 7732334015931957297419

theorem tailTrace_16941 : CollatzResearch.WordTrace tailWord_16941 prefixEnd_16941 7732334015931957297419 := by
  unfold tailWord_16941
  simp only [CollatzResearch.WordTrace]
  refine ⟨617889031633125137562677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 411926021088750091708451 617889031633125137562677)
  ·
    refine ⟨57927096715605481646501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 617889031633125137562677 57927096715605481646501)
    ·
      refine ⟨10861330634176027808719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57927096715605481646501 10861330634176027808719)
      ·
        refine ⟨16291995951264041713079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10861330634176027808719 16291995951264041713079)
        ·
          refine ⟨24437993926896062569619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16291995951264041713079 24437993926896062569619)
          ·
            refine ⟨36656990890344093854429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24437993926896062569619 36656990890344093854429)
            ·
              refine ⟨13746371583879035195411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36656990890344093854429 13746371583879035195411)
              ·
                refine ⟨20619557375818552793117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13746371583879035195411 20619557375818552793117)
                ·
                  refine ⟨7732334015931957297419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20619557375818552793117 7732334015931957297419)
                  ·
                    rfl

theorem cell20_16941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_16941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16941 prefixEnd_16941 := by exact prefixLift 16941
  have htrace : WordTrace (prefixWord ++ tailWord_16941) baseStart_16941 baseEnd_16941 := by
    simpa [prefixWord, tailWord_16941, baseEnd_16941] using wordTrace_append hprefix tailTrace_16941
  have hstable : (prefixWord ++ tailWord_16941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16941).length < 2 ^ (prefixWord ++ tailWord_16941).sum := by decide
  have hdescent : baseEnd_16941 < baseStart_16941 := by decide
  rcases family_descends (prefixWord ++ tailWord_16941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16956 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_16956 : Nat := 118140960795 + 16956 * 2 ^ 59
def prefixEnd_16956 : Nat := 4983230072969 + 3 ^ 40 * 16956 * 2
def baseEnd_16956 : Nat := 7739180424658571797357

theorem tailTrace_16956 : CollatzResearch.WordTrace tailWord_16956 prefixEnd_16956 7739180424658571797357 := by
  unfold tailWord_16956
  simp only [CollatzResearch.WordTrace]
  refine ⟨309218063289391349679361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 412290751052521799572481 309218063289391349679361)
  ·
    refine ⟨231913547467043512259521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 309218063289391349679361 231913547467043512259521)
    ·
      refine ⟨173935160600282634194641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231913547467043512259521 173935160600282634194641)
      ·
        refine ⟨130451370450211975645981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173935160600282634194641 130451370450211975645981)
        ·
          refine ⟨48919263918829490867243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130451370450211975645981 48919263918829490867243)
          ·
            refine ⟨73378895878244236300865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48919263918829490867243 73378895878244236300865)
            ·
              refine ⟨55034171908683177225649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73378895878244236300865 55034171908683177225649)
              ·
                refine ⟨41275628931512382919237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55034171908683177225649 41275628931512382919237)
                ·
                  refine ⟨7739180424658571797357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41275628931512382919237 7739180424658571797357)
                  ·
                    rfl

theorem cell20_16956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_16956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16956 prefixEnd_16956 := by exact prefixLift 16956
  have htrace : WordTrace (prefixWord ++ tailWord_16956) baseStart_16956 baseEnd_16956 := by
    simpa [prefixWord, tailWord_16956, baseEnd_16956] using wordTrace_append hprefix tailTrace_16956
  have hstable : (prefixWord ++ tailWord_16956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16956).length < 2 ^ (prefixWord ++ tailWord_16956).sum := by decide
  have hdescent : baseEnd_16956 < baseStart_16956 := by decide
  rcases family_descends (prefixWord ++ tailWord_16956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16966 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_16966 : Nat := 118140960795 + 16966 * 2 ^ 59
def prefixEnd_16966 : Nat := 4983230072969 + 3 ^ 40 * 16966 * 2
def baseEnd_16966 : Nat := 7743744697142981463983

theorem tailTrace_16966 : CollatzResearch.WordTrace tailWord_16966 prefixEnd_16966 7743744697142981463983 := by
  unfold tailWord_16966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19337526766954825225711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 412533904361702938148501 19337526766954825225711)
  ·
    refine ⟨29006290150432237838567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19337526766954825225711 29006290150432237838567)
    ·
      refine ⟨43509435225648356757851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29006290150432237838567 43509435225648356757851)
      ·
        refine ⟨65264152838472535136777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43509435225648356757851 65264152838472535136777)
        ·
          refine ⟨48948114628854401352583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65264152838472535136777 48948114628854401352583)
          ·
            refine ⟨73422171943281602028875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48948114628854401352583 73422171943281602028875)
            ·
              refine ⟨110133257914922403043313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73422171943281602028875 110133257914922403043313)
              ·
                refine ⟨82599943436191802282485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110133257914922403043313 82599943436191802282485)
                ·
                  refine ⟨7743744697142981463983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82599943436191802282485 7743744697142981463983)
                  ·
                    rfl

theorem cell20_16966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_16966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16966 prefixEnd_16966 := by exact prefixLift 16966
  have htrace : WordTrace (prefixWord ++ tailWord_16966) baseStart_16966 baseEnd_16966 := by
    simpa [prefixWord, tailWord_16966, baseEnd_16966] using wordTrace_append hprefix tailTrace_16966
  have hstable : (prefixWord ++ tailWord_16966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16966).length < 2 ^ (prefixWord ++ tailWord_16966).sum := by decide
  have hdescent : baseEnd_16966 < baseStart_16966 := by decide
  rcases family_descends (prefixWord ++ tailWord_16966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16970 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_16970 : Nat := 118140960795 + 16970 * 2 ^ 59
def prefixEnd_16970 : Nat := 4983230072969 + 3 ^ 40 * 16970 * 2
def baseEnd_16970 : Nat := 7745570406136745330633

theorem tailTrace_16970 : CollatzResearch.WordTrace tailWord_16970 prefixEnd_16970 7745570406136745330633 := by
  unfold tailWord_16970
  simp only [CollatzResearch.WordTrace]
  refine ⟨154736687132015772592091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 412631165685375393578909 154736687132015772592091)
  ·
    refine ⟨232105030698023658888137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154736687132015772592091 232105030698023658888137)
    ·
      refine ⟨174078773023517744166103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232105030698023658888137 174078773023517744166103)
      ·
        refine ⟨261118159535276616249155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174078773023517744166103 261118159535276616249155)
        ·
          refine ⟨391677239302914924373733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261118159535276616249155 391677239302914924373733)
          ·
            refine ⟨73439482369296548320075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 391677239302914924373733 73439482369296548320075)
            ·
              refine ⟨110159223553944822480113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73439482369296548320075 110159223553944822480113)
              ·
                refine ⟨82619417665458616860085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110159223553944822480113 82619417665458616860085)
                ·
                  refine ⟨7745570406136745330633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82619417665458616860085 7745570406136745330633)
                  ·
                    rfl

theorem cell20_16970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_16970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16970 prefixEnd_16970 := by exact prefixLift 16970
  have htrace : WordTrace (prefixWord ++ tailWord_16970) baseStart_16970 baseEnd_16970 := by
    simpa [prefixWord, tailWord_16970, baseEnd_16970] using wordTrace_append hprefix tailTrace_16970
  have hstable : (prefixWord ++ tailWord_16970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16970).length < 2 ^ (prefixWord ++ tailWord_16970).sum := by decide
  have hdescent : baseEnd_16970 < baseStart_16970 := by decide
  rcases family_descends (prefixWord ++ tailWord_16970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16984 : List Nat := [2, 1, 2, 2, 1, 2, 10]
def baseStart_16984 : Nat := 118140960795 + 16984 * 2 ^ 59
def prefixEnd_16984 : Nat := 4983230072969 + 3 ^ 40 * 16984 * 2
def baseEnd_16984 : Nat := 861328931957213207101

theorem tailTrace_16984 : CollatzResearch.WordTrace tailWord_16984 prefixEnd_16984 861328931957213207101 := by
  unfold tailWord_16984
  simp only [CollatzResearch.WordTrace]
  refine ⟨309728685238671740689003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 412971580318228987585337 309728685238671740689003)
  ·
    refine ⟨464593027858007611033505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309728685238671740689003 464593027858007611033505)
    ·
      refine ⟨348444770893505708275129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464593027858007611033505 348444770893505708275129)
      ·
        refine ⟨261333578170129281206347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348444770893505708275129 261333578170129281206347)
        ·
          refine ⟨392000367255193921809521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261333578170129281206347 392000367255193921809521)
          ·
            refine ⟨294000275441395441357141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392000367255193921809521 294000275441395441357141)
            ·
              refine ⟨861328931957213207101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 294000275441395441357141 861328931957213207101)
              ·
                rfl

theorem cell20_16984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_16984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_16984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_16984 prefixEnd_16984 := by exact prefixLift 16984
  have htrace : WordTrace (prefixWord ++ tailWord_16984) baseStart_16984 baseEnd_16984 := by
    simpa [prefixWord, tailWord_16984, baseEnd_16984] using wordTrace_append hprefix tailTrace_16984
  have hstable : (prefixWord ++ tailWord_16984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16984).length < 2 ^ (prefixWord ++ tailWord_16984).sum := by decide
  have hdescent : baseEnd_16984 < baseStart_16984 := by decide
  rcases family_descends (prefixWord ++ tailWord_16984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17000 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_17000 : Nat := 118140960795 + 17000 * 2 ^ 59
def prefixEnd_17000 : Nat := 4983230072969 + 3 ^ 40 * 17000 * 2
def baseEnd_17000 : Nat := 7759263223589974330511

theorem tailTrace_17000 : CollatzResearch.WordTrace tailWord_17000 prefixEnd_17000 7759263223589974330511 := by
  unfold tailWord_17000
  simp only [CollatzResearch.WordTrace]
  refine ⟨310020469209689106980227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 413360625612918809306969 310020469209689106980227)
  ·
    refine ⟨465030703814533660470341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310020469209689106980227 465030703814533660470341)
    ·
      refine ⟨87193256965225061338189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 465030703814533660470341 87193256965225061338189)
      ·
        refine ⟨32697471361959398001821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87193256965225061338189 32697471361959398001821)
        ·
          refine ⟨12261551760734774250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32697471361959398001821 12261551760734774250683)
          ·
            refine ⟨18392327641102161376025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12261551760734774250683 18392327641102161376025)
            ·
              refine ⟨13794245730826621032019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18392327641102161376025 13794245730826621032019)
              ·
                refine ⟨20691368596239931548029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13794245730826621032019 20691368596239931548029)
                ·
                  refine ⟨7759263223589974330511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20691368596239931548029 7759263223589974330511)
                  ·
                    rfl

theorem cell20_17000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_17000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17000 prefixEnd_17000 := by exact prefixLift 17000
  have htrace : WordTrace (prefixWord ++ tailWord_17000) baseStart_17000 baseEnd_17000 := by
    simpa [prefixWord, tailWord_17000, baseEnd_17000] using wordTrace_append hprefix tailTrace_17000
  have hstable : (prefixWord ++ tailWord_17000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17000).length < 2 ^ (prefixWord ++ tailWord_17000).sum := by decide
  have hdescent : baseEnd_17000 < baseStart_17000 := by decide
  rcases family_descends (prefixWord ++ tailWord_17000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17015 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_17015 : Nat := 118140960795 + 17015 * 2 ^ 59
def prefixEnd_17015 : Nat := 4983230072969 + 3 ^ 40 * 17015 * 2
def baseEnd_17015 : Nat := 7766109632316588830449

theorem tailTrace_17015 : CollatzResearch.WordTrace tailWord_17015 prefixEnd_17015 7766109632316588830449 := by
  unfold tailWord_17015
  simp only [CollatzResearch.WordTrace]
  refine ⟨620588033365035775756499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 413725355576690517170999 620588033365035775756499)
  ·
    refine ⟨930882050047553663634749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620588033365035775756499 930882050047553663634749)
    ·
      refine ⟨349080768767832623863031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 930882050047553663634749 349080768767832623863031)
      ·
        refine ⟨523621153151748935794547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349080768767832623863031 523621153151748935794547)
        ·
          refine ⟨785431729727623403691821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523621153151748935794547 785431729727623403691821)
          ·
            refine ⟨294536898647858776384433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 785431729727623403691821 294536898647858776384433)
            ·
              refine ⟨220902673985894082288325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294536898647858776384433 220902673985894082288325)
              ·
                refine ⟨41419251372355140429061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220902673985894082288325 41419251372355140429061)
                ·
                  refine ⟨7766109632316588830449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41419251372355140429061 7766109632316588830449)
                  ·
                    rfl

theorem cell20_17015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_17015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17015 prefixEnd_17015 := by exact prefixLift 17015
  have htrace : WordTrace (prefixWord ++ tailWord_17015) baseStart_17015 baseEnd_17015 := by
    simpa [prefixWord, tailWord_17015, baseEnd_17015] using wordTrace_append hprefix tailTrace_17015
  have hstable : (prefixWord ++ tailWord_17015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17015).length < 2 ^ (prefixWord ++ tailWord_17015).sum := by decide
  have hdescent : baseEnd_17015 < baseStart_17015 := by decide
  rcases family_descends (prefixWord ++ tailWord_17015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17042 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_17042 : Nat := 118140960795 + 17042 * 2 ^ 59
def prefixEnd_17042 : Nat := 4983230072969 + 3 ^ 40 * 17042 * 2
def baseEnd_17042 : Nat := 7778433168024494930339

theorem tailTrace_17042 : CollatzResearch.WordTrace tailWord_17042 prefixEnd_17042 7778433168024494930339 := by
  unfold tailWord_17042
  simp only [CollatzResearch.WordTrace]
  refine ⟨155393201066804846747345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 414381869511479591326253 155393201066804846747345)
  ·
    refine ⟨116544900800103635060509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155393201066804846747345 116544900800103635060509)
    ·
      refine ⟨43704337800038863147691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116544900800103635060509 43704337800038863147691)
      ·
        refine ⟨65556506700058294721537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43704337800038863147691 65556506700058294721537)
        ·
          refine ⟨49167380025043721041153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65556506700058294721537 49167380025043721041153)
          ·
            refine ⟨36875535018782790780865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49167380025043721041153 36875535018782790780865)
            ·
              refine ⟨27656651264087093085649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36875535018782790780865 27656651264087093085649)
              ·
                refine ⟨20742488448065319814237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27656651264087093085649 20742488448065319814237)
                ·
                  refine ⟨7778433168024494930339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20742488448065319814237 7778433168024494930339)
                  ·
                    rfl

theorem cell20_17042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_17042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17042 prefixEnd_17042 := by exact prefixLift 17042
  have htrace : WordTrace (prefixWord ++ tailWord_17042) baseStart_17042 baseEnd_17042 := by
    simpa [prefixWord, tailWord_17042, baseEnd_17042] using wordTrace_append hprefix tailTrace_17042
  have hstable : (prefixWord ++ tailWord_17042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17042).length < 2 ^ (prefixWord ++ tailWord_17042).sum := by decide
  have hdescent : baseEnd_17042 < baseStart_17042 := by decide
  rcases family_descends (prefixWord ++ tailWord_17042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17056 : List Nat := [2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_17056 : Nat := 118140960795 + 17056 * 2 ^ 59
def prefixEnd_17056 : Nat := 4983230072969 + 3 ^ 40 * 17056 * 2
def baseEnd_17056 : Nat := 2594941049834222821205

theorem tailTrace_17056 : CollatzResearch.WordTrace tailWord_17056 prefixEnd_17056 2594941049834222821205 := by
  unfold tailWord_17056
  simp only [CollatzResearch.WordTrace]
  refine ⟨311041713108249888999511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 414722284144333185332681 311041713108249888999511)
  ·
    refine ⟨466562569662374833499267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 311041713108249888999511 466562569662374833499267)
    ·
      refine ⟨699843854493562250248901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466562569662374833499267 699843854493562250248901)
      ·
        refine ⟨131220722717542921921669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 699843854493562250248901 131220722717542921921669)
        ·
          refine ⟨24603885509539297860313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131220722717542921921669 24603885509539297860313)
          ·
            refine ⟨18452914132154473395235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24603885509539297860313 18452914132154473395235)
            ·
              refine ⟨27679371198231710092853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18452914132154473395235 27679371198231710092853)
              ·
                refine ⟨2594941049834222821205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27679371198231710092853 2594941049834222821205)
                ·
                  rfl

theorem cell20_17056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_17056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17056 prefixEnd_17056 := by exact prefixLift 17056
  have htrace : WordTrace (prefixWord ++ tailWord_17056) baseStart_17056 baseEnd_17056 := by
    simpa [prefixWord, tailWord_17056, baseEnd_17056] using wordTrace_append hprefix tailTrace_17056
  have hstable : (prefixWord ++ tailWord_17056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17056).length < 2 ^ (prefixWord ++ tailWord_17056).sum := by decide
  have hdescent : baseEnd_17056 < baseStart_17056 := by decide
  rcases family_descends (prefixWord ++ tailWord_17056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17066 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_17066 : Nat := 118140960795 + 17066 * 2 ^ 59
def prefixEnd_17066 : Nat := 4983230072969 + 3 ^ 40 * 17066 * 2
def baseEnd_17066 : Nat := 7789387421987078130241

theorem tailTrace_17066 : CollatzResearch.WordTrace tailWord_17066 prefixEnd_17066 7789387421987078130241 := by
  unfold tailWord_17066
  simp only [CollatzResearch.WordTrace]
  refine ⟨155612039045067871465763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 414965437453514323908701 155612039045067871465763)
  ·
    refine ⟨233418058567601807198645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155612039045067871465763 233418058567601807198645)
    ·
      refine ⟨21882942990712669424873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233418058567601807198645 21882942990712669424873)
      ·
        refine ⟨16412207243034502068655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21882942990712669424873 16412207243034502068655)
        ·
          refine ⟨24618310864551753102983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412207243034502068655 24618310864551753102983)
          ·
            refine ⟨36927466296827629654475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24618310864551753102983 36927466296827629654475)
            ·
              refine ⟨55391199445241444481713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36927466296827629654475 55391199445241444481713)
              ·
                refine ⟨41543399583931083361285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55391199445241444481713 41543399583931083361285)
                ·
                  refine ⟨7789387421987078130241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41543399583931083361285 7789387421987078130241)
                  ·
                    rfl

theorem cell20_17066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_17066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17066 prefixEnd_17066 := by exact prefixLift 17066
  have htrace : WordTrace (prefixWord ++ tailWord_17066) baseStart_17066 baseEnd_17066 := by
    simpa [prefixWord, tailWord_17066, baseEnd_17066] using wordTrace_append hprefix tailTrace_17066
  have hstable : (prefixWord ++ tailWord_17066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17066).length < 2 ^ (prefixWord ++ tailWord_17066).sum := by decide
  have hdescent : baseEnd_17066 < baseStart_17066 := by decide
  rcases family_descends (prefixWord ++ tailWord_17066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17073 : List Nat := [1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_17073 : Nat := 118140960795 + 17073 * 2 ^ 59
def prefixEnd_17073 : Nat := 4983230072969 + 3 ^ 40 * 17073 * 2
def baseEnd_17073 : Nat := 2597527470908721632293

theorem tailTrace_17073 : CollatzResearch.WordTrace tailWord_17073 prefixEnd_17073 2597527470908721632293 := by
  unfold tailWord_17073
  simp only [CollatzResearch.WordTrace]
  refine ⟨622703467154911681367873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 415135644769941120911915 622703467154911681367873)
  ·
    refine ⟨467027600366183761025905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 622703467154911681367873 467027600366183761025905)
    ·
      refine ⟨350270700274637820769429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467027600366183761025905 350270700274637820769429)
      ·
        refine ⟨16418939075373647848567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 350270700274637820769429 16418939075373647848567)
        ·
          refine ⟨24628408613060471772851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16418939075373647848567 24628408613060471772851)
          ·
            refine ⟨36942612919590707659277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24628408613060471772851 36942612919590707659277)
            ·
              refine ⟨13853479844846515372229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36942612919590707659277 13853479844846515372229)
              ·
                refine ⟨2597527470908721632293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13853479844846515372229 2597527470908721632293)
                ·
                  rfl

theorem cell20_17073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_17073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17073 prefixEnd_17073 := by exact prefixLift 17073
  have htrace : WordTrace (prefixWord ++ tailWord_17073) baseStart_17073 baseEnd_17073 := by
    simpa [prefixWord, tailWord_17073, baseEnd_17073] using wordTrace_append hprefix tailTrace_17073
  have hstable : (prefixWord ++ tailWord_17073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17073).length < 2 ^ (prefixWord ++ tailWord_17073).sum := by decide
  have hdescent : baseEnd_17073 < baseStart_17073 := by decide
  rcases family_descends (prefixWord ++ tailWord_17073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17084 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_17084 : Nat := 118140960795 + 17084 * 2 ^ 59
def prefixEnd_17084 : Nat := 4983230072969 + 3 ^ 40 * 17084 * 2
def baseEnd_17084 : Nat := 7797603112459015530167

theorem tailTrace_17084 : CollatzResearch.WordTrace tailWord_17084 prefixEnd_17084 7797603112459015530167 := by
  unfold tailWord_17084
  simp only [CollatzResearch.WordTrace]
  refine ⟨311552335057530280009153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 415403113410040373345537 311552335057530280009153)
  ·
    refine ⟨233664251293147710006865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311552335057530280009153 233664251293147710006865)
    ·
      refine ⟨175248188469860782505149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233664251293147710006865 175248188469860782505149)
      ·
        refine ⟨65718070676197793439431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175248188469860782505149 65718070676197793439431)
        ·
          refine ⟨98577106014296690159147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65718070676197793439431 98577106014296690159147)
          ·
            refine ⟨147865659021445035238721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98577106014296690159147 147865659021445035238721)
            ·
              refine ⟨110899244266083776429041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147865659021445035238721 110899244266083776429041)
              ·
                refine ⟨83174433199562832321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110899244266083776429041 83174433199562832321781)
                ·
                  refine ⟨7797603112459015530167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83174433199562832321781 7797603112459015530167)
                  ·
                    rfl

theorem cell20_17084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_17084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17084 prefixEnd_17084 := by exact prefixLift 17084
  have htrace : WordTrace (prefixWord ++ tailWord_17084) baseStart_17084 baseEnd_17084 := by
    simpa [prefixWord, tailWord_17084, baseEnd_17084] using wordTrace_append hprefix tailTrace_17084
  have hstable : (prefixWord ++ tailWord_17084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17084).length < 2 ^ (prefixWord ++ tailWord_17084).sum := by decide
  have hdescent : baseEnd_17084 < baseStart_17084 := by decide
  rcases family_descends (prefixWord ++ tailWord_17084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17087 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 2]
def baseStart_17087 : Nat := 118140960795 + 17087 * 2 ^ 59
def prefixEnd_17087 : Nat := 4983230072969 + 3 ^ 40 * 17087 * 2
def baseEnd_17087 : Nat := 7798972394204338430155

theorem tailTrace_17087 : CollatzResearch.WordTrace tailWord_17087 prefixEnd_17087 7798972394204338430155 := by
  unfold tailWord_17087
  simp only [CollatzResearch.WordTrace]
  refine ⟨623214089104192072377515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 415476059402794714918343 623214089104192072377515)
  ·
    refine ⟨934821133656288108566273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623214089104192072377515 934821133656288108566273)
    ·
      refine ⟨701115850242216081424705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 934821133656288108566273 701115850242216081424705)
      ·
        refine ⟨525836887681662061068529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701115850242216081424705 525836887681662061068529)
        ·
          refine ⟨394377665761246545801397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525836887681662061068529 394377665761246545801397)
          ·
            refine ⟨36972906165116863668881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 394377665761246545801397 36972906165116863668881)
            ·
              refine ⟨27729679623837647751661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36972906165116863668881 27729679623837647751661)
              ·
                refine ⟨10398629858939117906873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27729679623837647751661 10398629858939117906873)
                ·
                  refine ⟨7798972394204338430155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10398629858939117906873 7798972394204338430155)
                  ·
                    rfl

theorem cell20_17087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2].length) (baseStart_17087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17087 prefixEnd_17087 := by exact prefixLift 17087
  have htrace : WordTrace (prefixWord ++ tailWord_17087) baseStart_17087 baseEnd_17087 := by
    simpa [prefixWord, tailWord_17087, baseEnd_17087] using wordTrace_append hprefix tailTrace_17087
  have hstable : (prefixWord ++ tailWord_17087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17087).length < 2 ^ (prefixWord ++ tailWord_17087).sum := by decide
  have hdescent : baseEnd_17087 < baseStart_17087 := by decide
  rcases family_descends (prefixWord ++ tailWord_17087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17129 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_17129 : Nat := 118140960795 + 17129 * 2 ^ 59
def prefixEnd_17129 : Nat := 4983230072969 + 3 ^ 40 * 17129 * 2
def baseEnd_17129 : Nat := 7818142338638859029983

theorem tailTrace_17129 : CollatzResearch.WordTrace tailWord_17129 prefixEnd_17129 7818142338638859029983 := by
  unfold tailWord_17129
  simp only [CollatzResearch.WordTrace]
  refine ⟨624745954952033245406441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 416497303301355496937627 624745954952033245406441)
  ·
    refine ⟨468559466214024934054831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 624745954952033245406441 468559466214024934054831)
    ·
      refine ⟨702839199321037401082247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468559466214024934054831 702839199321037401082247)
      ·
        refine ⟨1054258798981556101623371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702839199321037401082247 1054258798981556101623371)
        ·
          refine ⟨1581388198472334152435057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054258798981556101623371 1581388198472334152435057)
          ·
            refine ⟨1186041148854250614326293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581388198472334152435057 1186041148854250614326293)
            ·
              refine ⟨55595678852542997546545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1186041148854250614326293 55595678852542997546545)
              ·
                refine ⟨41696759139407248159909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55595678852542997546545 41696759139407248159909)
                ·
                  refine ⟨7818142338638859029983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41696759139407248159909 7818142338638859029983)
                  ·
                    rfl

theorem cell20_17129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_17129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17129 prefixEnd_17129 := by exact prefixLift 17129
  have htrace : WordTrace (prefixWord ++ tailWord_17129) baseStart_17129 baseEnd_17129 := by
    simpa [prefixWord, tailWord_17129, baseEnd_17129] using wordTrace_append hprefix tailTrace_17129
  have hstable : (prefixWord ++ tailWord_17129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17129).length < 2 ^ (prefixWord ++ tailWord_17129).sum := by decide
  have hdescent : baseEnd_17129 < baseStart_17129 := by decide
  rcases family_descends (prefixWord ++ tailWord_17129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17136 : List Nat := [2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_17136 : Nat := 118140960795 + 17136 * 2 ^ 59
def prefixEnd_17136 : Nat := 4983230072969 + 3 ^ 40 * 17136 * 2
def baseEnd_17136 : Nat := 2607112443125981932207

theorem tailTrace_17136 : CollatzResearch.WordTrace tailWord_17136 prefixEnd_17136 2607112443125981932207 := by
  unfold tailWord_17136
  simp only [CollatzResearch.WordTrace]
  refine ⟨312500632963336720455631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 416667510617782293940841 312500632963336720455631)
  ·
    refine ⟨468750949445005080683447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312500632963336720455631 468750949445005080683447)
    ·
      refine ⟨703126424167507621025171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468750949445005080683447 703126424167507621025171)
      ·
        refine ⟨1054689636251261431537757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703126424167507621025171 1054689636251261431537757)
        ·
          refine ⟨395508613594223036826659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1054689636251261431537757 395508613594223036826659)
          ·
            refine ⟨593262920391334555239989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395508613594223036826659 593262920391334555239989)
            ·
              refine ⟨55618398786687614553749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 593262920391334555239989 55618398786687614553749)
              ·
                refine ⟨2607112443125981932207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55618398786687614553749 2607112443125981932207)
                ·
                  rfl

theorem cell20_17136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_17136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17136 prefixEnd_17136 := by exact prefixLift 17136
  have htrace : WordTrace (prefixWord ++ tailWord_17136) baseStart_17136 baseEnd_17136 := by
    simpa [prefixWord, tailWord_17136, baseEnd_17136] using wordTrace_append hprefix tailTrace_17136
  have hstable : (prefixWord ++ tailWord_17136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17136).length < 2 ^ (prefixWord ++ tailWord_17136).sum := by decide
  have hdescent : baseEnd_17136 < baseStart_17136 := by decide
  rcases family_descends (prefixWord ++ tailWord_17136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17160 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_17160 : Nat := 118140960795 + 17160 * 2 ^ 59
def prefixEnd_17160 : Nat := 4983230072969 + 3 ^ 40 * 17160 * 2
def baseEnd_17160 : Nat := 7832291583340528996523

theorem tailTrace_17160 : CollatzResearch.WordTrace tailWord_17160 prefixEnd_17160 7832291583340528996523 := by
  unfold tailWord_17160
  simp only [CollatzResearch.WordTrace]
  refine ⟨312938308919862769892467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 417251078559817026523289 312938308919862769892467)
  ·
    refine ⟨469407463379794154838701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312938308919862769892467 469407463379794154838701)
    ·
      refine ⟨176027798767422808064513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 469407463379794154838701 176027798767422808064513)
      ·
        refine ⟨132020849075567106048385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176027798767422808064513 132020849075567106048385)
        ·
          refine ⟨99015636806675329536289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132020849075567106048385 99015636806675329536289)
          ·
            refine ⟨74261727605006497152217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99015636806675329536289 74261727605006497152217)
            ·
              refine ⟨55696295703754872864163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74261727605006497152217 55696295703754872864163)
              ·
                refine ⟨83544443555632309296245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55696295703754872864163 83544443555632309296245)
                ·
                  refine ⟨7832291583340528996523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83544443555632309296245 7832291583340528996523)
                  ·
                    rfl

theorem cell20_17160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_17160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17160 prefixEnd_17160 := by exact prefixLift 17160
  have htrace : WordTrace (prefixWord ++ tailWord_17160) baseStart_17160 baseEnd_17160 := by
    simpa [prefixWord, tailWord_17160, baseEnd_17160] using wordTrace_append hprefix tailTrace_17160
  have hstable : (prefixWord ++ tailWord_17160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17160).length < 2 ^ (prefixWord ++ tailWord_17160).sum := by decide
  have hdescent : baseEnd_17160 < baseStart_17160 := by decide
  rcases family_descends (prefixWord ++ tailWord_17160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17214 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_17214 : Nat := 118140960795 + 17214 * 2 ^ 59
def prefixEnd_17214 : Nat := 4983230072969 + 3 ^ 40 * 17214 * 2
def baseEnd_17214 : Nat := 7856938654756341196303

theorem tailTrace_17214 : CollatzResearch.WordTrace tailWord_17214 prefixEnd_17214 7856938654756341196303 := by
  unfold tailWord_17214
  simp only [CollatzResearch.WordTrace]
  refine ⟨78480769955511595281337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 418564106429395174833797 78480769955511595281337)
  ·
    refine ⟨58860577466633696461003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78480769955511595281337 58860577466633696461003)
    ·
      refine ⟨88290866199950544691505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58860577466633696461003 88290866199950544691505)
      ·
        refine ⟨66218149649962908518629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88290866199950544691505 66218149649962908518629)
        ·
          refine ⟨12415903059368045347243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66218149649962908518629 12415903059368045347243)
          ·
            refine ⟨18623854589052068020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12415903059368045347243 18623854589052068020865)
            ·
              refine ⟨13967890941789051015649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18623854589052068020865 13967890941789051015649)
              ·
                refine ⟨10475918206341788261737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13967890941789051015649 10475918206341788261737)
                ·
                  refine ⟨7856938654756341196303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10475918206341788261737 7856938654756341196303)
                  ·
                    rfl

theorem cell20_17214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_17214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17214 prefixEnd_17214 := by exact prefixLift 17214
  have htrace : WordTrace (prefixWord ++ tailWord_17214) baseStart_17214 baseEnd_17214 := by
    simpa [prefixWord, tailWord_17214, baseEnd_17214] using wordTrace_append hprefix tailTrace_17214
  have hstable : (prefixWord ++ tailWord_17214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17214).length < 2 ^ (prefixWord ++ tailWord_17214).sum := by decide
  have hdescent : baseEnd_17214 < baseStart_17214 := by decide
  rcases family_descends (prefixWord ++ tailWord_17214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17215 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_17215 : Nat := 118140960795 + 17215 * 2 ^ 59
def prefixEnd_17215 : Nat := 4983230072969 + 3 ^ 40 * 17215 * 2
def baseEnd_17215 : Nat := 7857395082004782162965

theorem tailTrace_17215 : CollatzResearch.WordTrace tailWord_17215 prefixEnd_17215 7857395082004782162965 := by
  unfold tailWord_17215
  simp only [CollatzResearch.WordTrace]
  refine ⟨627882632640469933037099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 418588421760313288691399 627882632640469933037099)
  ·
    refine ⟨941823948960704899555649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627882632640469933037099 941823948960704899555649)
    ·
      refine ⟨706367961720528674666737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 941823948960704899555649 706367961720528674666737)
      ·
        refine ⟨529775971290396506000053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706367961720528674666737 529775971290396506000053)
        ·
          refine ⟨49666497308474672437505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 529775971290396506000053 49666497308474672437505)
          ·
            refine ⟨37249872981356004328129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49666497308474672437505 37249872981356004328129)
            ·
              refine ⟨27937404736017003246097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37249872981356004328129 27937404736017003246097)
              ·
                refine ⟨20953053552012752434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27937404736017003246097 20953053552012752434573)
                ·
                  refine ⟨7857395082004782162965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20953053552012752434573 7857395082004782162965)
                  ·
                    rfl

theorem cell20_17215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_17215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17215 prefixEnd_17215 := by exact prefixLift 17215
  have htrace : WordTrace (prefixWord ++ tailWord_17215) baseStart_17215 baseEnd_17215 := by
    simpa [prefixWord, tailWord_17215, baseEnd_17215] using wordTrace_append hprefix tailTrace_17215
  have hstable : (prefixWord ++ tailWord_17215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17215).length < 2 ^ (prefixWord ++ tailWord_17215).sum := by decide
  have hdescent : baseEnd_17215 < baseStart_17215 := by decide
  rcases family_descends (prefixWord ++ tailWord_17215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17270 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_17270 : Nat := 118140960795 + 17270 * 2 ^ 59
def prefixEnd_17270 : Nat := 4983230072969 + 3 ^ 40 * 17270 * 2
def baseEnd_17270 : Nat := 7882498580669035329407

theorem tailTrace_17270 : CollatzResearch.WordTrace tailWord_17270 prefixEnd_17270 7882498580669035329407 := by
  unfold tailWord_17270
  simp only [CollatzResearch.WordTrace]
  refine ⟨39368040465075895393079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 419925764960809550859509 39368040465075895393079)
  ·
    refine ⟨59052060697613843089619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39368040465075895393079 59052060697613843089619)
    ·
      refine ⟨88578091046420764634429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59052060697613843089619 88578091046420764634429)
      ·
        refine ⟨33216784142407786737911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88578091046420764634429 33216784142407786737911)
        ·
          refine ⟨49825176213611680106867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33216784142407786737911 49825176213611680106867)
          ·
            refine ⟨74737764320417520160301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49825176213611680106867 74737764320417520160301)
            ·
              refine ⟨28026661620156570060113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74737764320417520160301 28026661620156570060113)
              ·
                refine ⟨21019996215117427545085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28026661620156570060113 21019996215117427545085)
                ·
                  refine ⟨7882498580669035329407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21019996215117427545085 7882498580669035329407)
                  ·
                    rfl

theorem cell20_17270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_17270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17270 prefixEnd_17270 := by exact prefixLift 17270
  have htrace : WordTrace (prefixWord ++ tailWord_17270) baseStart_17270 baseEnd_17270 := by
    simpa [prefixWord, tailWord_17270, baseEnd_17270] using wordTrace_append hprefix tailTrace_17270
  have hstable : (prefixWord ++ tailWord_17270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17270).length < 2 ^ (prefixWord ++ tailWord_17270).sum := by decide
  have hdescent : baseEnd_17270 < baseStart_17270 := by decide
  rcases family_descends (prefixWord ++ tailWord_17270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17332 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_17332 : Nat := 118140960795 + 17332 * 2 ^ 59
def prefixEnd_17332 : Nat := 4983230072969 + 3 ^ 40 * 17332 * 2
def baseEnd_17332 : Nat := 7910797070072375262487

theorem tailTrace_17332 : CollatzResearch.WordTrace tailWord_17332 prefixEnd_17332 7910797070072375262487 := by
  unfold tailWord_17332
  simp only [CollatzResearch.WordTrace]
  refine ⟨316074986608299457523125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 421433315477732610030833 316074986608299457523125)
  ·
    refine ⟨29632029994528074142793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 316074986608299457523125 29632029994528074142793)
    ·
      refine ⟨22224022495896055607095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29632029994528074142793 22224022495896055607095)
      ·
        refine ⟨33336033743844083410643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22224022495896055607095 33336033743844083410643)
        ·
          refine ⟨50004050615766125115965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33336033743844083410643 50004050615766125115965)
          ·
            refine ⟨18751518980912296918487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50004050615766125115965 18751518980912296918487)
            ·
              refine ⟨28127278471368445377731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18751518980912296918487 28127278471368445377731)
              ·
                refine ⟨42190917707052668066597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28127278471368445377731 42190917707052668066597)
                ·
                  refine ⟨7910797070072375262487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42190917707052668066597 7910797070072375262487)
                  ·
                    rfl

theorem cell20_17332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_17332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17332 prefixEnd_17332 := by exact prefixLift 17332
  have htrace : WordTrace (prefixWord ++ tailWord_17332) baseStart_17332 baseEnd_17332 := by
    simpa [prefixWord, tailWord_17332, baseEnd_17332] using wordTrace_append hprefix tailTrace_17332
  have hstable : (prefixWord ++ tailWord_17332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17332).length < 2 ^ (prefixWord ++ tailWord_17332).sum := by decide
  have hdescent : baseEnd_17332 < baseStart_17332 := by decide
  rcases family_descends (prefixWord ++ tailWord_17332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17336 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_17336 : Nat := 118140960795 + 17336 * 2 ^ 59
def prefixEnd_17336 : Nat := 4983230072969 + 3 ^ 40 * 17336 * 2
def baseEnd_17336 : Nat := 7912622779066139129137

theorem tailTrace_17336 : CollatzResearch.WordTrace tailWord_17336 prefixEnd_17336 7912622779066139129137 := by
  unfold tailWord_17336
  simp only [CollatzResearch.WordTrace]
  refine ⟨316147932601053799095931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 421530576801405065461241 316147932601053799095931)
  ·
    refine ⟨474221898901580698643897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316147932601053799095931 474221898901580698643897)
    ·
      refine ⟨355666424176185523982923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474221898901580698643897 355666424176185523982923)
      ·
        refine ⟨533499636264278285974385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355666424176185523982923 533499636264278285974385)
        ·
          refine ⟨400124727198208714480789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533499636264278285974385 400124727198208714480789)
          ·
            refine ⟨18755846587416033491287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 400124727198208714480789 18755846587416033491287)
            ·
              refine ⟨28133769881124050236931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18755846587416033491287 28133769881124050236931)
              ·
                refine ⟨42200654821686075355397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28133769881124050236931 42200654821686075355397)
                ·
                  refine ⟨7912622779066139129137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42200654821686075355397 7912622779066139129137)
                  ·
                    rfl

theorem cell20_17336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_17336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17336 prefixEnd_17336 := by exact prefixLift 17336
  have htrace : WordTrace (prefixWord ++ tailWord_17336) baseStart_17336 baseEnd_17336 := by
    simpa [prefixWord, tailWord_17336, baseEnd_17336] using wordTrace_append hprefix tailTrace_17336
  have hstable : (prefixWord ++ tailWord_17336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17336).length < 2 ^ (prefixWord ++ tailWord_17336).sum := by decide
  have hdescent : baseEnd_17336 < baseStart_17336 := by decide
  rcases family_descends (prefixWord ++ tailWord_17336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17381 : List Nat := [1, 3, 1, 6, 1, 8]
def baseStart_17381 : Nat := 118140960795 + 17381 * 2 ^ 59
def prefixEnd_17381 : Nat := 4983230072969 + 3 ^ 40 * 17381 * 2
def baseEnd_17381 : Nat := 293820815009110467739

theorem tailTrace_17381 : CollatzResearch.WordTrace tailWord_17381 prefixEnd_17381 293820815009110467739 := by
  unfold tailWord_17381
  simp only [CollatzResearch.WordTrace]
  refine ⟨633937150039080283579997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 422624766692720189053331 633937150039080283579997)
  ·
    refine ⟨237726431264655106342499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 633937150039080283579997 237726431264655106342499)
    ·
      refine ⟨356589646896982659513749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237726431264655106342499 356589646896982659513749)
      ·
        refine ⟨16715139698296062164707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 356589646896982659513749 16715139698296062164707)
        ·
          refine ⟨25072709547444093247061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16715139698296062164707 25072709547444093247061)
          ·
            refine ⟨293820815009110467739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 25072709547444093247061 293820815009110467739)
            ·
              rfl

theorem cell20_17381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 8].length) (baseStart_17381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17381 prefixEnd_17381 := by exact prefixLift 17381
  have htrace : WordTrace (prefixWord ++ tailWord_17381) baseStart_17381 baseEnd_17381 := by
    simpa [prefixWord, tailWord_17381, baseEnd_17381] using wordTrace_append hprefix tailTrace_17381
  have hstable : (prefixWord ++ tailWord_17381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17381).length < 2 ^ (prefixWord ++ tailWord_17381).sum := by decide
  have hdescent : baseEnd_17381 < baseStart_17381 := by decide
  rcases family_descends (prefixWord ++ tailWord_17381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17391 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 2]
def baseStart_17391 : Nat := 118140960795 + 17391 * 2 ^ 59
def prefixEnd_17391 : Nat := 4983230072969 + 3 ^ 40 * 17391 * 2
def baseEnd_17391 : Nat := 7937726277730392295579

theorem tailTrace_17391 : CollatzResearch.WordTrace tailWord_17391 prefixEnd_17391 7937726277730392295579 := by
  unfold tailWord_17391
  simp only [CollatzResearch.WordTrace]
  refine ⟨634301880002851991444027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 422867920001901327629351 634301880002851991444027)
  ·
    refine ⟨951452820004277987166041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634301880002851991444027 951452820004277987166041)
    ·
      refine ⟨713589615003208490374531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 951452820004277987166041 713589615003208490374531)
      ·
        refine ⟨1070384422504812735561797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713589615003208490374531 1070384422504812735561797)
        ·
          refine ⟨200697079219652387917837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1070384422504812735561797 200697079219652387917837)
          ·
            refine ⟨75261404707369645469189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200697079219652387917837 75261404707369645469189)
            ·
              refine ⟨14111513382631808525473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75261404707369645469189 14111513382631808525473)
              ·
                refine ⟨10583635036973856394105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14111513382631808525473 10583635036973856394105)
                ·
                  refine ⟨7937726277730392295579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10583635036973856394105 7937726277730392295579)
                  ·
                    rfl

theorem cell20_17391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2].length) (baseStart_17391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17391 prefixEnd_17391 := by exact prefixLift 17391
  have htrace : WordTrace (prefixWord ++ tailWord_17391) baseStart_17391 baseEnd_17391 := by
    simpa [prefixWord, tailWord_17391, baseEnd_17391] using wordTrace_append hprefix tailTrace_17391
  have hstable : (prefixWord ++ tailWord_17391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17391).length < 2 ^ (prefixWord ++ tailWord_17391).sum := by decide
  have hdescent : baseEnd_17391 < baseStart_17391 := by decide
  rcases family_descends (prefixWord ++ tailWord_17391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17398 : List Nat := [5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_17398 : Nat := 118140960795 + 17398 * 2 ^ 59
def prefixEnd_17398 : Nat := 4983230072969 + 3 ^ 40 * 17398 * 2
def baseEnd_17398 : Nat := 2646973756156493020739

theorem tailTrace_17398 : CollatzResearch.WordTrace tailWord_17398 prefixEnd_17398 2646973756156493020739 := by
  unfold tailWord_17398
  simp only [CollatzResearch.WordTrace]
  refine ⟨39659824436093261684303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 423038127318328124632565 39659824436093261684303)
  ·
    refine ⟨59489736654139892526455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39659824436093261684303 59489736654139892526455)
    ·
      refine ⟨89234604981209838789683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59489736654139892526455 89234604981209838789683)
      ·
        refine ⟨133851907471814758184525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89234604981209838789683 133851907471814758184525)
        ·
          refine ⟨50194465301930534319197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133851907471814758184525 50194465301930534319197)
          ·
            refine ⟨18822924488223950369699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50194465301930534319197 18822924488223950369699)
            ·
              refine ⟨28234386732335925554549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18822924488223950369699 28234386732335925554549)
              ·
                refine ⟨2646973756156493020739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28234386732335925554549 2646973756156493020739)
                ·
                  rfl

theorem cell20_17398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_17398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17398 prefixEnd_17398 := by exact prefixLift 17398
  have htrace : WordTrace (prefixWord ++ tailWord_17398) baseStart_17398 baseEnd_17398 := by
    simpa [prefixWord, tailWord_17398, baseEnd_17398] using wordTrace_append hprefix tailTrace_17398
  have hstable : (prefixWord ++ tailWord_17398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17398).length < 2 ^ (prefixWord ++ tailWord_17398).sum := by decide
  have hdescent : baseEnd_17398 < baseStart_17398 := by decide
  rcases family_descends (prefixWord ++ tailWord_17398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17419 : List Nat := [1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_17419 : Nat := 118140960795 + 17419 * 2 ^ 59
def prefixEnd_17419 : Nat := 4983230072969 + 3 ^ 40 * 17419 * 2
def baseEnd_17419 : Nat := 2650168746895579787377

theorem tailTrace_17419 : CollatzResearch.WordTrace tailWord_17419 prefixEnd_17419 2650168746895579787377 := by
  unfold tailWord_17419
  simp only [CollatzResearch.WordTrace]
  refine ⟨635323123901412773463311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 423548749267608515642207 635323123901412773463311)
  ·
    refine ⟨952984685852119160194967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635323123901412773463311 952984685852119160194967)
    ·
      refine ⟨1429477028778178740292451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952984685852119160194967 1429477028778178740292451)
      ·
        refine ⟨2144215543167268110438677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429477028778178740292451 2144215543167268110438677)
        ·
          refine ⟨100510103585965692676813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2144215543167268110438677 100510103585965692676813)
          ·
            refine ⟨37691288844737134753805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100510103585965692676813 37691288844737134753805)
            ·
              refine ⟨14134233316776425532677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37691288844737134753805 14134233316776425532677)
              ·
                refine ⟨2650168746895579787377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14134233316776425532677 2650168746895579787377)
                ·
                  rfl

theorem cell20_17419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_17419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17419 prefixEnd_17419 := by exact prefixLift 17419
  have htrace : WordTrace (prefixWord ++ tailWord_17419) baseStart_17419 baseEnd_17419 := by
    simpa [prefixWord, tailWord_17419, baseEnd_17419] using wordTrace_append hprefix tailTrace_17419
  have hstable : (prefixWord ++ tailWord_17419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17419).length < 2 ^ (prefixWord ++ tailWord_17419).sum := by decide
  have hdescent : baseEnd_17419 < baseStart_17419 := by decide
  rcases family_descends (prefixWord ++ tailWord_17419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17429 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 2]
def baseStart_17429 : Nat := 118140960795 + 17429 * 2 ^ 59
def prefixEnd_17429 : Nat := 4983230072969 + 3 ^ 40 * 17429 * 2
def baseEnd_17429 : Nat := 7955070513171149028757

theorem tailTrace_17429 : CollatzResearch.WordTrace tailWord_17429 prefixEnd_17429 7955070513171149028757 := by
  unfold tailWord_17429
  simp only [CollatzResearch.WordTrace]
  refine ⟨635687853865184481327341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 423791902576789654218227 635687853865184481327341)
  ·
    refine ⟨238382945199444180497753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 635687853865184481327341 238382945199444180497753)
    ·
      refine ⟨178787208899583135373315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238382945199444180497753 178787208899583135373315)
      ·
        refine ⟨268180813349374703059973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178787208899583135373315 268180813349374703059973)
        ·
          refine ⟨50283902503007756823745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268180813349374703059973 50283902503007756823745)
          ·
            refine ⟨37712926877255817617809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50283902503007756823745 37712926877255817617809)
            ·
              refine ⟨28284695157941863213357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37712926877255817617809 28284695157941863213357)
              ·
                refine ⟨10606760684228198705009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28284695157941863213357 10606760684228198705009)
                ·
                  refine ⟨7955070513171149028757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10606760684228198705009 7955070513171149028757)
                  ·
                    rfl

theorem cell20_17429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_17429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17429 prefixEnd_17429 := by exact prefixLift 17429
  have htrace : WordTrace (prefixWord ++ tailWord_17429) baseStart_17429 baseEnd_17429 := by
    simpa [prefixWord, tailWord_17429, baseEnd_17429] using wordTrace_append hprefix tailTrace_17429
  have hstable : (prefixWord ++ tailWord_17429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17429).length < 2 ^ (prefixWord ++ tailWord_17429).sum := by decide
  have hdescent : baseEnd_17429 < baseStart_17429 := by decide
  rcases family_descends (prefixWord ++ tailWord_17429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17443 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_17443 : Nat := 118140960795 + 17443 * 2 ^ 59
def prefixEnd_17443 : Nat := 4983230072969 + 3 ^ 40 * 17443 * 2
def baseEnd_17443 : Nat := 7961460494649322562033

theorem tailTrace_17443 : CollatzResearch.WordTrace tailWord_17443 prefixEnd_17443 7961460494649322562033 := by
  unfold tailWord_17443
  simp only [CollatzResearch.WordTrace]
  refine ⟨636198475814464872336983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 424132317209643248224655 636198475814464872336983)
  ·
    refine ⟨954297713721697308505475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 636198475814464872336983 954297713721697308505475)
    ·
      refine ⟨1431446570582545962758213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954297713721697308505475 1431446570582545962758213)
      ·
        refine ⟨268396231984227368017165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1431446570582545962758213 268396231984227368017165)
        ·
          refine ⟨100648586994085263006437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268396231984227368017165 100648586994085263006437)
          ·
            refine ⟨18871610061390986813707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100648586994085263006437 18871610061390986813707)
            ·
              refine ⟨28307415092086480220561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18871610061390986813707 28307415092086480220561)
              ·
                refine ⟨21230561319064860165421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28307415092086480220561 21230561319064860165421)
                ·
                  refine ⟨7961460494649322562033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21230561319064860165421 7961460494649322562033)
                  ·
                    rfl

theorem cell20_17443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_17443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17443 prefixEnd_17443 := by exact prefixLift 17443
  have htrace : WordTrace (prefixWord ++ tailWord_17443) baseStart_17443 baseEnd_17443 := by
    simpa [prefixWord, tailWord_17443, baseEnd_17443] using wordTrace_append hprefix tailTrace_17443
  have hstable : (prefixWord ++ tailWord_17443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17443).length < 2 ^ (prefixWord ++ tailWord_17443).sum := by decide
  have hdescent : baseEnd_17443 < baseStart_17443 := by decide
  rcases family_descends (prefixWord ++ tailWord_17443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17501 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 2]
def baseStart_17501 : Nat := 118140960795 + 17501 * 2 ^ 59
def prefixEnd_17501 : Nat := 4983230072969 + 3 ^ 40 * 17501 * 2
def baseEnd_17501 : Nat := 7987933275058898628463

theorem tailTrace_17501 : CollatzResearch.WordTrace tailWord_17501 prefixEnd_17501 7987933275058898628463 := by
  unfold tailWord_17501
  simp only [CollatzResearch.WordTrace]
  refine ⟨638313909604340777948357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 425542606402893851965571 638313909604340777948357)
  ·
    refine ⟨119683858050813895865317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 638313909604340777948357 119683858050813895865317)
    ·
      refine ⟨22440723384527605474747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119683858050813895865317 22440723384527605474747)
      ·
        refine ⟨33661085076791408212121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22440723384527605474747 33661085076791408212121)
        ·
          refine ⟨25245813807593556159091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33661085076791408212121 25245813807593556159091)
          ·
            refine ⟨37868720711390334238637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25245813807593556159091 37868720711390334238637)
            ·
              refine ⟨14200770266771375339489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37868720711390334238637 14200770266771375339489)
              ·
                refine ⟨10650577700078531504617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14200770266771375339489 10650577700078531504617)
                ·
                  refine ⟨7987933275058898628463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10650577700078531504617 7987933275058898628463)
                  ·
                    rfl

theorem cell20_17501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_17501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17501 prefixEnd_17501 := by exact prefixLift 17501
  have htrace : WordTrace (prefixWord ++ tailWord_17501) baseStart_17501 baseEnd_17501 := by
    simpa [prefixWord, tailWord_17501, baseEnd_17501] using wordTrace_append hprefix tailTrace_17501
  have hstable : (prefixWord ++ tailWord_17501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17501).length < 2 ^ (prefixWord ++ tailWord_17501).sum := by decide
  have hdescent : baseEnd_17501 < baseStart_17501 := by decide
  rcases family_descends (prefixWord ++ tailWord_17501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17512 : List Nat := [2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_17512 : Nat := 118140960795 + 17512 * 2 ^ 59
def prefixEnd_17512 : Nat := 4983230072969 + 3 ^ 40 * 17512 * 2
def baseEnd_17512 : Nat := 2664317991597249753917

theorem tailTrace_17512 : CollatzResearch.WordTrace tailWord_17512 prefixEnd_17512 2664317991597249753917 := by
  unfold tailWord_17512
  simp only [CollatzResearch.WordTrace]
  refine ⟨319357556282244828299395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 425810075042993104399193 319357556282244828299395)
  ·
    refine ⟨479036334423367242449093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319357556282244828299395 479036334423367242449093)
    ·
      refine ⟨89819312704381357959205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 479036334423367242449093 89819312704381357959205)
      ·
        refine ⟨16841121132071504617351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89819312704381357959205 16841121132071504617351)
        ·
          refine ⟨25261681698107256926027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16841121132071504617351 25261681698107256926027)
          ·
            refine ⟨37892522547160885389041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25261681698107256926027 37892522547160885389041)
            ·
              refine ⟨28419391910370664041781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37892522547160885389041 28419391910370664041781)
              ·
                refine ⟨2664317991597249753917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28419391910370664041781 2664317991597249753917)
                ·
                  rfl

theorem cell20_17512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_17512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17512 prefixEnd_17512 := by exact prefixLift 17512
  have htrace : WordTrace (prefixWord ++ tailWord_17512) baseStart_17512 baseEnd_17512 := by
    simpa [prefixWord, tailWord_17512, baseEnd_17512] using wordTrace_append hprefix tailTrace_17512
  have hstable : (prefixWord ++ tailWord_17512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17512).length < 2 ^ (prefixWord ++ tailWord_17512).sum := by decide
  have hdescent : baseEnd_17512 < baseStart_17512 := by decide
  rcases family_descends (prefixWord ++ tailWord_17512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
